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
module LindenElkLiftSimGate {
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
  import NB = LindenElkNulledPlusBool
  import opened LindenElkLiftSimCore
  import opened LindenElkLiftSimOracle
  import opened LindenElkLiftSimChain

  /** `LiftInvCNested` carrying the standalone `LiftInvRec`. */
  ghost predicate LiftInvCRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                              endl: nat, ngroups: nat, crv: CP.FCompiled, str: string,
                              ov: LOr.OracleView, S: set<LG.GroupId>,
                              ptsA: PT.PikeTreeState, ptsB: PT.PikeTreeState, vms: AI.VmState,
                              ncap: int, nlook: int, nquant: int)
    requires NR.NfaRepRE(re, code, 0, endl)
  {
    PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, vms, ncap, nlook, nquant)
    && (ptsB.PTS? ==> ptsA.PTS? && ptsA.inp == ptsB.inp)
    && LiftInvRec(rer, qm, re, code, crv, str, ov, S, ptsB, vms, ncap, nlook, nquant)
  }

  /** (3) Initial pairing: fresh VM state ↔ `PikeTreeInitialState(tcan, inp)`
      where `tcan` is the PLANTED CANONICAL entry tree (constructed here from
      the raw entry walk tree `t` by `ActionsTreeRepLkRE` + `WkE.WalkOkEntry`;
      `t` remains the value layer's erasure witness, and
      `ProgErase(tcan) == ProgErase(t)` is the endpoint `FirstLeaf` glue). */
  lemma LiftInit(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                 crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                 t: LT.Tree, vms: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (tcan: LT.Tree)
    requires AR.NoTrueStamps(code)   // §2.5b stage 2a: look-body code is stamp-free
    requires !rer.multiline
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re) && PIV.CapUnique(re)
    requires NR.NoNulledPlusRE(re)   // §2.5b interim: all stamps false
    requires code == CP.compile_to_bytecode(re)
    requires AR.ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
    requires LL.OracleOkSuffix(rer, qm, LC.InitInput(str))
    requires EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], LC.InitInput(str), BS.CannotExit, t)
    requires vms.cp == 0
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.blocked == [] && vms.bestmatch.None?
    requires vms.processed == AI.init_bpcset(|code|)
    requires vms.isblocked == AI.init_pcset(|code|)
    requires PIV.ContextOkRE(str, vms.cp, vms.context)
    ensures TreeRepLkRE(rer, qm, code, LC.InitInput(str), tcan, 0, false)
    ensures CE.ProgErase(tcan) == CE.ProgErase(t)   // endpoint glue: FirstLeaf(tcan) == FirstLeaf(t)
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S,
                    PT.PikeTreeInitialState(tcan, LC.InitInput(str)), vms, ncap, nlook, nquant)
  {
    var inp := LC.InitInput(str);
    var itr := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
    var acts := [LS.Areg(T.Translate(re))];

    // inp == InpOfCp(str, 0)
    assert str[..0] == [] && str[0..] == str;
    assert LC.Reverse(str[..0]) == [];
    assert inp == PIV.InpOfCp(str, 0);

    // entry walk-state facts
    EL.TranslateFragmentPikeLk(re);                           // PikeLkRegex(Translate(re))
    EL.PikeLkActionsConsIff(LS.Areg(T.Translate(re)), []);    // PikeLkActions(acts)
    assert EL.PikeLkActions(acts);
    PIV.GmOfLiveInit(re, ncap, nlook, nquant);               // GmOfLive(re, init...) == Empty

    // the single entry thread pairs with (t, Empty)
    assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, t, LG.Empty, itr, ncap, nlook, nquant) by {
      assert itr.pc == 0 && itr.exit_allowed == false;
      assert GateAheadClear(acts, LG.Empty);                 // Empty has no keys
      assert ATR.EaOf(BS.CannotExit) == itr.exit_allowed;
      TranslateDefGroupsNoDup(re);                            // NoDupSeq(DefGroups(Translate(re)))
      WalkDefsOkEntry(T.Translate(re));
      M.AllDefsActsCons(LS.Areg(T.Translate(re)), []);
      assert M.AllDefsActs(acts) == L.DefGroups(T.Translate(re));   // AllDefsActs([]) == []
      assert exists actsw: LS.Actions, bw: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, actsw, code, itr.pc as nat)
          && EL.PikeLkActions(actsw)
          && ATR.EaOf(bw) == itr.exit_allowed
          && EL.BoolTreeLk(rer, actsw, inp, bw, t)
          && GateAheadClear(actsw, LG.Empty)
          && WalkDefsOk(actsw);
      assert PIV.GmOfLive(re, itr.capture_regs, itr.look_regs, itr.quant_regs) == LG.Empty;
      assert GmtTieOutside(re, itr, LG.Empty, S);
      assert GmtTieInside(crv, str, ov, itr, LG.Empty, S, ncap, nlook, nquant);  // vacuous
    }
    // Construct machine B's PLANTED CANONICAL entry tree; the raw walk tree
    // `t` is its value-layer erasure witness.
    WkE.WalkOkEntry(re);
    assert WO.WalkOk(acts, code, 0, false);
    assert ATR.EaOf(BS.CannotExit) == false;
    tcan := ActionsTreeRepLkRE(rer, qm, acts, code, 0, inp, BS.CannotExit, t);
    var bst := PT.PikeTreeInitialState(tcan, inp);
    assert bst == PT.PTS(inp, [(tcan, LG.Empty)], None, [], SS.InitialSeenTrees);
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, tcan, LG.Empty, itr,
                        ncap, nlook, nquant) by {
      assert TreeRepLkRE(rer, qm, code, inp, tcan, itr.pc as nat, itr.exit_allowed);
      assert CE.ProgErase(t) == CE.ProgErase(tcan)
             && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, t, LG.Empty, itr, ncap, nlook, nquant);
    }
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, [(tcan, LG.Empty)], [itr], ncap, nlook, nquant);

    // blocked: both sides empty (vms.blocked == [])
    forall nextinp | LC.AdvanceInput(inp, WP.Forward) == Some(nextinp)
      ensures BlockedRepLkC(rer, qm, re, code, inp, nextinp, crv, str, ov, S, [],
                            PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant)
    {
      assert LC.Reverse(vms.blocked) == [];
      assert PIV.MatchingBlocked([], inp) == [];
    }
    assert BestTieLk(re, crv, str, ov, S, None, vms.bestmatch, ncap, nlook, nquant);
  }

  /** SKIP: the head's `(pc, ea)` is already processed — the VM drops it, and
      B fires `pts_skip`: the seen slot's canonical tree EQUALS the head's by
      `TreeRepLkDetermRE` (the whole point of the planted-canonical pivot);
      the stutter escape is killed by `NoStutterCycle`. */
  lemma LiftPreserveSkipLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                           crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                           bst: PT.PikeTreeState, s: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    ensures PTL.PikeTreeStepLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, s.(active := s.active[1..]),
                    ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;

    // The processed slot resolves LEFT: the stutter escape would need
    // StutterChainTo(pc, pc), impossible in tame code.
    assert AI.bpc_mem(s.processed, pc, ea);
    assert (exists t': LT.Tree :: SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, ea))
           || (TT.StuttersRE(pc, code)
               && exists t': LT.Tree ::
                 PIV.StutterChainTo(code, pc, pc) && Some(t) == Some(t')
                 && TreeRepLkRE(rer, qm, code, inp, t', pc, ea));
    if !(exists t': LT.Tree :: SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, ea)) {
      PIV.NoStutterCycle(code, pc);
      assert false;
    }
    var t': LT.Tree :| SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, ea);
    TreeRepLkDetermRE(rer, qm, code, inp, t, t', pc, ea);
    assert SS.Inseen(seen, t);

    // pts_skip
    bst1 := PT.PTS(inp, ta[1..], best, tb, seen);
    assert PTL.PikeTreeStepLk(bst, bst1);

    // invariant at the successor
    SkipSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc,
                  PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(s.active[1..]));
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
  }

  /** (L4 NESTED) clone of `LiftPreserveSkipLk` — GmtTieInside dropped. */
  lemma LiftPreserveSkipLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                 crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                 bst: PT.PikeTreeState, s: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    ensures PTL.PikeTreeStepLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, s.(active := s.active[1..]),
                          ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;

    // The processed slot resolves LEFT: the stutter escape would need
    // StutterChainTo(pc, pc), impossible in tame code.
    assert AI.bpc_mem(s.processed, pc, ea);
    assert (exists t': LT.Tree :: SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, ea))
           || (TT.StuttersRE(pc, code)
               && exists t': LT.Tree ::
                 PIV.StutterChainTo(code, pc, pc) && Some(t) == Some(t')
                 && TreeRepLkRE(rer, qm, code, inp, t', pc, ea));
    if !(exists t': LT.Tree :: SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, ea)) {
      PIV.NoStutterCycle(code, pc);
      assert false;
    }
    var t': LT.Tree :| SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, ea);
    TreeRepLkDetermRE(rer, qm, code, inp, t, t', pc, ea);
    assert SS.Inseen(seen, t);

    // pts_skip
    bst1 := PT.PTS(inp, ta[1..], best, tb, seen);
    assert PTL.PikeTreeStepLk(bst, bst1);

    // invariant at the successor
    SkipSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc,
                  PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(s.active[1..]));
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                              ncap, nlook, nquant);
  }

  /** STUTTER (Jmp / BeginLoop): the VM relocates the head thread, B does not
      step — the SAME canonical tree represents at the relocated `(pc', ea')`
      (`tr_jmp`/`tr_begin`), the raw witness relocates with its stack, and the
      seen escape chain extends one step (`StutterSeenRepLk`). */
  lemma LiftPreserveStutterLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                              crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                              bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState, th': AI.Thread,
                              vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires (exists x: int ::
                NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Jmp(x))
                && th' == s.active[0].(pc := x))
             || (NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.BeginLoop)
                 && th' == s.active[0].(exit_allowed := false, pc := s.active[0].pc + 1))
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);

    // the relocated head pairing
    var pc': nat;
    if exists x: int :: NR.GetPcRE(code, pc) == Some(RB.Jmp(x)) && th' == th.(pc := x) {
      var x: int :| NR.GetPcRE(code, pc) == Some(RB.Jmp(x)) && th' == th.(pc := x);
      TreeRepLkREAtJmp(rer, qm, code, inp, t, pc, ea, x);
      WalkPairLkAtJmp(rer, qm, code, inp, traw, gm, pc, ea, x);
      pc' := x as nat;
      assert PIV.StutterSuccIs(code, pc, pc');
    } else {
      TreeRepLkREAtBeginLoop(rer, qm, code, inp, t, pc, ea);
      WalkPairLkAtBeginLoop(rer, qm, code, inp, traw, gm, pc, ea);
      pc' := pc + 1;
      assert PIV.StutterSuccIs(code, pc, pc');
    }
    assert th'.pc == pc' as int;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc', th'.exit_allowed);
    assert WalkPairLk(rer, qm, code, inp, traw, gm, pc', th'.exit_allowed);
    assert th'.capture_regs == th.capture_regs && th'.look_regs == th.look_regs
           && th'.quant_regs == th.quant_regs;
    assert GmtTieOutside(re, th', gm, S);
    assert GmtTieInside(crv, str, ov, th', gm, S, ncap, nlook, nquant);
    assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th', ncap, nlook, nquant);
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th', ncap, nlook, nquant);

    // active: same (tree, gm) list against the relocated head
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ta == [ta[0]] + ta[1..];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, vms2.active, ncap, nlook, nquant);

    // seen: the escape chain extends by one stutter step
    assert TT.StuttersRE(pc, code);
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    StutterSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea, pc');
    assert PIV.HeadPcOf(vms2.active) == pc';
  }

  /** (L4 NESTED) clone of `LiftPreserveStutterLk` — GmtTieInside dropped. */
  lemma LiftPreserveStutterLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                    crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                    bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState, th': AI.Thread,
                                    vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires (exists x: int ::
                NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Jmp(x))
                && th' == s.active[0].(pc := x))
             || (NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.BeginLoop)
                 && th' == s.active[0].(exit_allowed := false, pc := s.active[0].pc + 1))
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);

    // the relocated head pairing
    var pc': nat;
    if exists x: int :: NR.GetPcRE(code, pc) == Some(RB.Jmp(x)) && th' == th.(pc := x) {
      var x: int :| NR.GetPcRE(code, pc) == Some(RB.Jmp(x)) && th' == th.(pc := x);
      TreeRepLkREAtJmp(rer, qm, code, inp, t, pc, ea, x);
      WalkPairLkAtJmp(rer, qm, code, inp, traw, gm, pc, ea, x);
      pc' := x as nat;
      assert PIV.StutterSuccIs(code, pc, pc');
    } else {
      TreeRepLkREAtBeginLoop(rer, qm, code, inp, t, pc, ea);
      WalkPairLkAtBeginLoop(rer, qm, code, inp, traw, gm, pc, ea);
      pc' := pc + 1;
      assert PIV.StutterSuccIs(code, pc, pc');
    }
    assert th'.pc == pc' as int;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc', th'.exit_allowed);
    assert WalkPairLk(rer, qm, code, inp, traw, gm, pc', th'.exit_allowed);
    assert th'.capture_regs == th.capture_regs && th'.look_regs == th.look_regs
           && th'.quant_regs == th.quant_regs;
    assert GmtTieOutside(re, th', gm, S);
    assert ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th', ncap, nlook, nquant);
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th', ncap, nlook, nquant);

    // active: same (tree, gm) list against the relocated head
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                              ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ta == [ta[0]] + ta[1..];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, vms2.active, ncap, nlook, nquant);

    // seen: the escape chain extends by one stutter step
    assert TT.StuttersRE(pc, code);
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    StutterSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea, pc');
    assert PIV.HeadPcOf(vms2.active) == pc';
  }

  /** ACCEPT: the VM records the winner and CUTS the queue; B fires
      `pts_match` — the head canonical tree IS `Match` and its `gm` carries
      exactly the two-sided value tie (`BestTieLk` straight from
      `ThreadRepLkC`'s payload). */
  lemma LiftPreserveAcceptLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                             crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                             bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                             vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Accept)
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [], bestmatch := Some(s.active[0]))
    ensures PTL.PikeTreeStepLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    TreeRepLkREAtAccept(rer, qm, code, inp, t, pc, ea);
    assert t == LT.Match;
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepMatch;

    // pts_match
    bst1 := PT.PTS(inp, [], Some((inp, gm)), tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);

    // the value tie for the recorded best — straight from the head's payload
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    assert GmtTieOutside(re, th, gm, S);
    assert GmtTieInside(crv, str, ov, th, gm, S, ncap, nlook, nquant);
    assert BestTieLk(re, crv, str, ov, S, Some((inp, gm)), vms2.bestmatch, ncap, nlook, nquant);

    // bookkeeping: seen grows with the memoized head; active empty both sides
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, [], vms2.active, ncap, nlook, nquant);
  }

  /** (L4 NESTED) clone of `LiftPreserveAcceptLk` — GmtTieInside dropped. */
  lemma LiftPreserveAcceptLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                   crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                   bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                   vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Accept)
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [], bestmatch := Some(s.active[0]))
    ensures PTL.PikeTreeStepLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    TreeRepLkREAtAccept(rer, qm, code, inp, t, pc, ea);
    assert t == LT.Match;
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepMatch;

    // pts_match
    bst1 := PT.PTS(inp, [], Some((inp, gm)), tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);

    // the value tie for the recorded best — straight from the head's payload
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    assert GmtTieOutside(re, th, gm, S);
    assert BestTieLkNested(re, crv, str, ov, S, Some((inp, gm)), vms2.bestmatch, ncap, nlook, nquant);

    // bookkeeping: seen grows with the memoized head; active empty both sides
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, [], vms2.active, ncap, nlook, nquant);
  }

  /** DEAD HEAD, shared bookkeeping: the head canonical tree steps to an EMPTY
      `pts_active` (`Mismatch`/`LKFail` — `StepDead() == StepActive([])`), the
      VM drops the thread, B memoizes the dead tree. Every kill case
      (EndLoop/Anchor/gate) reduces to this after pinning the head shape. */
  lemma LiftDropDeadHeadLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                           crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                           bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                           vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires |bst.active| > 0
    requires PTL.TreeBfsStepLk(bst.active[0].0, bst.active[0].1, bst.inp) == PT.StepActive([])
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.PikeTreeStepLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // pts_active with an empty successor list: the branch dies on both sides.
    bst1 := PT.PTS(inp, ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert [] + ta[1..] == ta[1..];
    assert PTL.PikeTreeStepLk(bst, bst1);

    // bookkeeping at the successor
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
    assert vms2.active == s.active[1..];
  }

  /** (L4 NESTED) `LiftDropDeadHeadLk` for `LiftInvNested` — pure predicate swap
      (`LiftInv`→`LiftInvNested`, `ActiveRepLkC`→`ActiveRepLkCNested`,
      `ThreadRepLkC`→`ThreadRepLkCNested`); no `GmtTieInside` obligation exists. */
  lemma LiftDropDeadHeadLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                 crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                 bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                 vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires |bst.active| > 0
    requires PTL.TreeBfsStepLk(bst.active[0].0, bst.active[0].1, bst.inp) == PT.StepActive([])
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.PikeTreeStepLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // pts_active with an empty successor list: the branch dies on both sides.
    bst1 := PT.PTS(inp, ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert [] + ta[1..] == ta[1..];
    assert PTL.PikeTreeStepLk(bst, bst1);

    // bookkeeping at the successor
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                              ncap, nlook, nquant);
    assert vms2.active == s.active[1..];
  }

  /** CONSUME, pc not yet blocked: the VM blocks the head unconditionally;
      B blocks a matching `Read` (`pts_blocked`, keeping `BlockedRepLkC`
      aligned through the `MatchingBlocked` filter) or drops a `Mismatch`
      (empty `pts_active` — the doomed blocked thread is invisible to the
      filter). Mirror of `PSM.PreserveConsumeAdd`. */
  lemma LiftPreserveConsumeAddLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                 crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                 bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                 ce: RC.char_expectation, vms2: AI.VmState,
                                 ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Consume(ce))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires !AI.pc_mem(s1.isblocked, s.active[0].pc)
    requires vms2 == s1.(blocked := [(s.active[0], ce)] + s1.blocked,
                     isblocked := AI.pc_add(s1.isblocked, s.active[0].pc),
                     active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    TreeRepLkREAtConsume(rer, qm, code, inp, t, pc, ea, ce);

    // shared list bookkeeping
    PSM.ReversePrepend((th, ce), s.blocked);
    PSM.MatchingBlockedSnoc(LC.Reverse(s.blocked), (th, ce), inp);

    // the new isblocked entry pc is covered by the freshly-seen head tree
    assert IsblockedRepLk(rer, qm, code, inp, SS.AddSeenTrees(seen, t), vms2.isblocked) by {
      forall pc0: nat | AI.pc_mem(vms2.isblocked, pc0)
        ensures exists t0: LT.Tree, b0: bool ::
                  SS.Inseen(SS.AddSeenTrees(seen, t), t0) && TreeRepLkRE(rer, qm, code, inp, t0, pc0, b0)
      {
        PIV.PcAddMemFwd(s1.isblocked, th.pc, pc0);
        if pc0 == pc {
          SS.InAdd(seen, t, t);
          assert SS.Inseen(SS.AddSeenTrees(seen, t), t) && TreeRepLkRE(rer, qm, code, inp, t, pc0, ea);
        } else {
          assert AI.pc_mem(s.isblocked, pc0);
          var t0: LT.Tree, b0: bool :| SS.Inseen(seen, t0) && TreeRepLkRE(rer, qm, code, inp, t0, pc0, b0);
          SS.InAdd(seen, t0, t);
        }
      }
    }

    if AR.ReadCharE(ce, inp).Some? {
      // MATCHING: pts_blocked pairs the appended entries.
      var (c, nextinp0) := AR.ReadCharE(ce, inp).value;
      assert t.Read? && t.c == c
             && TreeRepLkRE(rer, qm, code, nextinp0, t.t, pc + 1, true);
      assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepBlocked(t.t);
      bst1 := PT.PTS(inp, ta[1..], best, tb + [(t.t, gm)], SS.AddSeenTrees(seen, t));
      assert PTL.PikeTreeStepLk(bst, bst1);
      TrcLkRefl(bst1);
      TrcLkCons(bst, bst1, bst1);

      // the raw child witness for the blocked pair: the head's raw witness
      // reads the same character (erasure pins the Read root)
      var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                           && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
      assert WalkPairLk(rer, qm, code, inp, traw, gm, pc, ea);
      WalkPairLkAtConsume(rer, qm, code, inp, traw, gm, pc, ea, ce);
      assert traw.Read? by {
        if !traw.Read? {
          assert traw == LT.Mismatch;
          assert CE.ProgErase(traw) == LT.Mismatch;
          assert CE.ProgErase(t).Read?;
          assert false;
        }
      }
      var nextinpw: LC.Input :| AR.ReadCharE(ce, inp) == Some((traw.c, nextinpw))
                                && WalkPairLk(rer, qm, code, nextinpw, traw.t, gm, pc + 1, true);
      assert traw.c == c && nextinpw == nextinp0;    // ReadCharE is a function
      assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
        assert CE.ProgErase(traw) == LT.Read(traw.c, CE.ProgErase(traw.t));
        assert CE.ProgErase(t) == LT.Read(t.c, CE.ProgErase(t.t));
      }

      // blocked correspondence: the filter gains exactly the new pair
      forall nextinp | LC.AdvanceInput(inp, WP.Forward) == Some(nextinp)
        ensures BlockedRepLkC(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tb + [(t.t, gm)],
                              PIV.MatchingBlocked(LC.Reverse(vms2.blocked), inp), ncap, nlook, nquant)
      {
        assert nextinp == nextinp0;
        assert PIV.MatchingBlocked(LC.Reverse(vms2.blocked), inp)
            == PIV.MatchingBlocked(LC.Reverse(s.blocked), inp) + [(th, ce)];
        assert GmtTieOutside(re, th, gm, S);
        assert GmtTieInside(crv, str, ov, th, gm, S, ncap, nlook, nquant);
        BlockedRepLkCSnoc(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tb,
                          PIV.MatchingBlocked(LC.Reverse(s.blocked), inp), (t.t, gm), (th, ce),
                          ncap, nlook, nquant);
      }
      assert |inp.next| > 0;                          // ReadCharE Some
      assert LC.AdvanceInput(inp, WP.Forward).Some?;

      AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                   PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
      assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                          ncap, nlook, nquant);
      assert vms2.active == s.active[1..];
    } else {
      // MISMATCH: the tree is Mismatch and dies; the doomed blocked thread is
      // invisible to the filter.
      assert t == LT.Mismatch;
      assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([]);
      bst1 := PT.PTS(inp, ta[1..], best, tb, SS.AddSeenTrees(seen, t));
      assert [] + ta[1..] == ta[1..];
      assert PTL.PikeTreeStepLk(bst, bst1);
      TrcLkRefl(bst1);
      TrcLkCons(bst, bst1, bst1);

      assert PIV.MatchingBlocked(LC.Reverse(vms2.blocked), inp)
          == PIV.MatchingBlocked(LC.Reverse(s.blocked), inp);

      AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                   PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
      assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                          ncap, nlook, nquant);
      assert vms2.active == s.active[1..];
    }
  }

  /** (L4 NESTED) clone of `LiftPreserveConsumeAddLk` — GmtTieInside dropped. */
  lemma LiftPreserveConsumeAddLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                       crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                       bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                       ce: RC.char_expectation, vms2: AI.VmState,
                                       ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Consume(ce))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires !AI.pc_mem(s1.isblocked, s.active[0].pc)
    requires vms2 == s1.(blocked := [(s.active[0], ce)] + s1.blocked,
                     isblocked := AI.pc_add(s1.isblocked, s.active[0].pc),
                     active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    TreeRepLkREAtConsume(rer, qm, code, inp, t, pc, ea, ce);

    // shared list bookkeeping
    PSM.ReversePrepend((th, ce), s.blocked);
    PSM.MatchingBlockedSnoc(LC.Reverse(s.blocked), (th, ce), inp);

    // the new isblocked entry pc is covered by the freshly-seen head tree
    assert IsblockedRepLk(rer, qm, code, inp, SS.AddSeenTrees(seen, t), vms2.isblocked) by {
      forall pc0: nat | AI.pc_mem(vms2.isblocked, pc0)
        ensures exists t0: LT.Tree, b0: bool ::
                  SS.Inseen(SS.AddSeenTrees(seen, t), t0) && TreeRepLkRE(rer, qm, code, inp, t0, pc0, b0)
      {
        PIV.PcAddMemFwd(s1.isblocked, th.pc, pc0);
        if pc0 == pc {
          SS.InAdd(seen, t, t);
          assert SS.Inseen(SS.AddSeenTrees(seen, t), t) && TreeRepLkRE(rer, qm, code, inp, t, pc0, ea);
        } else {
          assert AI.pc_mem(s.isblocked, pc0);
          var t0: LT.Tree, b0: bool :| SS.Inseen(seen, t0) && TreeRepLkRE(rer, qm, code, inp, t0, pc0, b0);
          SS.InAdd(seen, t0, t);
        }
      }
    }

    if AR.ReadCharE(ce, inp).Some? {
      // MATCHING: pts_blocked pairs the appended entries.
      var (c, nextinp0) := AR.ReadCharE(ce, inp).value;
      assert t.Read? && t.c == c
             && TreeRepLkRE(rer, qm, code, nextinp0, t.t, pc + 1, true);
      assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepBlocked(t.t);
      bst1 := PT.PTS(inp, ta[1..], best, tb + [(t.t, gm)], SS.AddSeenTrees(seen, t));
      assert PTL.PikeTreeStepLk(bst, bst1);
      TrcLkRefl(bst1);
      TrcLkCons(bst, bst1, bst1);

      // the raw child witness for the blocked pair: the head's raw witness
      // reads the same character (erasure pins the Read root)
      var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                           && ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
      assert WalkPairLk(rer, qm, code, inp, traw, gm, pc, ea);
      WalkPairLkAtConsume(rer, qm, code, inp, traw, gm, pc, ea, ce);
      assert traw.Read? by {
        if !traw.Read? {
          assert traw == LT.Mismatch;
          assert CE.ProgErase(traw) == LT.Mismatch;
          assert CE.ProgErase(t).Read?;
          assert false;
        }
      }
      var nextinpw: LC.Input :| AR.ReadCharE(ce, inp) == Some((traw.c, nextinpw))
                                && WalkPairLk(rer, qm, code, nextinpw, traw.t, gm, pc + 1, true);
      assert traw.c == c && nextinpw == nextinp0;    // ReadCharE is a function
      assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
        assert CE.ProgErase(traw) == LT.Read(traw.c, CE.ProgErase(traw.t));
        assert CE.ProgErase(t) == LT.Read(t.c, CE.ProgErase(t.t));
      }

      // blocked correspondence: the filter gains exactly the new pair
      forall nextinp | LC.AdvanceInput(inp, WP.Forward) == Some(nextinp)
        ensures BlockedRepLkCNested(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tb + [(t.t, gm)],
                                    PIV.MatchingBlocked(LC.Reverse(vms2.blocked), inp), ncap, nlook, nquant)
      {
        assert nextinp == nextinp0;
        assert PIV.MatchingBlocked(LC.Reverse(vms2.blocked), inp)
            == PIV.MatchingBlocked(LC.Reverse(s.blocked), inp) + [(th, ce)];
        assert GmtTieOutside(re, th, gm, S);
        BlockedRepLkCSnocNested(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tb,
                                PIV.MatchingBlocked(LC.Reverse(s.blocked), inp), (t.t, gm), (th, ce),
                                ncap, nlook, nquant);
      }
      assert |inp.next| > 0;                          // ReadCharE Some
      assert LC.AdvanceInput(inp, WP.Forward).Some?;

      AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                   PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
      assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                                ncap, nlook, nquant);
      assert vms2.active == s.active[1..];
    } else {
      // MISMATCH: the tree is Mismatch and dies; the doomed blocked thread is
      // invisible to the filter.
      assert t == LT.Mismatch;
      assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([]);
      bst1 := PT.PTS(inp, ta[1..], best, tb, SS.AddSeenTrees(seen, t));
      assert [] + ta[1..] == ta[1..];
      assert PTL.PikeTreeStepLk(bst, bst1);
      TrcLkRefl(bst1);
      TrcLkCons(bst, bst1, bst1);

      assert PIV.MatchingBlocked(LC.Reverse(vms2.blocked), inp)
          == PIV.MatchingBlocked(LC.Reverse(s.blocked), inp);

      AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                   PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
      assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                                ncap, nlook, nquant);
      assert vms2.active == s.active[1..];
    }
  }

  /** CONSUME, pc already blocked (dedup): the VM drops the head; B fires
      `pts_skip` — `IsblockedRepLk` holds a canonical tree at the `Consume`
      pc, whose rule is flag-independent, so determinism identifies it with
      the head's. Mirror of `PSM.PreserveConsumeDrop`. BODILESS. */
  lemma LiftPreserveConsumeDropLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                  crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                  bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                  ce: RC.char_expectation, vms2: AI.VmState,
                                  ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Consume(ce))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires AI.pc_mem(s1.isblocked, s.active[0].pc)
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // the blocked pc's memoized canonical tree IS the head's — the Consume
    // rules are flag-independent, so the recorded flag transfers.
    assert IsblockedRepLk(rer, qm, code, inp, seen, s.isblocked);
    assert AI.pc_mem(s.isblocked, th.pc) && th.pc == pc as int;
    assert AI.pc_mem(s.isblocked, pc);
    var t': LT.Tree, b': bool :| SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, b');
    TreeRepLkREAtConsume(rer, qm, code, inp, t', pc, b', ce);
    assert TreeRepLkRE(rer, qm, code, inp, t', pc, ea) by {
      match AR.ReadCharE(ce, inp) {
        case None =>
    assert t' == LT.Mismatch;      // tr_readfail — flag-independent
        case Some(pair) =>
    assert t'.Read? && t'.c == pair.0
           && TreeRepLkRE(rer, qm, code, pair.1, t'.t, pc + 1, true);   // tr_read — flag-independent
      }
    }
    TreeRepLkDetermRE(rer, qm, code, inp, t, t', pc, ea);
    assert SS.Inseen(seen, t);

    // pts_skip
    bst1 := PT.PTS(inp, ta[1..], best, tb, seen);
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // bookkeeping: the new processed slot's tree is already memoized
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    SeenAddProcessedSlotRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                              PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
    assert vms2.active == s.active[1..];
  }

  /** (L4 NESTED) clone of `LiftPreserveConsumeDropLk` — GmtTieInside dropped. */
  lemma LiftPreserveConsumeDropLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                        crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                        bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                        ce: RC.char_expectation, vms2: AI.VmState,
                                        ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Consume(ce))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires AI.pc_mem(s1.isblocked, s.active[0].pc)
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // the blocked pc's memoized canonical tree IS the head's — the Consume
    // rules are flag-independent, so the recorded flag transfers.
    assert IsblockedRepLk(rer, qm, code, inp, seen, s.isblocked);
    assert AI.pc_mem(s.isblocked, th.pc) && th.pc == pc as int;
    assert AI.pc_mem(s.isblocked, pc);
    var t': LT.Tree, b': bool :| SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, b');
    TreeRepLkREAtConsume(rer, qm, code, inp, t', pc, b', ce);
    assert TreeRepLkRE(rer, qm, code, inp, t', pc, ea) by {
      match AR.ReadCharE(ce, inp) {
        case None =>
    assert t' == LT.Mismatch;      // tr_readfail — flag-independent
        case Some(pair) =>
    assert t'.Read? && t'.c == pair.0
           && TreeRepLkRE(rer, qm, code, pair.1, t'.t, pc + 1, true);   // tr_read — flag-independent
      }
    }
    TreeRepLkDetermRE(rer, qm, code, inp, t, t', pc, ea);
    assert SS.Inseen(seen, t);

    // pts_skip
    bst1 := PT.PTS(inp, ta[1..], best, tb, seen);
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // bookkeeping: the new processed slot's tree is already memoized
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    SeenAddProcessedSlotRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                              PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                              ncap, nlook, nquant);
    assert vms2.active == s.active[1..];
  }

  /** SETREG (group Open/Close): B steps the `GroupActionT` head, `gmt` moves
      by `GMUpdate` at the current index. The register-level gm effect
      (`GmOfLive` across the write == `GMOpen`/`GMClose`) is a REQUIRES — the
      dispatcher derives it from machine A's head via
      `PSM.OpenStepThreadRE`/`CloseStepThreadRE` (whose heavy positional
      hypotheses live in `PikeInvFullRE`). The written gid is OUTSIDE-look
      (`CaptureWriteIdsOutsideRE`: looks compile to gates, so main-code SetReg
      sites only target `CapIdsOutsideLooks`), hence outside `S`: the
      outside-`S` tie moves pointwise through the same `GMUpdate` on both
      sides, and the inside-`S` tie carries verbatim (look regs unchanged,
      inside groups untouched by the update). */
  lemma LiftPreserveSetRegLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                             crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                             bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                             reg: int, th': AI.Thread, vms2: AI.VmState,
                             ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.SetRegisterToCP(reg))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(capture_regs := AReg.set_reg(s.active[0].capture_regs, reg, Some(s1.cp), s1.clock),
                    pc := s.active[0].pc + 1)
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    // the value-tie boundary: SetReg gids are outside-look, hence outside S
    requires S == PIV.CapIdsInLooks(re)
    requires reg >= 0 && 0 <= s1.cp
    // (E3) freshness feed for the look-path carrier (from PikeInvFullRE's BBOf)
    requires s.clock >= 0 && CM.ThreadClocksLE(s.active[0], s.clock)
    // the register-level gm effect, supplied by the dispatcher from machine A's
    // proven step helpers (OpenStepThreadRE/CloseStepThreadRE)
    requires PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs)
          == (if reg % 2 == 0
              then LG.GMOpen(s1.cp as nat, (reg / 2) as nat,
                             PIV.GmOfLive(re, s.active[0].capture_regs, s.active[0].look_regs,
                                          s.active[0].quant_regs))
              else LG.GMClose(s1.cp as nat, (reg / 2) as nat,
                              PIV.GmOfLive(re, s.active[0].capture_regs, s.active[0].look_regs,
                                           s.active[0].quant_regs)))
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // canonical head: GroupActionT(Open/Close) with canonical child at (pc+1, ea)
    TreeRepLkREAtSetReg(rer, qm, code, inp, t, pc, ea, reg);
    assert t.GroupActionT? && (t.g.Open? || t.g.Close?);
    assert TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);
    var gid: LG.GroupId := t.g.g;

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // position: the B-side update index IS the VM's cp
    assert 0 <= s.cp <= |str| && inp == PIV.InpOfCp(str, s.cp);
    PIV.IdxInpOfCp(str, s.cp);
    var cpn: nat := s1.cp as nat;
    assert LC.Idx(inp) == cpn;
    var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // the written gid is outside-look, hence outside S
    assert pc < endl by {
      TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
      assert pc < |code| == endl + 1;
      if pc == endl {
        assert NR.GetPcRE(code, pc) == Some(RB.Accept);
        assert false;
      }
    }
    var OL := PIV.CapIdsOutsideLooks(re);
    PIV.CaptureWriteIdsOutsideRE(re, code, 0, endl, pc);
    assert reg in PIV.CaptureRegsSet(OL);
    assert gid in OL by {
      if t.g.Open? { assert reg == CP.start_reg(gid as int) == 2 * (gid as int); }
      else { assert reg == CP.end_reg(gid as int) == 2 * (gid as int) + 1; }
      if reg in (set cid: nat | cid in OL :: CP.start_reg(cid)) {
        var cid: nat :| cid in OL && reg == CP.start_reg(cid);
        assert reg == 2 * (cid as int);
        assert t.g.Open?;                              // parity
        assert cid == gid;
      } else {
        var cid: nat :| cid in OL && reg == CP.end_reg(cid);
        assert reg == 2 * (cid as int) + 1;
        assert t.g.Close?;                             // parity
        assert cid == gid;
      }
    }
    PIV.CapIdsLooksDisjoint(re);
    assert gid !in S by {
      if gid in PIV.CapIdsInLooks(re) { assert gid in OL * PIV.CapIdsInLooks(re); }
    }

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // B step: pts_active queues the child with the GMUpdate-moved gm
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm2)]);
    bst1 := PT.PTS(inp, [(t.t, gm2)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // raw witness: its walk peels the same GroupActionT (same reg pins the
    // same action via the erasure congruence), child walks at gm2
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtSetReg(rer, qm, code, inp, traw, gm, pc, ea, reg);
    assert traw.GroupActionT?;
    assert traw.g == t.g && CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == LT.GroupActionT(traw.g, CE.ProgErase(traw.t));
      assert CE.ProgErase(t) == LT.GroupActionT(t.g, CE.ProgErase(t.t));
    }
    assert WalkPairLk(rer, qm, code, inp, traw.t, gm2, pc + 1, ea);

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // value ties for th': both sides move by the SAME GMUpdate at cpn
    var gml := PIV.GmOfLive(re, th.capture_regs, th.look_regs, th.quant_regs);
    var gml2 := PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs);
    assert gml2 == LG.GMUpdate(t.g, cpn, gml) by {
      if t.g.Open? {
        assert reg == 2 * (gid as int);
        assert reg % 2 == 0 && (reg / 2) as nat == gid;
      } else {
        assert reg == 2 * (gid as int) + 1;
        assert reg % 2 == 1 && (reg / 2) as nat == gid;
      }
    }
    assert gm2 == LG.GMUpdate(t.g, cpn, gm);
    assert GmtTieOutside(re, th, gm, S) && GmtTieInside(crv, str, ov, th, gm, S, ncap, nlook, nquant);

    assert GmtTieOutside(re, th', gm2, S) by {
      forall g: LG.GroupId | g !in S
        ensures (g in gm2 <==> g in gml2) && (g in gm2 ==> gm2[g] == gml2[g])
      {
        assert (g in gm <==> g in gml) && (g in gm ==> gm[g] == gml[g]);
        if g == gid {
          if t.g.Close? {
            // GMClose reads the incoming entry — it agrees on both sides
            assert (gid in gm <==> gid in gml) && (gid in gm ==> gm[gid] == gml[gid]);
          }
        }
        // g != gid: GMUpdate touches only gid, both maps unchanged at g
      }
    }
    assert th'.look_regs == th.look_regs && th'.quant_regs == th.quant_regs;
    assert GmtTieInside(crv, str, ov, th', gm2, S, ncap, nlook, nquant) by {
      forall g: LG.GroupId | g in S && g in gm2
        ensures exists l: int ::
                  0 <= l < nlook
                  && g in PIV.CapIds(M.VBody(crv, l))
                  && M.MatchedPosLA(crv, th'.look_regs, l)
                  && var rf := M.FreshBodyMatch(crv, str, l, th'.look_regs, ov, ncap, nlook, nquant);
                  rf.Some?
                  && var gmb := PIV.GmOfLive(M.VBody(crv, l), rf.value.capture_regs,
                                             rf.value.look_regs, rf.value.quant_regs);
                  var looktype := if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead;
                  g in gmb && gm2[g] == (if looktype.Lookbehind? then LBV.SwapRange(gmb[g]) else gmb[g])
      {
        assert g != gid;
        assert g in gm && gm2[g] == gm[g];             // GMUpdate touches only gid
        var l: int :| 0 <= l < nlook
                      && g in PIV.CapIds(M.VBody(crv, l))
                      && M.MatchedPosLA(crv, th.look_regs, l)
                      && var rf := M.FreshBodyMatch(crv, str, l, th.look_regs, ov, ncap, nlook, nquant);
                      rf.Some?
                      && var gmb := PIV.GmOfLive(M.VBody(crv, l), rf.value.capture_regs,
                                                 rf.value.look_regs, rf.value.quant_regs);
                      var looktype := if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead;
                      g in gmb && gm[g] == (if looktype.Lookbehind? then LBV.SwapRange(gmb[g]) else gmb[g]);
      }
    }
    assert (th.pc + 1) as nat == pc + 1;
    assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm2, th', ncap, nlook, nquant);
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm2, th', ncap, nlook, nquant);

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // list bookkeeping
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm2)] + ta[1..])[0] == (t.t, gm2) && ([(t.t, gm2)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                        ncap, nlook, nquant);

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // ---- (E3) the look-path carrier: fresh cap stamp, no new inside-S group ----
    assert LookNestRepC(re, S, ta, s.active);
    assert LookNestOkT(re, S, gm, th);
    var Bc := s1.clock;
    assert forall k :: AI.get_idx(th.quant_regs.a_clk, k) <= Bc by {
      assert CM.RegsClocksLE(th.quant_regs, s.clock);
    }
    assert forall j: int ::
        AI.get_idx(th'.capture_regs.a_clk, j) == AI.get_idx(th.capture_regs.a_clk, j)
        || (AI.get_idx(th'.capture_regs.a_clk, j) >= 0 && AI.get_idx(th'.capture_regs.a_clk, j) >= Bc)
    by {
      RL.ASetLaws(th.capture_regs, reg, Some(s1.cp), s1.clock);
    }
    assert forall g: LG.GroupId :: g in S && g in gm2 ==> g in gm by {
      forall g: LG.GroupId | g in S && g in gm2 ensures g in gm {
        assert g != gid;
      }
    }
    LookNestOkTFreshCap(re, S, gm, gm2, th, th', Bc);
    assert LookNestRepC(re, S, [(t.t, gm2)] + ta[1..], vms2.active) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestOkT(re, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i])
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // ---- (E4) the converse carrier: look/quant banks untouched, gm grows ----
    assert LookNestBackRepC(re, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert forall g: LG.GroupId :: g in gm ==> g in gm2;   // GMOpen adds / GMClose keeps domain
    LookNestBackTRegSame(re, crv, str, ov, S, gm, gm2, th, th', ncap, nlook, nquant);
    assert LookNestBackRepC(re, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                            ncap, nlook, nquant) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestBackT(re, crv, str, ov, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i],
                              ncap, nlook, nquant)
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm2)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  /** (L4 NESTED) clone of `LiftPreserveSetRegLk` — GmtTieInside dropped. */
  lemma LiftPreserveSetRegLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                   crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                   bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                   reg: int, th': AI.Thread, vms2: AI.VmState,
                                   ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.SetRegisterToCP(reg))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(capture_regs := AReg.set_reg(s.active[0].capture_regs, reg, Some(s1.cp), s1.clock),
                    pc := s.active[0].pc + 1)
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    // the value-tie boundary: SetReg gids are outside-look, hence outside S
    requires S == PIV.CapIdsInLooks(re)
    requires reg >= 0 && 0 <= s1.cp
    // (E3) freshness feed for the look-path carrier (from PikeInvFullRE's BBOf)
    requires s.clock >= 0 && CM.ThreadClocksLE(s.active[0], s.clock)
    // the register-level gm effect, supplied by the dispatcher from machine A's
    // proven step helpers (OpenStepThreadRE/CloseStepThreadRE)
    requires PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs)
          == (if reg % 2 == 0
              then LG.GMOpen(s1.cp as nat, (reg / 2) as nat,
                             PIV.GmOfLive(re, s.active[0].capture_regs, s.active[0].look_regs,
                                          s.active[0].quant_regs))
              else LG.GMClose(s1.cp as nat, (reg / 2) as nat,
                              PIV.GmOfLive(re, s.active[0].capture_regs, s.active[0].look_regs,
                                           s.active[0].quant_regs)))
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // canonical head: GroupActionT(Open/Close) with canonical child at (pc+1, ea)
    TreeRepLkREAtSetReg(rer, qm, code, inp, t, pc, ea, reg);
    assert t.GroupActionT? && (t.g.Open? || t.g.Close?);
    assert TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);
    var gid: LG.GroupId := t.g.g;

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // position: the B-side update index IS the VM's cp
    assert 0 <= s.cp <= |str| && inp == PIV.InpOfCp(str, s.cp);
    PIV.IdxInpOfCp(str, s.cp);
    var cpn: nat := s1.cp as nat;
    assert LC.Idx(inp) == cpn;
    var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // the written gid is outside-look, hence outside S
    assert pc < endl by {
      TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
      assert pc < |code| == endl + 1;
      if pc == endl {
        assert NR.GetPcRE(code, pc) == Some(RB.Accept);
        assert false;
      }
    }
    var OL := PIV.CapIdsOutsideLooks(re);
    PIV.CaptureWriteIdsOutsideRENested(re, code, 0, endl, pc);
    assert reg in PIV.CaptureRegsSet(OL);
    assert gid in OL by {
      if t.g.Open? { assert reg == CP.start_reg(gid as int) == 2 * (gid as int); }
      else { assert reg == CP.end_reg(gid as int) == 2 * (gid as int) + 1; }
      if reg in (set cid: nat | cid in OL :: CP.start_reg(cid)) {
        var cid: nat :| cid in OL && reg == CP.start_reg(cid);
        assert reg == 2 * (cid as int);
        assert t.g.Open?;                              // parity
        assert cid == gid;
      } else {
        var cid: nat :| cid in OL && reg == CP.end_reg(cid);
        assert reg == 2 * (cid as int) + 1;
        assert t.g.Close?;                             // parity
        assert cid == gid;
      }
    }
    PIV.CapIdsLooksDisjoint(re);
    assert gid !in S by {
      if gid in PIV.CapIdsInLooks(re) { assert gid in OL * PIV.CapIdsInLooks(re); }
    }

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // B step: pts_active queues the child with the GMUpdate-moved gm
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm2)]);
    bst1 := PT.PTS(inp, [(t.t, gm2)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // raw witness: its walk peels the same GroupActionT (same reg pins the
    // same action via the erasure congruence), child walks at gm2
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtSetReg(rer, qm, code, inp, traw, gm, pc, ea, reg);
    assert traw.GroupActionT?;
    assert traw.g == t.g && CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == LT.GroupActionT(traw.g, CE.ProgErase(traw.t));
      assert CE.ProgErase(t) == LT.GroupActionT(t.g, CE.ProgErase(t.t));
    }
    assert WalkPairLk(rer, qm, code, inp, traw.t, gm2, pc + 1, ea);

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // value ties for th': both sides move by the SAME GMUpdate at cpn
    var gml := PIV.GmOfLive(re, th.capture_regs, th.look_regs, th.quant_regs);
    var gml2 := PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs);
    assert gml2 == LG.GMUpdate(t.g, cpn, gml) by {
      if t.g.Open? {
        assert reg == 2 * (gid as int);
        assert reg % 2 == 0 && (reg / 2) as nat == gid;
      } else {
        assert reg == 2 * (gid as int) + 1;
        assert reg % 2 == 1 && (reg / 2) as nat == gid;
      }
    }
    assert gm2 == LG.GMUpdate(t.g, cpn, gm);
    assert GmtTieOutside(re, th, gm, S);

    assert GmtTieOutside(re, th', gm2, S) by {
      forall g: LG.GroupId | g !in S
        ensures (g in gm2 <==> g in gml2) && (g in gm2 ==> gm2[g] == gml2[g])
      {
        assert (g in gm <==> g in gml) && (g in gm ==> gm[g] == gml[g]);
        if g == gid {
          if t.g.Close? {
            // GMClose reads the incoming entry — it agrees on both sides
            assert (gid in gm <==> gid in gml) && (gid in gm ==> gm[gid] == gml[gid]);
          }
        }
        // g != gid: GMUpdate touches only gid, both maps unchanged at g
      }
    }
    assert th'.look_regs == th.look_regs && th'.quant_regs == th.quant_regs;
    assert (th.pc + 1) as nat == pc + 1;
    assert ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm2, th', ncap, nlook, nquant);
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm2, th', ncap, nlook, nquant);

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // list bookkeeping
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                              ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm2)] + ta[1..])[0] == (t.t, gm2) && ([(t.t, gm2)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                              ncap, nlook, nquant);

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // ---- (E3) the look-path carrier: fresh cap stamp, no new inside-S group ----
    assert LookNestRepC(re, S, ta, s.active);
    assert LookNestOkT(re, S, gm, th);
    var Bc := s1.clock;
    assert forall k :: AI.get_idx(th.quant_regs.a_clk, k) <= Bc by {
      assert CM.RegsClocksLE(th.quant_regs, s.clock);
    }
    assert forall j: int ::
        AI.get_idx(th'.capture_regs.a_clk, j) == AI.get_idx(th.capture_regs.a_clk, j)
        || (AI.get_idx(th'.capture_regs.a_clk, j) >= 0 && AI.get_idx(th'.capture_regs.a_clk, j) >= Bc)
    by {
      RL.ASetLaws(th.capture_regs, reg, Some(s1.cp), s1.clock);
    }
    assert forall g: LG.GroupId :: g in S && g in gm2 ==> g in gm by {
      forall g: LG.GroupId | g in S && g in gm2 ensures g in gm {
        assert g != gid;
      }
    }
    LookNestOkTFreshCap(re, S, gm, gm2, th, th', Bc);
    assert LookNestRepC(re, S, [(t.t, gm2)] + ta[1..], vms2.active) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestOkT(re, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i])
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // ---- (E4) the converse carrier: look/quant banks untouched, gm grows ----
    assert LookNestBackRepC(re, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert forall g: LG.GroupId :: g in gm ==> g in gm2;   // GMOpen adds / GMClose keeps domain
    LookNestBackTRegSame(re, crv, str, ov, S, gm, gm2, th, th', ncap, nlook, nquant);
    assert LookNestBackRepC(re, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                            ncap, nlook, nquant) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestBackT(re, crv, str, ov, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i],
                              ncap, nlook, nquant)
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    assert {:split_here} true;   // (2026-11-05) per-section batch: one VC was a 900 s timeout in the gate
    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm2)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  /** SETQUANT (the quantifier Reset): B steps the `GroupActionT(Reset)` head;
      both value maps shed the SAME group set (`GMReset(qm.quants[q], ·)` —
      the A-side effect supplied by the dispatcher from
      `PSM.ResetStepThreadRE`), so the outside-`S` tie moves pointwise and the
      inside-`S` witnesses carry verbatim (look regs untouched; surviving
      groups unchanged). The raw layer steps by `WalkPairLkAtSetQuant`
      (forced-copy actions route OR the SQC see-through disjunct). `bq` is
      refuted by the canonical tie (`TreeRepLkREAtSetQuant`: compiled SQC
      sites always write `false`). */
  lemma LiftPreserveSetQuantLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                               crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                               bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                               q: int, bq: bool, th': AI.Thread, vms2: AI.VmState,
                               ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.SetQuantToClock(q, bq))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(quant_regs := AReg.set_reg(s.active[0].quant_regs, q,
                                                            if bq then Some(s1.cp) else None, s1.clock),
                    pc := s.active[0].pc + 1)
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    // the register-level gm effect, supplied by the dispatcher from machine A's
    // proven step helper (ResetStepThreadRE); q's table binding rides along
    requires q in qm.quants
    // (E3) look-id uniqueness (cross-lid ownership pinning for the carrier)
    requires LTB.LookUnique(re)
    // (E4) converse-carrier feeds
    requires PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires CM.ThreadRegsWf(s.active[0], ncap, nlook, nquant)
    requires s.clock >= 0 && CM.ThreadClocksLE(s.active[0], s.clock)
    requires PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs)
          == LG.GMReset(qm.quants[q],
                        PIV.GmOfLive(re, s.active[0].capture_regs, s.active[0].look_regs,
                                     s.active[0].quant_regs))
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    NoTrueStampsFromStaticRE(qm, re, code, endl);   // §2.5b stage 2a
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // canonical head: Reset(qm.quants[q]) with canonical child at (pc+1, ea);
    // pins !bq (compiled SQC sites always write false)
    TreeRepLkREAtSetQuant(rer, qm, code, inp, t, pc, ea, q, bq);
    assert !bq;
    var gidl := qm.quants[q];
    assert t.GroupActionT? && t.g == LG.Reset(gidl);
    assert TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);

    var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);
    assert gm2 == LG.GMReset(gidl, gm);

    // B step: pts_active queues the child with the Reset-moved gm
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm2)]);
    bst1 := PT.PTS(inp, [(t.t, gm2)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // raw witness: same Reset head via the SetQuant walk wrapper
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtSetQuant(rer, qm, code, inp, traw, gm, pc, ea, q);
    assert traw.GroupActionT? && traw.g == LG.Reset(gidl) == t.g;
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == LT.GroupActionT(traw.g, CE.ProgErase(traw.t));
      assert CE.ProgErase(t) == LT.GroupActionT(t.g, CE.ProgErase(t.t));
    }
    assert WalkPairLk(rer, qm, code, inp, traw.t, gm2, pc + 1, ea);

    // value ties: both maps shed the SAME set(gidl); everything else unchanged
    var gml := PIV.GmOfLive(re, th.capture_regs, th.look_regs, th.quant_regs);
    var gml2 := PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs);
    assert gml2 == LG.GMReset(gidl, gml);
    assert GmtTieOutside(re, th, gm, S) && GmtTieInside(crv, str, ov, th, gm, S, ncap, nlook, nquant);

    assert GmtTieOutside(re, th', gm2, S) by {
      forall g: LG.GroupId | g !in S
        ensures (g in gm2 <==> g in gml2) && (g in gm2 ==> gm2[g] == gml2[g])
      {
        assert (g in gm <==> g in gml) && (g in gm ==> gm[g] == gml[g]);
      }
    }
    assert th'.look_regs == th.look_regs;
    assert GmtTieInside(crv, str, ov, th', gm2, S, ncap, nlook, nquant) by {
      forall g: LG.GroupId | g in S && g in gm2
        ensures exists l2: int ::
                  0 <= l2 < nlook
                  && g in PIV.CapIds(M.VBody(crv, l2))
                  && M.MatchedPosLA(crv, th'.look_regs, l2)
                  && var rf := M.FreshBodyMatch(crv, str, l2, th'.look_regs, ov, ncap, nlook, nquant);
                  rf.Some?
                  && var gmb := PIV.GmOfLive(M.VBody(crv, l2), rf.value.capture_regs,
                                             rf.value.look_regs, rf.value.quant_regs);
                  var looktype := if 0 <= l2 < |crv.f_look_types| then crv.f_look_types[l2] else R.Lookahead;
                  g in gmb && gm2[g] == (if looktype.Lookbehind? then LBV.SwapRange(gmb[g]) else gmb[g])
      {
        assert g in gm && gm2[g] == gm[g];   // survivors of the Reset are unchanged
        var l'': int :| 0 <= l'' < nlook
                        && g in PIV.CapIds(M.VBody(crv, l''))
                        && M.MatchedPosLA(crv, th.look_regs, l'')
                        && var rf'' := M.FreshBodyMatch(crv, str, l'', th.look_regs, ov, ncap, nlook, nquant);
                        rf''.Some?
                        && var gmb'' := PIV.GmOfLive(M.VBody(crv, l''), rf''.value.capture_regs,
                                                     rf''.value.look_regs, rf''.value.quant_regs);
                        var looktype := if 0 <= l'' < |crv.f_look_types| then crv.f_look_types[l''] else R.Lookahead;
                        g in gmb'' && gm[g] == (if looktype.Lookbehind? then LBV.SwapRange(gmb''[g]) else gmb''[g]);
      }
    }
    assert (th.pc + 1) as nat == pc + 1;
    assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm2, th', ncap, nlook, nquant);
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm2, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm2)] + ta[1..])[0] == (t.t, gm2) && ([(t.t, gm2)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                        ncap, nlook, nquant);

    // ---- (E3) the look-path carrier: the Reset vacates on-path lids ----
    assert LookNestRepC(re, S, ta, s.active);
    assert LookNestOkT(re, S, gm, th);
    assert pc < endl by {
      TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
      assert pc < |code| == endl + 1;
      if pc == endl { assert NR.GetPcRE(code, pc) == Some(RB.Accept); assert false; }
    }
    PIV.QuantWriteIdsRE(re, code, 0, endl, pc);
    assert q >= 0 && (q as nat) in PIV.QuantIds(re);
    var qn: nat := q as nat;
    M.TransWfQidBody(re, qn);
    QmapOkAtQid(re, qm, qn);
    assert gidl == L.DefGroups(T.Translate(PIV.QidBody(re, qn)));
    M.TranslateDefGroupsEqCapIds(PIV.QidBody(re, qn));
    assert forall g: nat :: g in PIV.CapIds(PIV.QidBody(re, qn)) ==> g !in gm2 by {
      forall g: nat | g in PIV.CapIds(PIV.QidBody(re, qn)) ensures g !in gm2 {
        assert g in (set gx | gx in L.DefGroups(T.Translate(PIV.QidBody(re, qn))));
        assert g in gidl;                        // seq membership via the set identity
      }
    }
    assert forall g: LG.GroupId :: g in gm2 ==> g in gm;   // GMReset only removes
    assert forall j: int :: j != q ==>
                              AI.get_idx(th'.quant_regs.a_clk, j) == AI.get_idx(th.quant_regs.a_clk, j)
    by { RL.ASetLaws(th.quant_regs, q, if bq then Some(s1.cp) else None, s1.clock); }
    LookNestOkTSetQuant(re, S, gm, gm2, th, th', qn);
    assert LookNestRepC(re, S, [(t.t, gm2)] + ta[1..], vms2.active) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestOkT(re, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i])
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    // ---- (E4) converse: on-path dominance breaks; off-path scopes disjoint ----
    assert LookNestBackRepC(re, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert 0 <= q < nquant by {
      NI.QuantIdsLEMaxQuant(re);
      assert (q as nat) <= R.max_quant(re);
    }
    assert AI.get_idx(th'.quant_regs.a_clk, q) == s1.clock by {
      assert |th.quant_regs.a_clk| == nquant;
      RL.ASetLaws(th.quant_regs, q, if bq then Some(s1.cp) else None, s1.clock);
    }
    assert forall j: int :: AI.get_idx(th.look_regs.a_clk, j) < AI.get_idx(th'.quant_regs.a_clk, q as int) by {
      assert CM.RegsClocksLE(th.look_regs, s.clock);
    }
    assert forall g: LG.GroupId :: g in gm && g !in PIV.CapIds(PIV.QidBody(re, qn)) ==> g in gm2 by {
      forall g: LG.GroupId | g in gm && g !in PIV.CapIds(PIV.QidBody(re, qn))
        ensures g in gm2
      {
        assert g !in (set gx | gx in gidl);
        assert g !in gidl;
      }
    }
    LookNestBackTSetQuant(re, crv, str, ov, S, gm, gm2, th, th', qn, ncap, nlook, nquant);
    assert LookNestBackRepC(re, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                            ncap, nlook, nquant) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestBackT(re, crv, str, ov, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i],
                              ncap, nlook, nquant)
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm2)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  /** (L4 NESTED) clone of `LiftPreserveSetQuantLk` — GmtTieInside dropped. */
  lemma LiftPreserveSetQuantLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                     crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                     bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                     q: int, bq: bool, th': AI.Thread, vms2: AI.VmState,
                                     ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.SetQuantToClock(q, bq))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(quant_regs := AReg.set_reg(s.active[0].quant_regs, q,
                                                            if bq then Some(s1.cp) else None, s1.clock),
                    pc := s.active[0].pc + 1)
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    // the register-level gm effect, supplied by the dispatcher from machine A's
    // proven step helper (ResetStepThreadRE); q's table binding rides along
    requires q in qm.quants
    // (E3) look-id uniqueness (cross-lid ownership pinning for the carrier)
    requires LTB.LookUnique(re)
    // (E4) converse-carrier feeds
    requires PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires CM.ThreadRegsWf(s.active[0], ncap, nlook, nquant)
    requires s.clock >= 0 && CM.ThreadClocksLE(s.active[0], s.clock)
    requires PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs)
          == LG.GMReset(qm.quants[q],
                        PIV.GmOfLive(re, s.active[0].capture_regs, s.active[0].look_regs,
                                     s.active[0].quant_regs))
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    NoTrueStampsFromStaticNestedRE(qm, re, code, endl);   // §2.5b stage 2a
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // canonical head: Reset(qm.quants[q]) with canonical child at (pc+1, ea);
    // pins !bq (compiled SQC sites always write false)
    TreeRepLkREAtSetQuant(rer, qm, code, inp, t, pc, ea, q, bq);
    assert !bq;
    var gidl := qm.quants[q];
    assert t.GroupActionT? && t.g == LG.Reset(gidl);
    assert TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);

    var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);
    assert gm2 == LG.GMReset(gidl, gm);

    // B step: pts_active queues the child with the Reset-moved gm
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm2)]);
    bst1 := PT.PTS(inp, [(t.t, gm2)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // raw witness: same Reset head via the SetQuant walk wrapper
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtSetQuant(rer, qm, code, inp, traw, gm, pc, ea, q);
    assert traw.GroupActionT? && traw.g == LG.Reset(gidl) == t.g;
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == LT.GroupActionT(traw.g, CE.ProgErase(traw.t));
      assert CE.ProgErase(t) == LT.GroupActionT(t.g, CE.ProgErase(t.t));
    }
    assert WalkPairLk(rer, qm, code, inp, traw.t, gm2, pc + 1, ea);

    // value ties: both maps shed the SAME set(gidl); everything else unchanged
    var gml := PIV.GmOfLive(re, th.capture_regs, th.look_regs, th.quant_regs);
    var gml2 := PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs);
    assert gml2 == LG.GMReset(gidl, gml);
    assert GmtTieOutside(re, th, gm, S);

    assert GmtTieOutside(re, th', gm2, S) by {
      forall g: LG.GroupId | g !in S
        ensures (g in gm2 <==> g in gml2) && (g in gm2 ==> gm2[g] == gml2[g])
      {
        assert (g in gm <==> g in gml) && (g in gm ==> gm[g] == gml[g]);
      }
    }
    assert th'.look_regs == th.look_regs;
    assert (th.pc + 1) as nat == pc + 1;
    assert ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm2, th', ncap, nlook, nquant);
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm2, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                              ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm2)] + ta[1..])[0] == (t.t, gm2) && ([(t.t, gm2)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                              ncap, nlook, nquant);

    // ---- (E3) the look-path carrier: the Reset vacates on-path lids ----
    assert LookNestRepC(re, S, ta, s.active);
    assert LookNestOkT(re, S, gm, th);
    assert pc < endl by {
      TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
      assert pc < |code| == endl + 1;
      if pc == endl { assert NR.GetPcRE(code, pc) == Some(RB.Accept); assert false; }
    }
    PIV.QuantWriteIdsRENested(re, code, 0, endl, pc);
    assert q >= 0 && (q as nat) in PIV.QuantIds(re);
    var qn: nat := q as nat;
    M.TransWfQidBody(re, qn);
    QmapOkAtQid(re, qm, qn);
    assert gidl == L.DefGroups(T.Translate(PIV.QidBody(re, qn)));
    M.TranslateDefGroupsEqCapIds(PIV.QidBody(re, qn));
    assert forall g: nat :: g in PIV.CapIds(PIV.QidBody(re, qn)) ==> g !in gm2 by {
      forall g: nat | g in PIV.CapIds(PIV.QidBody(re, qn)) ensures g !in gm2 {
        assert g in (set gx | gx in L.DefGroups(T.Translate(PIV.QidBody(re, qn))));
        assert g in gidl;                        // seq membership via the set identity
      }
    }
    assert forall g: LG.GroupId :: g in gm2 ==> g in gm;   // GMReset only removes
    assert forall j: int :: j != q ==>
                              AI.get_idx(th'.quant_regs.a_clk, j) == AI.get_idx(th.quant_regs.a_clk, j)
    by { RL.ASetLaws(th.quant_regs, q, if bq then Some(s1.cp) else None, s1.clock); }
    LookNestOkTSetQuant(re, S, gm, gm2, th, th', qn);
    assert LookNestRepC(re, S, [(t.t, gm2)] + ta[1..], vms2.active) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestOkT(re, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i])
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    // ---- (E4) converse: on-path dominance breaks; off-path scopes disjoint ----
    assert LookNestBackRepC(re, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert 0 <= q < nquant by {
      NI.QuantIdsLEMaxQuant(re);
      assert (q as nat) <= R.max_quant(re);
    }
    assert AI.get_idx(th'.quant_regs.a_clk, q) == s1.clock by {
      assert |th.quant_regs.a_clk| == nquant;
      RL.ASetLaws(th.quant_regs, q, if bq then Some(s1.cp) else None, s1.clock);
    }
    assert forall j: int :: AI.get_idx(th.look_regs.a_clk, j) < AI.get_idx(th'.quant_regs.a_clk, q as int) by {
      assert CM.RegsClocksLE(th.look_regs, s.clock);
    }
    assert forall g: LG.GroupId :: g in gm && g !in PIV.CapIds(PIV.QidBody(re, qn)) ==> g in gm2 by {
      forall g: LG.GroupId | g in gm && g !in PIV.CapIds(PIV.QidBody(re, qn))
        ensures g in gm2
      {
        assert g !in (set gx | gx in gidl);
        assert g !in gidl;
      }
    }
    LookNestBackTSetQuantNested(re, crv, str, ov, S, gm, gm2, th, th', qn, ncap, nlook, nquant);
    assert LookNestBackRepC(re, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                            ncap, nlook, nquant) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestBackT(re, crv, str, ov, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i],
                              ncap, nlook, nquant)
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm2)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  /** FORK: forward = one `pts_active` on the `Choice` head (arms at `x`/`y`
      in VM priority order); backward = TWO B steps (`Progress` unwrap, then
      `Choice` split) per one VM step, `ea` pinned by the dispatcher from
      `EaColdOkRE`. Arms via `WalkPairLkAtForkArms` (erased-Choice witnesses);
      registers unchanged on both arms so the value ties carry verbatim.
      Mirror of `PSM.PreserveForkCase`. */
  lemma LiftPreserveForkLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                           crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                           bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                           x: int, y: int, vms2: AI.VmState,
                           ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Fork(x, y))
    // backward-fork flag pin (the dispatcher discharges it from EaColdOkRE)
    requires (x <= s.active[0].pc || y <= s.active[0].pc) ==> s.active[0].exit_allowed
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [AI.Thread(x, s.active[0].capture_regs, s.active[0].look_regs,
                                              s.active[0].quant_regs, s.active[0].exit_allowed),
                                    s.active[0].(pc := y)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    NoTrueStampsFromStaticRE(qm, re, code, endl);   // §2.5b stage 2a
    var PTS(inp, ta, best, tbl, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    TreeRepLkREAtFork(rer, qm, code, inp, t, pc, ea, x, y);
    assert x >= 0 && y >= 0;
    var th1 := AI.Thread(x, th.capture_regs, th.look_regs, th.quant_regs, ea);
    var th2 := th.(pc := y);
    assert vms2.active == [th1, th2] + s.active[1..];

    // raw witness + its arms (erased-Choice existential)
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtForkArms(rer, qm, code, inp, traw, gm, pc, ea, x, y);

    // value ties carry: both arm threads keep th's registers
    assert GmtTieOutside(re, th, gm, S) && GmtTieInside(crv, str, ov, th, gm, S, ncap, nlook, nquant);
    assert th1.capture_regs == th.capture_regs && th1.look_regs == th.look_regs
           && th1.quant_regs == th.quant_regs;
    assert GmtTieOutside(re, th1, gm, S) && GmtTieInside(crv, str, ov, th1, gm, S, ncap, nlook, nquant);
    assert GmtTieOutside(re, th2, gm, S) && GmtTieInside(crv, str, ov, th2, gm, S, ncap, nlook, nquant);

    if x as nat > pc && y as nat > pc {
      // ---- FORWARD: canonical Choice; one B step -------------------------
      assert t.Choice?
             && TreeRepLkRE(rer, qm, code, inp, t.t1, x as nat, ea)
             && TreeRepLkRE(rer, qm, code, inp, t.t2, y as nat, ea);
      assert CE.ProgErase(traw) == LT.Choice(CE.ProgErase(t.t1), CE.ProgErase(t.t2));
      assert CE.ProgErase(traw) != LT.Mismatch;
      var ta1: LT.Tree, ta2: LT.Tree :|
        CE.ProgErase(traw) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
        && WalkPairLk(rer, qm, code, inp, ta1, gm, x as nat, ea)
        && WalkPairLk(rer, qm, code, inp, ta2, gm, y as nat, ea);
      assert CE.ProgErase(ta1) == CE.ProgErase(t.t1) && CE.ProgErase(ta2) == CE.ProgErase(t.t2);
      assert th1.pc >= 0 && th2.pc >= 0;
      assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, ta1, gm, th1, ncap, nlook, nquant);
      assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, ta2, gm, th2, ncap, nlook, nquant);
      assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t.t1, gm, th1, ncap, nlook, nquant);
      assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t.t2, gm, th2, ncap, nlook, nquant);

      var na := [(t.t1, gm), (t.t2, gm)];
      assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive(na);
      bst1 := PT.PTS(inp, na + ta[1..], best, tbl, SS.AddSeenTrees(seen, t));
      assert PTL.PikeTreeStepLk(bst, bst1);
      TrcLkRefl(bst1);
      TrcLkCons(bst, bst1, bst1);

      assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                          ncap, nlook, nquant);
      assert (na + ta[1..])[0] == (t.t1, gm) && (na + ta[1..])[1..] == [(t.t2, gm)] + ta[1..];
      assert ([(t.t2, gm)] + ta[1..])[0] == (t.t2, gm) && ([(t.t2, gm)] + ta[1..])[1..] == ta[1..];
      assert vms2.active[0] == th1 && vms2.active[1..] == [th2] + s.active[1..];
      assert ([th2] + s.active[1..])[0] == th2 && ([th2] + s.active[1..])[1..] == s.active[1..];
      assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, na + ta[1..], vms2.active,
                          ncap, nlook, nquant);

      assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
      AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                   PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
      IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
    } else {
      // ---- BACKWARD (do-while): ea pinned; TWO B steps -------------------
      assert ea;
      assert t.Progress? && t.t.Choice?
             && TreeRepLkRE(rer, qm, code, inp, t.t.t1, x as nat, true)
             && TreeRepLkRE(rer, qm, code, inp, t.t.t2, y as nat, true);
      assert CE.ProgErase(t) == LT.Choice(CE.ProgErase(t.t.t1), CE.ProgErase(t.t.t2));
      assert CE.ProgErase(traw) != LT.Mismatch;
      var ta1: LT.Tree, ta2: LT.Tree :|
        CE.ProgErase(traw) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
        && WalkPairLk(rer, qm, code, inp, ta1, gm, x as nat, ea)
        && WalkPairLk(rer, qm, code, inp, ta2, gm, y as nat, ea);
      assert CE.ProgErase(ta1) == CE.ProgErase(t.t.t1) && CE.ProgErase(ta2) == CE.ProgErase(t.t.t2);
      assert th1.pc >= 0 && th2.pc >= 0 && th1.exit_allowed && th2.exit_allowed;
      assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, ta1, gm, th1, ncap, nlook, nquant);
      assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, ta2, gm, th2, ncap, nlook, nquant);
      assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t.t.t1, gm, th1, ncap, nlook, nquant);
      assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t.t.t2, gm, th2, ncap, nlook, nquant);

      var mta := [(t.t, gm)] + ta[1..];
      assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm)]);
      var mid := PT.PTS(inp, mta, best, tbl, SS.AddSeenTrees(seen, t));
      assert PTL.PikeTreeStepLk(bst, mid);
      var na := [(t.t.t1, gm), (t.t.t2, gm)];
      assert mta[0] == (t.t, gm) && mta[1..] == ta[1..];
      assert PTL.TreeBfsStepLk(t.t, gm, inp) == PT.StepActive(na);
      bst1 := PT.PTS(inp, na + ta[1..], best, tbl,
                     SS.AddSeenTrees(SS.AddSeenTrees(seen, t), t.t));
      assert PTL.PikeTreeStepLk(mid, bst1);
      TrcLkRefl(bst1);
      TrcLkCons(mid, bst1, bst1);
      TrcLkCons(bst, mid, bst1);

      assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                          ncap, nlook, nquant);
      assert (na + ta[1..])[0] == (t.t.t1, gm) && (na + ta[1..])[1..] == [(t.t.t2, gm)] + ta[1..];
      assert ([(t.t.t2, gm)] + ta[1..])[0] == (t.t.t2, gm) && ([(t.t.t2, gm)] + ta[1..])[1..] == ta[1..];
      assert vms2.active[0] == th1 && vms2.active[1..] == [th2] + s.active[1..];
      assert ([th2] + s.active[1..])[0] == th2 && ([th2] + s.active[1..])[1..] == s.active[1..];
      assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, na + ta[1..], vms2.active,
                          ncap, nlook, nquant);

      assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
      AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                   PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
      SeenGrowSeenRepLk(rer, qm, code, inp, SS.AddSeenTrees(seen, t),
                        AI.bpc_add(s.processed, th.pc, ea), t.t,
                        PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
      IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
      IsblockedGrowLk(rer, qm, code, inp, SS.AddSeenTrees(seen, t), s.isblocked, t.t);
    }
  }

  /** (L4 NESTED) clone of `LiftPreserveForkLk` — GmtTieInside dropped. */
  lemma LiftPreserveForkLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                 crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                 bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                 x: int, y: int, vms2: AI.VmState,
                                 ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Fork(x, y))
    // backward-fork flag pin (the dispatcher discharges it from EaColdOkRE)
    requires (x <= s.active[0].pc || y <= s.active[0].pc) ==> s.active[0].exit_allowed
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [AI.Thread(x, s.active[0].capture_regs, s.active[0].look_regs,
                                              s.active[0].quant_regs, s.active[0].exit_allowed),
                                    s.active[0].(pc := y)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    NoTrueStampsFromStaticNestedRE(qm, re, code, endl);   // §2.5b stage 2a
    var PTS(inp, ta, best, tbl, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    TreeRepLkREAtFork(rer, qm, code, inp, t, pc, ea, x, y);
    assert x >= 0 && y >= 0;
    var th1 := AI.Thread(x, th.capture_regs, th.look_regs, th.quant_regs, ea);
    var th2 := th.(pc := y);
    assert vms2.active == [th1, th2] + s.active[1..];

    // raw witness + its arms (erased-Choice existential)
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtForkArms(rer, qm, code, inp, traw, gm, pc, ea, x, y);

    // value ties carry: both arm threads keep th's registers
    assert GmtTieOutside(re, th, gm, S);
    assert th1.capture_regs == th.capture_regs && th1.look_regs == th.look_regs
           && th1.quant_regs == th.quant_regs;
    assert GmtTieOutside(re, th1, gm, S);
    assert GmtTieOutside(re, th2, gm, S);

    if x as nat > pc && y as nat > pc {
      // ---- FORWARD: canonical Choice; one B step -------------------------
      assert t.Choice?
             && TreeRepLkRE(rer, qm, code, inp, t.t1, x as nat, ea)
             && TreeRepLkRE(rer, qm, code, inp, t.t2, y as nat, ea);
      assert CE.ProgErase(traw) == LT.Choice(CE.ProgErase(t.t1), CE.ProgErase(t.t2));
      assert CE.ProgErase(traw) != LT.Mismatch;
      var ta1: LT.Tree, ta2: LT.Tree :|
        CE.ProgErase(traw) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
        && WalkPairLk(rer, qm, code, inp, ta1, gm, x as nat, ea)
        && WalkPairLk(rer, qm, code, inp, ta2, gm, y as nat, ea);
      assert CE.ProgErase(ta1) == CE.ProgErase(t.t1) && CE.ProgErase(ta2) == CE.ProgErase(t.t2);
      assert th1.pc >= 0 && th2.pc >= 0;
      assert ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, ta1, gm, th1, ncap, nlook, nquant);
      assert ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, ta2, gm, th2, ncap, nlook, nquant);
      assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t.t1, gm, th1, ncap, nlook, nquant);
      assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t.t2, gm, th2, ncap, nlook, nquant);

      var na := [(t.t1, gm), (t.t2, gm)];
      assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive(na);
      bst1 := PT.PTS(inp, na + ta[1..], best, tbl, SS.AddSeenTrees(seen, t));
      assert PTL.PikeTreeStepLk(bst, bst1);
      TrcLkRefl(bst1);
      TrcLkCons(bst, bst1, bst1);

      assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                                ncap, nlook, nquant);
      assert (na + ta[1..])[0] == (t.t1, gm) && (na + ta[1..])[1..] == [(t.t2, gm)] + ta[1..];
      assert ([(t.t2, gm)] + ta[1..])[0] == (t.t2, gm) && ([(t.t2, gm)] + ta[1..])[1..] == ta[1..];
      assert vms2.active[0] == th1 && vms2.active[1..] == [th2] + s.active[1..];
      assert ([th2] + s.active[1..])[0] == th2 && ([th2] + s.active[1..])[1..] == s.active[1..];
      assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, na + ta[1..], vms2.active,
                                ncap, nlook, nquant);

      assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
      AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                   PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
      IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
    } else {
      // ---- BACKWARD (do-while): ea pinned; TWO B steps -------------------
      assert ea;
      assert t.Progress? && t.t.Choice?
             && TreeRepLkRE(rer, qm, code, inp, t.t.t1, x as nat, true)
             && TreeRepLkRE(rer, qm, code, inp, t.t.t2, y as nat, true);
      assert CE.ProgErase(t) == LT.Choice(CE.ProgErase(t.t.t1), CE.ProgErase(t.t.t2));
      assert CE.ProgErase(traw) != LT.Mismatch;
      var ta1: LT.Tree, ta2: LT.Tree :|
        CE.ProgErase(traw) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
        && WalkPairLk(rer, qm, code, inp, ta1, gm, x as nat, ea)
        && WalkPairLk(rer, qm, code, inp, ta2, gm, y as nat, ea);
      assert CE.ProgErase(ta1) == CE.ProgErase(t.t.t1) && CE.ProgErase(ta2) == CE.ProgErase(t.t.t2);
      assert th1.pc >= 0 && th2.pc >= 0 && th1.exit_allowed && th2.exit_allowed;
      assert ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, ta1, gm, th1, ncap, nlook, nquant);
      assert ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, ta2, gm, th2, ncap, nlook, nquant);
      assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t.t.t1, gm, th1, ncap, nlook, nquant);
      assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t.t.t2, gm, th2, ncap, nlook, nquant);

      var mta := [(t.t, gm)] + ta[1..];
      assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm)]);
      var mid := PT.PTS(inp, mta, best, tbl, SS.AddSeenTrees(seen, t));
      assert PTL.PikeTreeStepLk(bst, mid);
      var na := [(t.t.t1, gm), (t.t.t2, gm)];
      assert mta[0] == (t.t, gm) && mta[1..] == ta[1..];
      assert PTL.TreeBfsStepLk(t.t, gm, inp) == PT.StepActive(na);
      bst1 := PT.PTS(inp, na + ta[1..], best, tbl,
                     SS.AddSeenTrees(SS.AddSeenTrees(seen, t), t.t));
      assert PTL.PikeTreeStepLk(mid, bst1);
      TrcLkRefl(bst1);
      TrcLkCons(mid, bst1, bst1);
      TrcLkCons(bst, mid, bst1);

      assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                                ncap, nlook, nquant);
      assert (na + ta[1..])[0] == (t.t.t1, gm) && (na + ta[1..])[1..] == [(t.t.t2, gm)] + ta[1..];
      assert ([(t.t.t2, gm)] + ta[1..])[0] == (t.t.t2, gm) && ([(t.t.t2, gm)] + ta[1..])[1..] == ta[1..];
      assert vms2.active[0] == th1 && vms2.active[1..] == [th2] + s.active[1..];
      assert ([th2] + s.active[1..])[0] == th2 && ([th2] + s.active[1..])[1..] == s.active[1..];
      assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, na + ta[1..], vms2.active,
                                ncap, nlook, nquant);

      assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
      AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                   PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
      SeenGrowSeenRepLk(rer, qm, code, inp, SS.AddSeenTrees(seen, t),
                        AI.bpc_add(s.processed, th.pc, ea), t.t,
                        PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
      IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
      IsblockedGrowLk(rer, qm, code, inp, SS.AddSeenTrees(seen, t), s.isblocked, t.t);
    }
  }

  /** POSITIVE GATE, PASSING: the VM writes `a_cp[l] := cp` and continues; B
      steps the `LK` head, `gmt` merges `LkResult`. Split by the lid's static
      flavour: a capturing `Lookahead` goes through the proven
      `ThreadRepLkStepCheckOracle` (with `GateStepValue` inside); a positive
      `Lookbehind` is CAPTURE-FREE (fragment), so the merge agrees with `gm`
      everywhere (`LkResultAgreeOutside` over an empty group set) and the
      inside-`S` witnesses carry across the `a_cp[l]`-only write (Case B
      pattern). Negative flavours are refuted by the polarity pin. */
  lemma LiftPreserveGatePassLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                               crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                               bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                               l: int, th': AI.Thread, vms2: AI.VmState,
                               ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires |ov| == |str| + 1                                    // L3b: the backward LB gate needs the mirror
    requires S == PIV.CapIdsInLooks(re)
    requires GateStaticsOk(qm, re, crv, ncap, nlook, nquant)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires CM.ThreadRegsWf(s.active[0], ncap, nlook, nquant)
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.CheckOracle(l))
    requires LOr.view_get_oracle(ov, s.cp, l)
    // (E3) carrier feeds: freshness, positional invariant, look uniqueness
    requires s.clock >= 0 && CM.ThreadClocksLE(s.active[0], s.clock)
    requires PSM.ThreadNestRE(re, code, endl, s.active[0].pc, s.active[0])
    requires LTB.LookUnique(re)
    // (E4) the row↔structure tie for the converse coverage
    requires LTB.LookTablesOk(re, crv)
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(pc := s.active[0].pc + 1,
                    look_regs := AReg.set_reg(s.active[0].look_regs, l, Some(s1.cp), s1.clock))
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    // (2026-08-29 E3) the preamble is an OPAQUE block: only the facts below reach the arm's VC.
    var inp := *;
    var ta: seq<(LT.Tree, LG.GroupMap)> := *;
    var best := *;
    var tbl := *;
    var seen := *;
    var th := *;
    var t := *;
    var gm: LG.GroupMap := *;
    var pc: nat := *;
    var ea := *;
    var lk := *;
    var r1 := *;
    var cp: nat := *;
    var traw: LT.Tree := *;
    var tlk := *;
    var gm2: LG.GroupMap := *;
    var la: R.lookaround := *;
    var body: R.regex := *;
    var clk := *;
    bst1 := *;
    opaque
      ensures (LS.LkResult(lk, tlk, LG.Empty, inp).Some?)
      ensures (LS.LkResult(lk, tlk, gm, inp).Some?)
      ensures (bst == PT.PTS(inp, ta, best, tbl, seen))
      ensures (th == s.active[0])
      ensures (ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant))
      ensures (|ta| > 0)
      ensures (t == ta[0].0)
      ensures (gm == ta[0].1)
      ensures (ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant))
      ensures (pc == th.pc as nat)
      ensures (ea == th.exit_allowed)
      ensures (TreeRepLkRE(rer, qm, code, inp, t, pc, ea))
      ensures (|code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept))
      ensures (pc < endl)
      ensures (l in qm.looks)
      ensures (lk == qm.looks[l].0)
      ensures (r1 == qm.looks[l].1)
      ensures (AR.PositiveL(lk) && L.Positivity(lk))
      ensures (0 <= s.cp <= |str| && inp == PIV.InpOfCp(str, s.cp))
      ensures (cp == s.cp as nat)
      ensures (TREP.CpOf(inp) == cp && TR_CpOf(inp) == cp)
      ensures (LL.OracleOkAt(rer, qm, inp))
      ensures (CE.ProgErase(traw) == CE.ProgErase(t)
                                 && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant))
      ensures (WalkPairLk(rer, qm, code, inp, traw, gm, pc, ea))
      ensures (LOr.view_get_oracle(qm.ov, TR_CpOf(inp), l))
      ensures (traw.LK? && traw.lk == lk)
      ensures (EL.LkGateOk(rer, lk, r1, inp, traw.tlk, true))
      ensures (tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk)))
      ensures (traw.tlk == tlk)
      ensures (gm2 == LS.LkResult(lk, tlk, gm, inp).value)
      ensures (WalkPairLk(rer, qm, code, inp, traw.t, gm2, pc + 1, ea))
      ensures (forall gg :: gg in L.DefGroups(r1) ==> gg !in gm)
      ensures (t.LK? && t.lk == lk && t.tlk == tlk
                   && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea))
      ensures (CE.ProgErase(traw) == LT.LK(lk, CE.ProgErase(traw.tlk), CE.ProgErase(traw.t)))
      ensures (CE.ProgErase(t) == LT.LK(lk, CE.ProgErase(t.tlk), CE.ProgErase(t.t)))
      ensures (CE.ProgErase(traw.t) == CE.ProgErase(t.t))
      ensures (LS.LkResult(t.lk, t.tlk, gm, inp) == Some(gm2))
      ensures (PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm2)]))
      ensures (bst1 == PT.PTS(inp, [(t.t, gm2)] + ta[1..], best, tbl, SS.AddSeenTrees(seen, t)))
      ensures (PTL.PikeTreeStepLk(bst, bst1))
      ensures (LTB.LookEntryOk(crv, l, la, body)
              && T.TransWf(body) && NR.LookFreeRE(body)
              && qm.looks[l].0 == T.TrLookaround(la)
              && qm.looks[l].1 == T.Translate(body)
              && (set g: LG.GroupId | g in L.DefGroups(T.Translate(body))) <= PIV.CapIdsInLooks(re)
              && var bodycode := CP.compile_to_bytecode(body);
              |bodycode| >= 1
              && PSM.StaticOkRE(qm, body, bodycode, |bodycode| - 1)
              && PSM.SizesOkRE(body, ncap, nlook, nquant)
              && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body)))
      ensures (lk == T.TrLookaround(la) && r1 == T.Translate(body))
      ensures (body == M.VBody(crv, l))
      ensures (0 <= l < nlook)
      ensures (clk == s1.clock)
      ensures (th' == th.(pc := th.pc + 1, look_regs := AReg.set_reg(th.look_regs, l, Some(cp as int), clk)))
      ensures (!la.NegLookahead? && !la.NegLookbehind?)
      ensures (S == LL.LkBodyGroups(T.Translate(re)))
    {
      var PTS(inp', ta', best', tbl', seen') := bst; inp, ta, best, tbl, seen := inp', ta', best', tbl', seen';
      th := s.active[0];
      assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
      assert |ta| > 0;
      t := ta[0].0;
      gm := ta[0].1;
      assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
      pc := th.pc as nat;
      ea := th.exit_allowed;
      assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
  
      // gate pc interior + polarity pin
      TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
      assert |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept);
      assert pc < endl;
      GatePolarityRE(re, qm, code, 0, endl, pc);
      assert l in qm.looks;
      lk := qm.looks[l].0;
      r1 := qm.looks[l].1;
      assert AR.PositiveL(lk) && L.Positivity(lk);
  
      // position glue
      assert 0 <= s.cp <= |str| && inp == PIV.InpOfCp(str, s.cp);
      cp := s.cp as nat;
      PIV.IdxInpOfCp(str, cp);
      assert TREP.CpOf(inp) == cp && TR_CpOf(inp) == cp;
      assert LL.OracleOkAt(rer, qm, inp);
  
      // raw witness at the gate: the walk lemma keys on the (true) oracle bit
      traw :| CE.ProgErase(traw) == CE.ProgErase(t)
                           && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
      assert WalkPairLk(rer, qm, code, inp, traw, gm, pc, ea);
      WalkPairLkAtCheckOracle(rer, qm, code, inp, traw, gm, pc, ea, l);
      assert LOr.view_get_oracle(qm.ov, TR_CpOf(inp), l);
      assert traw.LK? && traw.lk == lk;
      assert EL.LkGateOk(rer, lk, r1, inp, traw.tlk, true);
      tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
      assert traw.tlk == tlk;                                   // LkGateOk pins tlk functionally
      assert LS.LkResult(lk, tlk, LG.Empty, inp).Some?;
      assert LS.LkResult(lk, tlk, gm, inp).Some?;
      gm2 := LS.LkResult(lk, tlk, gm, inp).value;
      assert WalkPairLk(rer, qm, code, inp, traw.t, gm2, pc + 1, ea);
      assert forall gg :: gg in L.DefGroups(r1) ==> gg !in gm;  // the gate's own clear instance
  
      // canonical head: the LK branch of the gate rule (functional verdict Some)
      TreeRepLkREAtCheckOracle(rer, qm, code, inp, t, pc, ea, l);
      assert t.LK? && t.lk == lk && t.tlk == tlk
             && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);
  
      // erasure congruence: children tie
      assert CE.ProgErase(traw) == LT.LK(lk, CE.ProgErase(traw.tlk), CE.ProgErase(traw.t));
      assert CE.ProgErase(t) == LT.LK(lk, CE.ProgErase(t.tlk), CE.ProgErase(t.t));
      assert CE.ProgErase(traw.t) == CE.ProgErase(t.t);
  
      // B step on the canonical LK head: pts_active with the merged gm
      assert LS.LkResult(t.lk, t.tlk, gm, inp) == Some(gm2);
      assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm2)]);
      bst1 := PT.PTS(inp, [(t.t, gm2)] + ta[1..], best, tbl, SS.AddSeenTrees(seen, t));
      assert PTL.PikeTreeStepLk(bst, bst1);
      TrcLkRefl(bst1);
      TrcLkCons(bst, bst1, bst1);
  
      // the per-lid static package
      la, body :|
        LTB.LookEntryOk(crv, l, la, body)
        && T.TransWf(body) && NR.LookFreeRE(body)
        && qm.looks[l].0 == T.TrLookaround(la)
        && qm.looks[l].1 == T.Translate(body)
        && (set g: LG.GroupId | g in L.DefGroups(T.Translate(body))) <= PIV.CapIdsInLooks(re)
        && var bodycode := CP.compile_to_bytecode(body);
        |bodycode| >= 1
        && PSM.StaticOkRE(qm, body, bodycode, |bodycode| - 1)
        && PSM.SizesOkRE(body, ncap, nlook, nquant)
        && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
      assert lk == T.TrLookaround(la) && r1 == T.Translate(body);
      assert body == M.VBody(crv, l);
      assert 0 <= l < nlook;
  
      clk := s1.clock;
      assert th' == th.(pc := th.pc + 1, look_regs := AReg.set_reg(th.look_regs, l, Some(cp as int), clk));
  
      // the polarity pin refutes the negative flavours
      assert !la.NegLookahead? && !la.NegLookbehind? by {
        if la.NegLookahead? || la.NegLookbehind? { assert !L.Positivity(lk); }
      }
      M.LkBodyGroupsEqCapIdsInLooks(re);
      assert S == LL.LkBodyGroups(T.Translate(re));
    }
    assert {:split_here} true;   // (E3) section boundary: its own assertion batch

    // ---- (E3) the gate case split ----
    if la.Lookahead? {
      // ---- capturing-lookahead half: the proven crux core -------------------
      assert crv.f_look_types[l] == la && crv.f_look_types[l].Lookahead?;
      assert AI.capture_type(crv.f_look_types[l]);
      assert L.LkDir(lk) == WP.Forward;
      assert RL.ASize(th.look_regs) == nlook;
      var bodycode := CP.compile_to_bytecode(body);
      assert LT.LK(lk, tlk, traw.t) == traw;
      ThreadRepLkStepCheckOracle(rer, qm, re, code, crv, str, ov, S, lk, r1, tlk, traw.t,
                                 gm, th, l, cp, clk, body, la, bodycode, |bodycode| - 1, 0,
                                 th.quant_regs, ncap, nlook, nquant);
      assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm2, th', ncap, nlook, nquant);
    } else {
      // ---- capture-free positive look (Lookbehind) --------------------------
      assert la.Lookbehind?;
      if NR.CaptureFreeRE(body) {
        // ---- capture-free positive lookbehind: gm2 == gm, no inside-S groups --------
        assert NR.CaptureFreeRE(body);
        PIV.CaptureFreeNoCapIds(body);
        M.TranslateDefGroupsEqCapIds(body);
        assert (set g | g in L.DefGroups(r1)) == PIV.CapIds(body) == {};
        // the merge over an EMPTY group set agrees with gm everywhere
        EL.TranslateNoLkBr(body);
        LkResultAgreeOutside(rer, lk, r1, inp, tlk, gm);
        assert forall g: LG.GroupId :: (g in gm2 <==> g in gm) && (g in gm2 ==> gm2[g] == gm[g]) by {
          forall g: LG.GroupId ensures (g in gm2 <==> g in gm) && (g in gm2 ==> gm2[g] == gm[g]) {
            assert g !in (set gx | gx in L.DefGroups(r1)) by {
              if g in (set gx | gx in L.DefGroups(r1)) { assert g in PIV.CapIds(body); }
            }
          }
        }

        // outside tie: the gate-crossing frame (works for backward gates too)
        GmtTieOutsideAfterGate(rer, re, str, lk, r1, tlk, gm, th, l, cp, clk, S);
        assert GmtTieOutside(re, th', gm2, S);

        // inside tie: witnesses carry across the l-only look-reg write
        assert GmtTieInside(crv, str, ov, th, gm, S, ncap, nlook, nquant);
        assert GmtTieInside(crv, str, ov, th', gm2, S, ncap, nlook, nquant) by {
          forall g: LG.GroupId | g in S && g in gm2
            ensures exists l2: int ::
                      0 <= l2 < nlook
                      && g in PIV.CapIds(M.VBody(crv, l2))
                      && M.MatchedPosLA(crv, th'.look_regs, l2)
                      && var rf := M.FreshBodyMatch(crv, str, l2, th'.look_regs, ov, ncap, nlook, nquant);
                      rf.Some?
                      && var gmb := PIV.GmOfLive(M.VBody(crv, l2), rf.value.capture_regs,
                                                 rf.value.look_regs, rf.value.quant_regs);
                      var looktype := if 0 <= l2 < |crv.f_look_types| then crv.f_look_types[l2] else R.Lookahead;
                      g in gmb && gm2[g] == (if looktype.Lookbehind? then LBV.SwapRange(gmb[g]) else gmb[g])
          {
            assert g in gm && gm2[g] == gm[g];
            var l'': int :| 0 <= l'' < nlook
                            && g in PIV.CapIds(M.VBody(crv, l''))
                            && M.MatchedPosLA(crv, th.look_regs, l'')
                            && var rf'' := M.FreshBodyMatch(crv, str, l'', th.look_regs, ov, ncap, nlook, nquant);
                            rf''.Some?
                            && var gmb'' := PIV.GmOfLive(M.VBody(crv, l''), rf''.value.capture_regs,
                                                         rf''.value.look_regs, rf''.value.quant_regs);
                            var looktype := if 0 <= l'' < |crv.f_look_types| then crv.f_look_types[l''] else R.Lookahead;
                            g in gmb'' && gm[g] == (if looktype.Lookbehind? then LBV.SwapRange(gmb''[g]) else gmb''[g]);
            // l'' != l: the l-row's body is capture-free, so it owns no groups
            assert l'' != l by {
              if l'' == l { assert g in PIV.CapIds(M.VBody(crv, l)); assert g in PIV.CapIds(body); }
            }
            // th' differs from th only at slot l ⟹ l'' reads the SAME cp on both banks
            RL.ASetLaws(th.look_regs, l, Some(cp as int), clk);
            assert AReg.get_cp(th'.look_regs, l'') == AReg.get_cp(th.look_regs, l'');
            assert M.MatchedPosLA(crv, th'.look_regs, l'');
            assert M.FreshBodyMatch(crv, str, l'', th'.look_regs, ov, ncap, nlook, nquant)
                == M.FreshBodyMatch(crv, str, l'', th.look_regs, ov, ncap, nlook, nquant);
          }
        }
        assert (th.pc + 1) as nat == pc + 1;
        assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm2, th', ncap, nlook, nquant);
      } else {
        // ---- CAPTURING positive lookbehind: keystone-based backward gate ----
        var bodycode := CP.compile_to_bytecode(body);
        assert LT.LK(lk, tlk, traw.t) == traw;
        // ---- the keystone-gate static package for the body ----
        assert PSM.StaticOkRE(qm, body, bodycode, |bodycode| - 1);   // ⟹ CapUnique(body) & QuantUnique(body)
        assert PIV.CapUnique(body) && PIV.QuantUnique(body);
        PIV.LookCheckIdsRE(re, code, 0, endl, pc);                   // (l as nat) in LookIds(re)
        assert (l as nat) in LTB.LookIds(re);
        NI.LookBodyOfTablesTie(re, crv, l as nat);                   // VBody(crv,l) == LookBodyOfRE(re,l)
        NI.LookBodyOfFragment(re, l as nat);                        // PlusFragmentRE(body)
        assert NR.PlusFragmentRE(body);
        OS.TranslateLookFreeGroupOk(body);                         // GroupOkL(Translate(body))
        TranslateDefGroupsNoDup(body);                             // NoDupSeq == CD.NoDupG (same def)
        assert CD.NoDupG(L.DefGroups(T.Translate(body)));
        assert |ov| == |str| + 1;
        ThreadRepLkStepCheckOracleLB(rer, qm, re, code, crv, str, ov, S, lk, r1, tlk, traw.t,
                                     gm, th, l, cp, clk, body, la, bodycode, |bodycode| - 1, 0,
                                     th.quant_regs, ncap, nlook, nquant);
        assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm2, th', ncap, nlook, nquant);
      }
    }

    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm2, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm2)] + ta[1..])[0] == (t.t, gm2) && ([(t.t, gm2)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                        ncap, nlook, nquant);

    // ---- (E3) the look-path carrier: the crossing establishes lid l fresh ----
    // (2026-08-29 E3) the preamble is an OPAQUE block: only the facts below reach the arm's VC.
    var LB := *;
    opaque
      ensures (LookNestRepC(re, S, ta, s.active))
      ensures (LookNestOkT(re, S, gm, th))
      ensures (NI.NestInvRE(re, code, 0, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk, -1))
      ensures (AI.get_idx(th'.look_regs.a_clk, l) == clk && clk >= 0)
      ensures (forall k :: AI.get_idx(th.quant_regs.a_clk, k) <= AI.get_idx(th'.look_regs.a_clk, l))
      ensures (forall j: int :: j != l ==>
                                      AI.get_idx(th'.look_regs.a_clk, j) == AI.get_idx(th.look_regs.a_clk, j))
      ensures (l >= 0 && (l as nat) in LTB.LookIds(re))
      ensures (l >= 0 && (l as nat) in LTB.LookIds(re))
      ensures (LB == NI.LookBodyOfRE(re, l as nat))
      ensures (T.TransWf(LB))
      ensures (r1 == T.Translate(LB))
      ensures ((set gx | gx in L.DefGroups(r1)) == PIV.CapIds(LB))
      ensures (EL.NoLkBrL(r1))
      ensures (LL.GmAgreeOutside(gm2, gm, set g | g in L.DefGroups(r1)))
      ensures (forall g: LG.GroupId :: g in S && g in gm2 && g !in gm ==>
                                             l >= 0 && (l as nat) in LTB.LookIds(re) && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat)))
      ensures (LookNestRepC(re, S, [(t.t, gm2)] + ta[1..], vms2.active))
    {
      assert LookNestRepC(re, S, ta, s.active);
      assert LookNestOkT(re, S, gm, th);
      assert NI.NestInvRE(re, code, 0, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk, -1) by {
        assert PSM.ThreadNestRE(re, code, endl, th.pc, th);
        assert pc < endl;
      }
      RL.ASetLaws(th.look_regs, l, Some(cp as int), clk);
      assert AI.get_idx(th'.look_regs.a_clk, l) == clk && clk >= 0;
      assert forall k :: AI.get_idx(th.quant_regs.a_clk, k) <= AI.get_idx(th'.look_regs.a_clk, l) by {
        assert CM.RegsClocksLE(th.quant_regs, s.clock);
      }
      assert forall j: int :: j != l ==>
                                AI.get_idx(th'.look_regs.a_clk, j) == AI.get_idx(th.look_regs.a_clk, j);
      // ownership: the fold adds only l-owned groups (LmapOk row + fold confinement)
      PIV.LookCheckIdsRE(re, code, 0, endl, pc);
      assert l >= 0 && (l as nat) in LTB.LookIds(re);
      LmapOkAtLid(re, qm, l as nat);
      assert l >= 0 && (l as nat) in LTB.LookIds(re);   // (E3) exported: LookBodyOfRE(re, l) is well-formed in the residual
      LB := NI.LookBodyOfRE(re, l as nat);
      assert T.TransWf(LB);   // (E3) exported: Translate(LB) is well-formed in the residual
      assert r1 == T.Translate(LB);
      M.TranslateDefGroupsEqCapIds(LB);
      assert (set gx | gx in L.DefGroups(r1)) == PIV.CapIds(LB);
      EL.TranslateNoLkBr(body);
      assert EL.NoLkBrL(r1);
      LkResultAgreeOutside(rer, lk, r1, inp, tlk, gm);
      assert LL.GmAgreeOutside(gm2, gm, set g | g in L.DefGroups(r1));   // (E3) exported: the agree-outside post (gm only grows)
      assert forall g: LG.GroupId :: g in S && g in gm2 && g !in gm ==>
                                       l >= 0 && (l as nat) in LTB.LookIds(re) && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
      by {
        forall g: LG.GroupId | g in S && g in gm2 && g !in gm
          ensures g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
        {
          if g !in (set gx | gx in L.DefGroups(r1)) {
            assert g in gm;                          // GmAgreeOutside membership
            assert false;
          }
        }
      }
      LookNestOkTGatePass(re, code, endl, S, gm, gm2, th, th', pc, l);
      assert LookNestRepC(re, S, [(t.t, gm2)] + ta[1..], vms2.active) by {
        forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
          ensures LookNestOkT(re, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i])
        {
          if i == 0 {
          } else {
            assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
            assert vms2.active[i] == s.active[i];
          }
        }
      }
    }
    assert {:split_here} true;   // (E3) section boundary: its own assertion batch

    // ---- (E4) converse: the crossing's coverage from the replay↔spec tie ----
    assert LookNestBackRepC(re, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    // structural body == row body (both pin f_look_ast[l])
    NI.LookBodyOfTablesTie(re, crv, l as nat);
    var la3: R.lookaround :| LTB.LookEntryOk(crv, l, la3, NI.LookBodyOfRE(re, l as nat));
    assert NI.LookBodyOfRE(re, l as nat) == body;
    // gm only grows across the fold (its S-body keys were CLEAR coming in)
    assert forall g: LG.GroupId :: g in gm ==> g in gm2 by {
      forall g: LG.GroupId | g in gm ensures g in gm2 {
        assert g !in (set gx | gx in L.DefGroups(r1)) by {
          if g in (set gx | gx in L.DefGroups(r1)) { assert g !in gm; }
        }
      }
    }
    // the crossing coverage for l itself
    assert var rfx := M.FreshBodyMatch(crv, str, l, th'.look_regs, ov, ncap, nlook, nquant);
           rfx.Some? ==>
             forall g: LG.GroupId ::
               g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
               && g in PIV.GmOfLive(NI.LookBodyOfRE(re, l as nat), rfx.value.capture_regs,
                                    rfx.value.look_regs, rfx.value.quant_regs)
               ==> g in gm2
    by {
      var rfx := M.FreshBodyMatch(crv, str, l, th'.look_regs, ov, ncap, nlook, nquant);
      if rfx.Some? {
        if la.Lookahead? {
          M.TranslateDefGroupsEqCapIds(body);
          EL.TranslateNoLkBr(body);
          EL.ComputeTrGmIndepLk(rer, r1, inp, gm, WP.Forward);
          assert tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], inp, gm, WP.Forward);
          assert M.GmAgreeOn(gm, LG.Empty, set gx | gx in L.DefGroups(r1)) by {
            forall g: LG.GroupId | g in (set gx | gx in L.DefGroups(r1))
              ensures (g in gm <==> g in LG.Empty) && (g in gm ==> gm[g] == LG.Empty[g])
            {
              assert g !in gm;
            }
          }
          var bodycode3 := CP.compile_to_bytecode(body);
          assert AReg.get_cp(th'.look_regs, l) == Some(s1.cp) by {
            RL.ASetLaws(th.look_regs, l, Some(cp as int), clk);
          }
          M.LkReplayMatchesSpec(rer, qm, body, bodycode3, |bodycode3| - 1, 0, str, cp,
                                AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                ov, LCdn.compile_cdns(body), la, tlk, gm, ncap, nlook, nquant);
          assert crv.f_look_cdns[l] == LCdn.compile_cdns(body);      // LookEntryOk row
          var rfSpec := AI.FFindMatch(bodycode3, str,
                                      AI.FInitState(bodycode3, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                    AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                                      ov, LAnc.Forward, LCdn.compile_cdns(body)).0;
          assert rfx == rfSpec;
          assert LS.LkResult(T.TrLookaround(la), tlk, gm, inp).Some?
                 && LS.LkResult(T.TrLookaround(la), tlk, gm, inp).value == gm2 by {
            assert lk == T.TrLookaround(la);
          }
          assert M.GmAgreeOn(gm2,
                             PIV.GmOfLive(body, rfSpec.value.capture_regs,
                                          rfSpec.value.look_regs, rfSpec.value.quant_regs),
                             set gx | gx in L.DefGroups(T.Translate(body)));
          forall g: LG.GroupId |
            g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
            && g in PIV.GmOfLive(NI.LookBodyOfRE(re, l as nat), rfx.value.capture_regs,
                                 rfx.value.look_regs, rfx.value.quant_regs)
            ensures g in gm2
          {
            assert g in (set gx | gx in L.DefGroups(T.Translate(body)));
          }
        } else if NR.CaptureFreeRE(body) {
          // capture-free positive lookbehind: nothing to cover
          assert la.Lookbehind? && NR.CaptureFreeRE(body);
          PIV.CaptureFreeNoCapIds(body);
          forall g: LG.GroupId |
            g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
            && g in PIV.GmOfLive(NI.LookBodyOfRE(re, l as nat), rfx.value.capture_regs,
                                 rfx.value.look_regs, rfx.value.quant_regs)
            ensures g in gm2
          {
            assert g in PIV.CapIds(body);
            assert false;
          }
        } else {
          // CAPTURING positive lookbehind: gm2 covers the body's groups via the BACKWARD
          // keystone's key-set (SwapGm preserves keys). Mirrors the lookahead arm above.
          M.TranslateDefGroupsEqCapIds(body);
          EL.TranslateNoLkBr(body);
          EL.ComputeTrGmIndepLk(rer, r1, inp, gm, WP.Backward);
          assert tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], inp, gm, WP.Backward);
          assert M.GmAgreeOn(gm, LG.Empty, set gx | gx in L.DefGroups(r1)) by {
            forall g: LG.GroupId | g in (set gx | gx in L.DefGroups(r1))
              ensures (g in gm <==> g in LG.Empty) && (g in gm ==> gm[g] == LG.Empty[g])
            { assert g !in gm; }
          }
          var bodycode3 := CP.compile_to_bytecode(body);
          assert AReg.get_cp(th'.look_regs, l) == Some(s1.cp) by {
            RL.ASetLaws(th.look_regs, l, Some(cp as int), clk);
          }
          // static package for BackFreshBodyGmTie
          NI.LookBodyOfFragment(re, l as nat);                    // PlusFragmentRE(body)
          OS.TranslateLookFreeGroupOk(body);                      // GroupOkL(Translate(body))
          TranslateDefGroupsNoDup(body);                          // NoDupG(DefGroups(Translate(body)))
          assert PIV.CapUnique(body) && PIV.QuantUnique(body);
          // rfx == the backward run raB
          assert CP.capture_regex(crv.f_look_types[l], body) == R.reverse_regex(body);
          assert AI.capture_direction(crv.f_look_types[l]) == LAnc.Backward;
          NI.NoNulledPlusLookBody(re, l as nat);                  // §2.5b interim: NoNulledPlusRE(body)
          LBK.BackFreshBodyGmTie(rer, body, str, cp, ov, crv.f_look_cdns[l], la, tlk, gm,
                                 ncap, nlook, nquant, |str|);
          var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
          var raB := AI.FFindMatch(bcB, str,
                                   AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                 AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                                   ov, LAnc.Backward, crv.f_look_cdns[l]).0;
          assert rfx == raB;
          assert LS.LkResult(T.TrLookaround(la), tlk, gm, inp).value == gm2 by {
            assert lk == T.TrLookaround(la);
          }
          // BackFreshBodyGmTie: GmAgreeOn(SwapGm(gm2), GmOfLive(body, raB.caps), Sbody)
          forall g: LG.GroupId |
            g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
            && g in PIV.GmOfLive(NI.LookBodyOfRE(re, l as nat), rfx.value.capture_regs,
                                 rfx.value.look_regs, rfx.value.quant_regs)
            ensures g in gm2
          {
            assert g in (set gx | gx in L.DefGroups(T.Translate(body)));
            assert g in LBV.SwapGm(gm2);                          // GmAgreeOn key-set at g in Sbody
          }
        }
      }
    }
    assert forall j: int :: j != l ==>
                              AI.get_idx(th'.look_regs.a_clk, j) == AI.get_idx(th.look_regs.a_clk, j)
                              && AI.get_idx(th'.look_regs.a_cp, j) == AI.get_idx(th.look_regs.a_cp, j)
    by {
      RL.ASetLaws(th.look_regs, l, Some(cp as int), clk);
    }
    LookNestBackTGatePass(re, crv, str, ov, S, gm, gm2, th, th', l, ncap, nlook, nquant);
    assert LookNestBackRepC(re, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                            ncap, nlook, nquant) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestBackT(re, crv, str, ov, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i],
                              ncap, nlook, nquant)
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm2)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  /** (L4 NESTED) clone of `LiftPreserveGatePassLk` — GmtTieInside dropped. */
  lemma {:isolate_assertions} LiftPreserveGatePassLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                     crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                     bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                     l: int, th': AI.Thread, vms2: AI.VmState,
                                     ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires |ov| == |str| + 1                                    // L3b: the backward LB gate needs the mirror
    requires S == PIV.CapIdsInLooks(re)
    requires GateStaticsOk(qm, re, crv, ncap, nlook, nquant)
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires CM.ThreadRegsWf(s.active[0], ncap, nlook, nquant)
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.CheckOracle(l))
    requires LOr.view_get_oracle(ov, s.cp, l)
    // (E3) carrier feeds: freshness, positional invariant, look uniqueness
    requires s.clock >= 0 && CM.ThreadClocksLE(s.active[0], s.clock)
    // (2026-11-05) only the nesting conjunct of `PSM.ThreadNestRE`: with rung F's
    // per-thread stamp conjuncts in the requires, one isolated postcondition
    // obligation of this lemma passed 17 GB under the packed inputs
    requires NI.NestTopRE(re, code, endl, s.active[0].pc as nat,
                          s.active[0].capture_regs.a_clk, s.active[0].quant_regs.a_clk)
    requires LTB.LookUnique(re)
    // (E4) the row↔structure tie for the converse coverage
    requires LTB.LookTablesOk(re, crv)
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(pc := s.active[0].pc + 1,
                    look_regs := AReg.set_reg(s.active[0].look_regs, l, Some(s1.cp), s1.clock))
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    // (§2.5b/z3 4.14) recursive nullability predicates + the CIN disjunct's
    // triggered existential storm the solver; all uses here are opaque.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    // (L4 NESTED) NestedFragmentRE(re) is now DIRECT from StaticOkNestedRE
    var PTS(inp, ta, best, tbl, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // gate pc interior + polarity pin
    TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
    assert |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept);
    assert pc < endl;
    GatePolarityRE(re, qm, code, 0, endl, pc);
    assert l in qm.looks;
    var lk := qm.looks[l].0;
    var r1 := qm.looks[l].1;
    assert AR.PositiveL(lk) && L.Positivity(lk);

    // position glue
    assert 0 <= s.cp <= |str| && inp == PIV.InpOfCp(str, s.cp);
    var cp: nat := s.cp as nat;
    PIV.IdxInpOfCp(str, cp);
    assert TREP.CpOf(inp) == cp && TR_CpOf(inp) == cp;
    assert LL.OracleOkAt(rer, qm, inp);

    // raw witness at the gate: the walk lemma keys on the (true) oracle bit
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    assert WalkPairLk(rer, qm, code, inp, traw, gm, pc, ea);
    WalkPairLkAtCheckOracle(rer, qm, code, inp, traw, gm, pc, ea, l);
    assert LOr.view_get_oracle(qm.ov, TR_CpOf(inp), l);
    assert traw.LK? && traw.lk == lk;
    assert EL.LkGateOk(rer, lk, r1, inp, traw.tlk, true);
    var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
    assert traw.tlk == tlk;                                   // LkGateOk pins tlk functionally
    assert LS.LkResult(lk, tlk, LG.Empty, inp).Some?;
    assert LS.LkResult(lk, tlk, gm, inp).Some?;
    var gm2 := LS.LkResult(lk, tlk, gm, inp).value;
    assert WalkPairLk(rer, qm, code, inp, traw.t, gm2, pc + 1, ea);
    assert forall gg :: gg in L.DefGroups(r1) ==> gg !in gm;  // the gate's own clear instance

    // canonical head: the LK branch of the gate rule (functional verdict Some)
    TreeRepLkREAtCheckOracle(rer, qm, code, inp, t, pc, ea, l);
    assert t.LK? && t.lk == lk && t.tlk == tlk
           && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);

    // erasure congruence: children tie
    assert CE.ProgErase(traw) == LT.LK(lk, CE.ProgErase(traw.tlk), CE.ProgErase(traw.t));
    assert CE.ProgErase(t) == LT.LK(lk, CE.ProgErase(t.tlk), CE.ProgErase(t.t));
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t);

    // B step on the canonical LK head: pts_active with the merged gm
    assert LS.LkResult(t.lk, t.tlk, gm, inp) == Some(gm2);
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm2)]);
    bst1 := PT.PTS(inp, [(t.t, gm2)] + ta[1..], best, tbl, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // the per-lid static package
    var la: R.lookaround, body: R.regex :|
      LTB.LookEntryOk(crv, l, la, body)
      && T.TransWf(body) && NR.LookFreeRE(body)
      && qm.looks[l].0 == T.TrLookaround(la)
      && qm.looks[l].1 == T.Translate(body)
      && (set g: LG.GroupId | g in L.DefGroups(T.Translate(body))) <= PIV.CapIdsInLooks(re)
      && var bodycode := CP.compile_to_bytecode(body);
      |bodycode| >= 1
      && PSM.StaticOkRE(qm, body, bodycode, |bodycode| - 1)
      && PSM.SizesOkRE(body, ncap, nlook, nquant)
      && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
    assert lk == T.TrLookaround(la) && r1 == T.Translate(body);
    assert body == M.VBody(crv, l);
    assert 0 <= l < nlook;

    var clk := s1.clock;
    assert th' == th.(pc := th.pc + 1, look_regs := AReg.set_reg(th.look_regs, l, Some(cp as int), clk));

    // the polarity pin refutes the negative flavours
    assert !la.NegLookahead? && !la.NegLookbehind? by {
      if la.NegLookahead? || la.NegLookbehind? { assert !L.Positivity(lk); }
    }
    M.LkBodyGroupsEqCapIdsInLooks(re);
    assert S == LL.LkBodyGroups(T.Translate(re));

    if la.Lookahead? {
      // ---- capturing-lookahead half: the proven crux core -------------------
      assert crv.f_look_types[l] == la && crv.f_look_types[l].Lookahead?;
      assert AI.capture_type(crv.f_look_types[l]);
      assert L.LkDir(lk) == WP.Forward;
      assert RL.ASize(th.look_regs) == nlook;
      var bodycode := CP.compile_to_bytecode(body);
      assert LT.LK(lk, tlk, traw.t) == traw;
      // (L4 NESTED) the gate-step lemma wants the body in the positive-nesting
      // sub-fragment; under the depth-1 fragment the body is look-free, so
      // NestedFragmentRE + NegLooksLookFreeRE follow from LookFreeRE+PlusFragmentRE.
      PIV.LookCheckIdsRENested(re, code, 0, endl, pc);
      NI.LookBodyOfTablesTie(re, crv, l as nat);
      NI.NoNulledPlusLookBody(re, l as nat);   // §2.5b interim: NoNulledPlusRE(body)
      assert PSM.StaticOkRE(qm, body, bodycode, |bodycode| - 1);   // (⟹ LookBehindFragmentRE(body))
      NR.LookFreeIsPlusFragmentRE(body);                          // PlusFragmentRE(body)
      NR.LookFreePlusIsNestedRE(body);                            // NestedFragmentRE(body)
      NR.LookFreeNegLooksLookFree(body);                          // NegLooksLookFreeRE(body)
      ThreadRepLkStepCheckOracleNested(rer, qm, re, code, crv, str, ov, S, lk, r1, tlk, traw.t,
                                       gm, th, l, cp, clk, body, la, bodycode, |bodycode| - 1, 0,
                                       th.quant_regs, ncap, nlook, nquant);
      assert ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm2, th', ncap, nlook, nquant);
    } else {
      // ---- capture-free positive look (Lookbehind) --------------------------
      assert la.Lookbehind?;
      if NR.CaptureFreeRE(body) {
        // ---- capture-free positive lookbehind: gm2 == gm, no inside-S groups --------
        assert NR.CaptureFreeRE(body);
        PIV.CaptureFreeNoCapIds(body);
        M.TranslateDefGroupsEqCapIds(body);
        assert (set g | g in L.DefGroups(r1)) == PIV.CapIds(body) == {};
        // the merge over an EMPTY group set agrees with gm everywhere
        EL.TranslateNoLkBr(body);
        LkResultAgreeOutside(rer, lk, r1, inp, tlk, gm);
        assert forall g: LG.GroupId :: (g in gm2 <==> g in gm) && (g in gm2 ==> gm2[g] == gm[g]) by {
          forall g: LG.GroupId ensures (g in gm2 <==> g in gm) && (g in gm2 ==> gm2[g] == gm[g]) {
            assert g !in (set gx | gx in L.DefGroups(r1)) by {
              if g in (set gx | gx in L.DefGroups(r1)) { assert g in PIV.CapIds(body); }
            }
          }
        }

        // outside tie: the gate-crossing frame (works for backward gates too);
        // NoLkBrL(r1) (look-free body) ⟹ the recursive PikeLkRegexRec(r1).
        PIV.LookCheckIdsRENested(re, code, 0, endl, pc);
        NI.LookBodyOfTablesTie(re, crv, l as nat);
        NI.NoNulledPlusLookBody(re, l as nat);   // §2.5b interim: NoNulledPlusRE(body)
        NUL.TransNoNulledPlus(body);             // §2.5b interim: NoNulledPlusL(r1)
        EL.NoLkBrLIsPikeLkRegexRec(r1);
        GmtTieOutsideAfterGateNested(rer, re, str, lk, r1, tlk, gm, th, l, cp, clk, S);
        assert GmtTieOutside(re, th', gm2, S);

        // inside tie: witnesses carry across the l-only look-reg write
        assert (th.pc + 1) as nat == pc + 1;
        assert ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm2, th', ncap, nlook, nquant);
      } else {
        // ---- CAPTURING positive lookbehind: keystone-based backward gate ----
        var bodycode := CP.compile_to_bytecode(body);
        assert LT.LK(lk, tlk, traw.t) == traw;
        // ---- the keystone-gate static package for the body ----
        assert PSM.StaticOkRE(qm, body, bodycode, |bodycode| - 1);   // ⟹ CapUnique(body) & QuantUnique(body)
        assert PIV.CapUnique(body) && PIV.QuantUnique(body);
        PIV.LookCheckIdsRENested(re, code, 0, endl, pc);                   // (l as nat) in LookIds(re)
        assert (l as nat) in LTB.LookIds(re);
        NI.LookBodyOfTablesTie(re, crv, l as nat);                   // VBody(crv,l) == LookBodyOfRE(re,l)
        NI.NoNulledPlusLookBody(re, l as nat);                     // §2.5b interim: NoNulledPlusRE(body)
        NR.LookFreeIsPlusFragmentRE(body);                         // PlusFragmentRE(body) from StaticOkRE(body)+LookFreeRE(body)
        assert NR.PlusFragmentRE(body);
        NR.LookFreePlusIsNestedRE(body);                           // NestedFragmentRE(body)
        NR.LookFreeNegLooksLookFree(body);                         // NegLooksLookFreeRE(body)
        assert |ov| == |str| + 1;
        ThreadRepLkStepCheckOracleLBNested(rer, qm, re, code, crv, str, ov, S, lk, r1, tlk, traw.t,
                                           gm, th, l, cp, clk, body, la, bodycode, |bodycode| - 1, 0,
                                           th.quant_regs, ncap, nlook, nquant);
        assert ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm2, th', ncap, nlook, nquant);
      }
    }

    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm2, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                              ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm2)] + ta[1..])[0] == (t.t, gm2) && ([(t.t, gm2)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                              ncap, nlook, nquant);

    // ---- (E3) the look-path carrier: the crossing establishes lid l fresh ----
    assert LookNestRepC(re, S, ta, s.active);
    assert LookNestOkT(re, S, gm, th);
    assert NI.NestInvRE(re, code, 0, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk, -1) by {
      assert NI.NestTopRE(re, code, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk);
      assert pc < endl;
    }
    RL.ASetLaws(th.look_regs, l, Some(cp as int), clk);
    assert AI.get_idx(th'.look_regs.a_clk, l) == clk && clk >= 0;
    assert forall k :: AI.get_idx(th.quant_regs.a_clk, k) <= AI.get_idx(th'.look_regs.a_clk, l) by {
      assert CM.RegsClocksLE(th.quant_regs, s.clock);
    }
    assert forall j: int :: j != l ==>
                              AI.get_idx(th'.look_regs.a_clk, j) == AI.get_idx(th.look_regs.a_clk, j);
    // ownership: the fold adds only l-owned groups (LmapOk row + fold confinement)
    PIV.LookCheckIdsRENested(re, code, 0, endl, pc);
    assert l >= 0 && (l as nat) in LTB.LookIds(re);
    LmapOkAtLid(re, qm, l as nat);
    var LB := NI.LookBodyOfRE(re, l as nat);
    assert r1 == T.Translate(LB);
    M.TranslateDefGroupsEqCapIds(LB);
    assert (set gx | gx in L.DefGroups(r1)) == PIV.CapIds(LB);
    EL.TranslateNoLkBr(body);
    assert EL.NoLkBrL(r1);
    LkResultAgreeOutside(rer, lk, r1, inp, tlk, gm);
    assert forall g: LG.GroupId :: g in S && g in gm2 && g !in gm ==>
                                     l >= 0 && (l as nat) in LTB.LookIds(re) && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
    by {
      forall g: LG.GroupId | g in S && g in gm2 && g !in gm
        ensures g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
      {
        if g !in (set gx | gx in L.DefGroups(r1)) {
          assert g in gm;                          // GmAgreeOutside membership
          assert false;
        }
      }
    }
    // (L4 NESTED) the fold sits DIRECTLY in lid l's body, not a nested look:
    // the gate body (GateStaticsOk) is look-free, so CapIdsInLooks(body) == {}.
    NI.LookBodyOfTablesTie(re, crv, l as nat);       // VBody(crv,l) == LookBodyOfRE(re,l) == body
    PIV.LookFreeCapIdsInLooksEmpty(body);            // CapIdsInLooks(body) == {}
    assert PIV.CapIdsInLooks(NI.LookBodyOfRE(re, l as nat)) == {};
    LookNestOkTGatePassNested(re, code, endl, S, gm, gm2, th, th', pc, l);
    assert LookNestRepC(re, S, [(t.t, gm2)] + ta[1..], vms2.active) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestOkT(re, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i])
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    // ---- (E4) converse: the crossing's coverage from the replay↔spec tie ----
    assert LookNestBackRepC(re, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    // structural body == row body (both pin f_look_ast[l])
    NI.LookBodyOfTablesTie(re, crv, l as nat);
    var la3: R.lookaround :| LTB.LookEntryOk(crv, l, la3, NI.LookBodyOfRE(re, l as nat));
    assert NI.LookBodyOfRE(re, l as nat) == body;
    // gm only grows across the fold (its S-body keys were CLEAR coming in)
    assert forall g: LG.GroupId :: g in gm ==> g in gm2 by {
      forall g: LG.GroupId | g in gm ensures g in gm2 {
        assert g !in (set gx | gx in L.DefGroups(r1)) by {
          if g in (set gx | gx in L.DefGroups(r1)) { assert g !in gm; }
        }
      }
    }
    // the crossing coverage for l itself
    assert var rfx := M.FreshBodyMatch(crv, str, l, th'.look_regs, ov, ncap, nlook, nquant);
           rfx.Some? ==>
             forall g: LG.GroupId ::
               g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
               && g in PIV.GmOfLive(NI.LookBodyOfRE(re, l as nat), rfx.value.capture_regs,
                                    rfx.value.look_regs, rfx.value.quant_regs)
               ==> g in gm2
    by {
      var rfx := M.FreshBodyMatch(crv, str, l, th'.look_regs, ov, ncap, nlook, nquant);
      if rfx.Some? {
        if la.Lookahead? {
          M.TranslateDefGroupsEqCapIds(body);
          EL.TranslateNoLkBr(body);
          EL.ComputeTrGmIndepLk(rer, r1, inp, gm, WP.Forward);
          assert tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], inp, gm, WP.Forward);
          assert M.GmAgreeOn(gm, LG.Empty, set gx | gx in L.DefGroups(r1)) by {
            forall g: LG.GroupId | g in (set gx | gx in L.DefGroups(r1))
              ensures (g in gm <==> g in LG.Empty) && (g in gm ==> gm[g] == LG.Empty[g])
            {
              assert g !in gm;
            }
          }
          var bodycode3 := CP.compile_to_bytecode(body);
          assert AReg.get_cp(th'.look_regs, l) == Some(s1.cp) by {
            RL.ASetLaws(th.look_regs, l, Some(cp as int), clk);
          }
          M.LkReplayMatchesSpec(rer, qm, body, bodycode3, |bodycode3| - 1, 0, str, cp,
                                AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                ov, LCdn.compile_cdns(body), la, tlk, gm, ncap, nlook, nquant);
          assert crv.f_look_cdns[l] == LCdn.compile_cdns(body);      // LookEntryOk row
          var rfSpec := AI.FFindMatch(bodycode3, str,
                                      AI.FInitState(bodycode3, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                    AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                                      ov, LAnc.Forward, LCdn.compile_cdns(body)).0;
          assert rfx == rfSpec;
          assert LS.LkResult(T.TrLookaround(la), tlk, gm, inp).Some?
                 && LS.LkResult(T.TrLookaround(la), tlk, gm, inp).value == gm2 by {
            assert lk == T.TrLookaround(la);
          }
          assert M.GmAgreeOn(gm2,
                             PIV.GmOfLive(body, rfSpec.value.capture_regs,
                                          rfSpec.value.look_regs, rfSpec.value.quant_regs),
                             set gx | gx in L.DefGroups(T.Translate(body)));
          forall g: LG.GroupId |
            g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
            && g in PIV.GmOfLive(NI.LookBodyOfRE(re, l as nat), rfx.value.capture_regs,
                                 rfx.value.look_regs, rfx.value.quant_regs)
            ensures g in gm2
          {
            assert g in (set gx | gx in L.DefGroups(T.Translate(body)));
          }
        } else if NR.CaptureFreeRE(body) {
          // capture-free positive lookbehind: nothing to cover
          assert la.Lookbehind? && NR.CaptureFreeRE(body);
          PIV.CaptureFreeNoCapIds(body);
          forall g: LG.GroupId |
            g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
            && g in PIV.GmOfLive(NI.LookBodyOfRE(re, l as nat), rfx.value.capture_regs,
                                 rfx.value.look_regs, rfx.value.quant_regs)
            ensures g in gm2
          {
            assert g in PIV.CapIds(body);
            assert false;
          }
        } else {
          // CAPTURING positive lookbehind: gm2 covers the body's groups via the BACKWARD
          // keystone's key-set (SwapGm preserves keys). Mirrors the lookahead arm above.
          M.TranslateDefGroupsEqCapIds(body);
          EL.TranslateNoLkBr(body);
          EL.ComputeTrGmIndepLk(rer, r1, inp, gm, WP.Backward);
          assert tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], inp, gm, WP.Backward);
          assert M.GmAgreeOn(gm, LG.Empty, set gx | gx in L.DefGroups(r1)) by {
            forall g: LG.GroupId | g in (set gx | gx in L.DefGroups(r1))
              ensures (g in gm <==> g in LG.Empty) && (g in gm ==> gm[g] == LG.Empty[g])
            { assert g !in gm; }
          }
          var bodycode3 := CP.compile_to_bytecode(body);
          assert AReg.get_cp(th'.look_regs, l) == Some(s1.cp) by {
            RL.ASetLaws(th.look_regs, l, Some(cp as int), clk);
          }
          // static package for BackFreshBodyGmTie
          assert PSM.StaticOkRE(qm, body, bodycode3, |bodycode3| - 1);   // (⇒ LookBehindFragmentRE(body))
          NR.LookFreeIsPlusFragmentRE(body);                     // PlusFragmentRE(body)
          OS.TranslateLookFreeGroupOk(body);                      // GroupOkL(Translate(body))
          TranslateDefGroupsNoDup(body);                          // NoDupG(DefGroups(Translate(body)))
          assert PIV.CapUnique(body) && PIV.QuantUnique(body);
          // rfx == the backward run raB
          assert CP.capture_regex(crv.f_look_types[l], body) == R.reverse_regex(body);
          assert AI.capture_direction(crv.f_look_types[l]) == LAnc.Backward;
          NI.NoNulledPlusLookBody(re, l as nat);                  // §2.5b interim: NoNulledPlusRE(body)
          LBK.BackFreshBodyGmTie(rer, body, str, cp, ov, crv.f_look_cdns[l], la, tlk, gm,
                                 ncap, nlook, nquant, |str|);
          var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
          var raB := AI.FFindMatch(bcB, str,
                                   AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                 AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                                   ov, LAnc.Backward, crv.f_look_cdns[l]).0;
          assert rfx == raB;
          assert LS.LkResult(T.TrLookaround(la), tlk, gm, inp).value == gm2 by {
            assert lk == T.TrLookaround(la);
          }
          // BackFreshBodyGmTie: GmAgreeOn(SwapGm(gm2), GmOfLive(body, raB.caps), Sbody)
          forall g: LG.GroupId |
            g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
            && g in PIV.GmOfLive(NI.LookBodyOfRE(re, l as nat), rfx.value.capture_regs,
                                 rfx.value.look_regs, rfx.value.quant_regs)
            ensures g in gm2
          {
            assert g in (set gx | gx in L.DefGroups(T.Translate(body)));
            assert g in LBV.SwapGm(gm2);                          // GmAgreeOn key-set at g in Sbody
          }
        }
      }
    }
    assert forall j: int :: j != l ==>
                              AI.get_idx(th'.look_regs.a_clk, j) == AI.get_idx(th.look_regs.a_clk, j)
                              && AI.get_idx(th'.look_regs.a_cp, j) == AI.get_idx(th.look_regs.a_cp, j)
    by {
      RL.ASetLaws(th.look_regs, l, Some(cp as int), clk);
    }
    LookNestBackTGatePass(re, crv, str, ov, S, gm, gm2, th, th', l, ncap, nlook, nquant);
    assert LookNestBackRepC(re, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                            ncap, nlook, nquant) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestBackT(re, crv, str, ov, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i],
                              ncap, nlook, nquant)
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm2)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  /** NEGATIVE GATE, PASSING (clear bit): zero-width, no register write; B
      steps the `LK` head — a succeeding negative look's merge IS the running
      map (`LkResult` returns `Some(gm)`), so every tie transfers verbatim. */
  lemma LiftPreserveNegGatePassLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                  crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                  bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                  l: int, vms2: AI.VmState,
                                  ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires qm.ov == ov
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.NegCheckOracle(l))
    requires !LOr.view_get_oracle(ov, s.cp, l)
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [s.active[0].(pc := s.active[0].pc + 1)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    var th' := th.(pc := th.pc + 1);
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // polarity + the bit ⟹ the functional verdict is Some (negative passes)
    TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
    assert |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept);
    assert pc < endl;
    GatePolarityRE(re, qm, code, 0, endl, pc);
    assert l in qm.looks;
    var lk := qm.looks[l].0;
    var r1 := qm.looks[l].1;
    assert AR.PositiveL(lk) == L.Positivity(lk);
    assert !L.Positivity(lk);
    var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
    assert LL.OracleOkAt(rer, qm, inp);
    PIV.IdxInpOfCp(str, s.cp as nat);
    assert TREP.CpOf(inp) == s.cp as nat;
    assert qm.looks[l] == (lk, r1);
    assert LOr.view_get_oracle(qm.ov, TREP.CpOf(inp), l)
      <==> LT.TreeRes(tlk, LG.Empty, inp, L.LkDir(lk)).Some?;
    assert LS.LkResult(lk, tlk, LG.Empty, inp).Some?;      // clear bit + negative

    // canonical head: the LK branch of the gate rule
    TreeRepLkREAtNegCheckOracle(rer, qm, code, inp, t, pc, ea, l);
    assert t.LK? && t.lk == lk && t.tlk == tlk
           && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);

    // B step: the merge at the RUNNING map is Some(gm) — the identity
    EL.LkResultGmIndep(lk, tlk, gm, inp);
    assert LS.LkResult(lk, tlk, gm, inp).Some?;
    assert LS.LkResult(lk, tlk, gm, inp).value == gm;      // negative: Some(gm)
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm)]);
    bst1 := PT.PTS(inp, [(t.t, gm)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // the child pairing: the raw witness steps by the neg-gate walk core; the
    // erasure tie transports the child
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtNegCheckOracle(rer, qm, code, inp, traw, gm, pc, ea, l);
    assert traw.LK? && WalkPairLk(rer, qm, code, inp, traw.t, gm, pc + 1, ea);
    assert (th.pc + 1) as nat == pc + 1;
    assert GmtTieOutside(re, th', gm, S);
    assert GmtTieInside(crv, str, ov, th', gm, S, ncap, nlook, nquant);
    assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm, th', ncap, nlook, nquant);
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == LT.LK(traw.lk, CE.ProgErase(traw.tlk), CE.ProgErase(traw.t));
      assert CE.ProgErase(t) == LT.LK(t.lk, CE.ProgErase(t.tlk), CE.ProgErase(t.t));
    }
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm)] + ta[1..])[0] == (t.t, gm) && ([(t.t, gm)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm)] + ta[1..], vms2.active,
                        ncap, nlook, nquant);

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  /** (L4 NESTED) clone of `LiftPreserveNegGatePassLk` — GmtTieInside dropped. */
  lemma LiftPreserveNegGatePassLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                        crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                        bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                        l: int, vms2: AI.VmState,
                                        ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires qm.ov == ov
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.NegCheckOracle(l))
    requires !LOr.view_get_oracle(ov, s.cp, l)
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [s.active[0].(pc := s.active[0].pc + 1)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    var th' := th.(pc := th.pc + 1);
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // polarity + the bit ⟹ the functional verdict is Some (negative passes)
    TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
    assert |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept);
    assert pc < endl;
    GatePolarityRE(re, qm, code, 0, endl, pc);
    assert l in qm.looks;
    var lk := qm.looks[l].0;
    var r1 := qm.looks[l].1;
    assert AR.PositiveL(lk) == L.Positivity(lk);
    assert !L.Positivity(lk);
    var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
    assert LL.OracleOkAt(rer, qm, inp);
    PIV.IdxInpOfCp(str, s.cp as nat);
    assert TREP.CpOf(inp) == s.cp as nat;
    assert qm.looks[l] == (lk, r1);
    assert LOr.view_get_oracle(qm.ov, TREP.CpOf(inp), l)
      <==> LT.TreeRes(tlk, LG.Empty, inp, L.LkDir(lk)).Some?;
    assert LS.LkResult(lk, tlk, LG.Empty, inp).Some?;      // clear bit + negative

    // canonical head: the LK branch of the gate rule
    TreeRepLkREAtNegCheckOracle(rer, qm, code, inp, t, pc, ea, l);
    assert t.LK? && t.lk == lk && t.tlk == tlk
           && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);

    // B step: the merge at the RUNNING map is Some(gm) — the identity
    EL.LkResultGmIndep(lk, tlk, gm, inp);
    assert LS.LkResult(lk, tlk, gm, inp).Some?;
    assert LS.LkResult(lk, tlk, gm, inp).value == gm;      // negative: Some(gm)
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm)]);
    bst1 := PT.PTS(inp, [(t.t, gm)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // the child pairing: the raw witness steps by the neg-gate walk core; the
    // erasure tie transports the child
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtNegCheckOracle(rer, qm, code, inp, traw, gm, pc, ea, l);
    assert traw.LK? && WalkPairLk(rer, qm, code, inp, traw.t, gm, pc + 1, ea);
    assert (th.pc + 1) as nat == pc + 1;
    assert GmtTieOutside(re, th', gm, S);
    assert ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm, th', ncap, nlook, nquant);
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == LT.LK(traw.lk, CE.ProgErase(traw.tlk), CE.ProgErase(traw.t));
      assert CE.ProgErase(t) == LT.LK(t.lk, CE.ProgErase(t.tlk), CE.ProgErase(t.t));
    }
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                              ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm)] + ta[1..])[0] == (t.t, gm) && ([(t.t, gm)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm)] + ta[1..], vms2.active,
                              ncap, nlook, nquant);

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  /** GATE KILL (either polarity, failing bit): the head canonical tree is
      `LKFail` — the polarity pin (`GatePolarityRE`) + the oracle column
      (`OracleOkAt`) convert the failing BIT into a `None` functional verdict,
      which is exactly the canonical rule's `LKFail` branch. B drops the head
      with an empty `pts_active`. */
  lemma LiftPreserveGateKillLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                               crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                               bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                               l: int, pos: bool, vms2: AI.VmState,
                               ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires qm.ov == ov
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat)
          == Some(if pos then RB.CheckOracle(l) else RB.NegCheckOracle(l))
    requires LOr.view_get_oracle(ov, s.cp, l) != pos
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // the gate pc is interior (endl holds Accept), so the polarity pin applies
    TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
    assert |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept);
    assert pc < endl;
    GatePolarityRE(re, qm, code, 0, endl, pc);
    assert l in qm.looks;
    var lk := qm.looks[l].0;
    var r1 := qm.looks[l].1;
    assert AR.PositiveL(lk) == L.Positivity(lk);
    assert L.Positivity(lk) == pos;

    // the bit at this position IS the body tree's verdict (oracle column)
    var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
    assert LL.OracleOkAt(rer, qm, inp);          // inp == inp0 instance of OracleOkSuffix
    PIV.IdxInpOfCp(str, s.cp as nat);
    assert TREP.CpOf(inp) == s.cp as nat;
    assert qm.looks[l] == (lk, r1);
    assert LOr.view_get_oracle(qm.ov, TREP.CpOf(inp), l)
      <==> LT.TreeRes(tlk, LG.Empty, inp, L.LkDir(lk)).Some?;
    // failing bit + polarity ⟹ the functional verdict is None (both flavours)
    assert LS.LkResult(lk, tlk, LG.Empty, inp).None?;

    // canonical head: the LKFail branch of the gate rule
    if pos {
      TreeRepLkREAtCheckOracle(rer, qm, code, inp, t, pc, ea, l);
    } else {
      TreeRepLkREAtNegCheckOracle(rer, qm, code, inp, t, pc, ea, l);
    }
    assert t == LT.LKFail(lk, tlk);
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([]);
    bst1 := LiftDropDeadHeadLk(rer, qm, re, code, endl, crv, str, ov, S,
                               bst, s, s1, vms2, ncap, nlook, nquant);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);
  }

  /** (L4 NESTED) clone of `LiftPreserveGateKillLk` — GmtTieInside dropped. */
  lemma LiftPreserveGateKillLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                     crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                     bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                     l: int, pos: bool, vms2: AI.VmState,
                                     ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires qm.ov == ov
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat)
          == Some(if pos then RB.CheckOracle(l) else RB.NegCheckOracle(l))
    requires LOr.view_get_oracle(ov, s.cp, l) != pos
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // the gate pc is interior (endl holds Accept), so the polarity pin applies
    TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
    assert |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept);
    assert pc < endl;
    GatePolarityRE(re, qm, code, 0, endl, pc);
    assert l in qm.looks;
    var lk := qm.looks[l].0;
    var r1 := qm.looks[l].1;
    assert AR.PositiveL(lk) == L.Positivity(lk);
    assert L.Positivity(lk) == pos;

    // the bit at this position IS the body tree's verdict (oracle column)
    var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
    assert LL.OracleOkAt(rer, qm, inp);          // inp == inp0 instance of OracleOkSuffix
    PIV.IdxInpOfCp(str, s.cp as nat);
    assert TREP.CpOf(inp) == s.cp as nat;
    assert qm.looks[l] == (lk, r1);
    assert LOr.view_get_oracle(qm.ov, TREP.CpOf(inp), l)
      <==> LT.TreeRes(tlk, LG.Empty, inp, L.LkDir(lk)).Some?;
    // failing bit + polarity ⟹ the functional verdict is None (both flavours)
    assert LS.LkResult(lk, tlk, LG.Empty, inp).None?;

    // canonical head: the LKFail branch of the gate rule
    if pos {
      TreeRepLkREAtCheckOracle(rer, qm, code, inp, t, pc, ea, l);
    } else {
      TreeRepLkREAtNegCheckOracle(rer, qm, code, inp, t, pc, ea, l);
    }
    assert t == LT.LKFail(lk, tlk);
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([]);
    bst1 := LiftDropDeadHeadLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                     bst, s, s1, vms2, ncap, nlook, nquant);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);
  }

  /** ENDLOOP, PASSING (`exit_allowed`): B steps the `Progress` head (unwrap,
      same gm, child at `pc+1`/CanExit). `Progress` is erasure-transparent, so
      the raw child witness is just the raw walk's own child. */
  lemma LiftPreserveEndLoopPassLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                  crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                  bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                  vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.EndLoop)
    requires s.active[0].exit_allowed
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [s.active[0].(pc := s.active[0].pc + 1)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    var th' := th.(pc := th.pc + 1);
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // canonical head: Progress with canonical child at (pc+1, true)
    TreeRepLkREAtEndLoop(rer, qm, code, inp, t, pc, ea);
    assert t.Progress? && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, true);

    // B step: pts_active queues the child with the same gm
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm)]);
    bst1 := PT.PTS(inp, [(t.t, gm)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // the child pairing: the raw witness unwraps its own Progress; erasure is
    // transparent to the guard on BOTH sides
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtEndLoop(rer, qm, code, inp, traw, gm, pc, ea);
    assert traw.Progress? && WalkPairLk(rer, qm, code, inp, traw.t, gm, pc + 1, true);
    assert (th.pc + 1) as nat == pc + 1;
    assert th'.exit_allowed == true;
    assert GmtTieOutside(re, th', gm, S);
    assert GmtTieInside(crv, str, ov, th', gm, S, ncap, nlook, nquant);
    assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm, th', ncap, nlook, nquant);
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == CE.ProgErase(traw.t);   // Progress transparent
      assert CE.ProgErase(t) == CE.ProgErase(t.t);
    }
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm)] + ta[1..])[0] == (t.t, gm) && ([(t.t, gm)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm)] + ta[1..], vms2.active,
                        ncap, nlook, nquant);

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  /** (L4 NESTED) clone of `LiftPreserveEndLoopPassLk` — GmtTieInside dropped. */
  lemma LiftPreserveEndLoopPassLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                        crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                        bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                        vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.EndLoop)
    requires s.active[0].exit_allowed
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [s.active[0].(pc := s.active[0].pc + 1)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    var th' := th.(pc := th.pc + 1);
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // canonical head: Progress with canonical child at (pc+1, true)
    TreeRepLkREAtEndLoop(rer, qm, code, inp, t, pc, ea);
    assert t.Progress? && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, true);

    // B step: pts_active queues the child with the same gm
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm)]);
    bst1 := PT.PTS(inp, [(t.t, gm)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // the child pairing: the raw witness unwraps its own Progress; erasure is
    // transparent to the guard on BOTH sides
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtEndLoop(rer, qm, code, inp, traw, gm, pc, ea);
    assert traw.Progress? && WalkPairLk(rer, qm, code, inp, traw.t, gm, pc + 1, true);
    assert (th.pc + 1) as nat == pc + 1;
    assert th'.exit_allowed == true;
    assert GmtTieOutside(re, th', gm, S);
    assert ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm, th', ncap, nlook, nquant);
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == CE.ProgErase(traw.t);   // Progress transparent
      assert CE.ProgErase(t) == CE.ProgErase(t.t);
    }
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                              ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm)] + ta[1..])[0] == (t.t, gm) && ([(t.t, gm)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm)] + ta[1..], vms2.active,
                              ncap, nlook, nquant);

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  /** ENDLOOP, KILLING (`!exit_allowed`): the head canonical tree is
      `Mismatch` (`tr_progressfail`), B drops it. */
  lemma LiftPreserveEndLoopKillLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                  crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                  bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                  vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.EndLoop)
    requires !s.active[0].exit_allowed
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, ta[0].1, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, th.exit_allowed);
    TreeRepLkREAtEndLoop(rer, qm, code, inp, t, pc, th.exit_allowed);
    assert t == LT.Mismatch;
    assert PTL.TreeBfsStepLk(t, ta[0].1, inp) == PT.StepActive([]);
    bst1 := LiftDropDeadHeadLk(rer, qm, re, code, endl, crv, str, ov, S,
                               bst, s, s1, vms2, ncap, nlook, nquant);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);
  }

  /** (L4 NESTED) clone of `LiftPreserveEndLoopKillLk` — GmtTieInside dropped. */
  lemma LiftPreserveEndLoopKillLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                        crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                        bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                        vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.EndLoop)
    requires !s.active[0].exit_allowed
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, ta[0].1, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, th.exit_allowed);
    TreeRepLkREAtEndLoop(rer, qm, code, inp, t, pc, th.exit_allowed);
    assert t == LT.Mismatch;
    assert PTL.TreeBfsStepLk(t, ta[0].1, inp) == PT.StepActive([]);
    bst1 := LiftDropDeadHeadLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                     bst, s, s1, vms2, ncap, nlook, nquant);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);
  }

  /** ANCHOR, PASSING: B steps the `AnchorPass` head (child, same gm); the
      VM/spec branch agreement rides `ContextOkRE` + `AnchorAgreeInput`; the
      erasure tie pins the RAW witness's shape (a `Mismatch` witness would
      erase to `Mismatch`, contradicting the canonical `AnchorPass`). */
  lemma LiftPreserveAnchorPassLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                 crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                 bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                 a: R.anchor, vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires !rer.multiline
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.AnchorAssertion(a))
    requires LAnc.is_satisfied(a, s.context, LAnc.Forward)
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [s.active[0].(pc := s.active[0].pc + 1)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    var th' := th.(pc := th.pc + 1);
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // the VM-side check IS the spec-side check
    assert PIV.ContextOkRE(str, s.cp, s.context);
    PSM.ContextOkIsCtxOf(str, s.cp as nat);
    assert LAnc.is_satisfied(a, TREP.CtxOf(inp), LAnc.Forward);
    TREP.AnchorAgreeInput(rer, a, inp);
    assert LS.AnchorSatisfied(rer, T.TrAnchor(a), inp);

    // canonical head: AnchorPass with canonical child at (pc+1, ea)
    TreeRepLkREAtAnchor(rer, qm, code, inp, t, pc, ea, a);
    assert t.AnchorPass? && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);

    // B step: pts_active queues the child with the same gm
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm)]);
    bst1 := PT.PTS(inp, [(t.t, gm)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // the child pairing: raw witness steps by the proven Anchor core; the
    // erasure tie transports to the canonical child
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    assert traw.AnchorPass? by {
      if !traw.AnchorPass? {
        var acts: LS.Actions, b: BS.LoopBool :|
          AR.ActionsRepL(rer, qm, acts, code, pc)
          && EL.PikeLkActions(acts)
          && ATR.EaOf(b) == ea
          && EL.BoolTreeLk(rer, acts, inp, b, traw)
          && GateAheadClear(acts, gm)
          && WalkDefsOk(acts);
        assert TtLk(rer, qm, code, inp, traw, pc, ea);
        TtLkAtAnchor(rer, qm, code, inp, traw, pc, ea, a);
        assert traw == LT.Mismatch;
        assert CE.ProgErase(traw) == LT.Mismatch;
        assert CE.ProgErase(t).AnchorPass?;
        assert false;
      }
    }
    ThreadRepLkStepAnchor(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th,
                          ncap, nlook, nquant, a);
    assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm, th', ncap, nlook, nquant);
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == LT.AnchorPass(traw.a, CE.ProgErase(traw.t));
      assert CE.ProgErase(t) == LT.AnchorPass(t.a, CE.ProgErase(t.t));
    }
    assert (th.pc + 1) as nat == pc + 1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm)] + ta[1..])[0] == (t.t, gm) && ([(t.t, gm)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm)] + ta[1..], vms2.active,
                        ncap, nlook, nquant);

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  /** (L4 NESTED) clone of `LiftPreserveAnchorPassLk` — GmtTieInside dropped. */
  lemma LiftPreserveAnchorPassLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                       crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                       bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                       a: R.anchor, vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires !rer.multiline
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.AnchorAssertion(a))
    requires LAnc.is_satisfied(a, s.context, LAnc.Forward)
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [s.active[0].(pc := s.active[0].pc + 1)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    var th' := th.(pc := th.pc + 1);
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // the VM-side check IS the spec-side check
    assert PIV.ContextOkRE(str, s.cp, s.context);
    PSM.ContextOkIsCtxOf(str, s.cp as nat);
    assert LAnc.is_satisfied(a, TREP.CtxOf(inp), LAnc.Forward);
    TREP.AnchorAgreeInput(rer, a, inp);
    assert LS.AnchorSatisfied(rer, T.TrAnchor(a), inp);

    // canonical head: AnchorPass with canonical child at (pc+1, ea)
    TreeRepLkREAtAnchor(rer, qm, code, inp, t, pc, ea, a);
    assert t.AnchorPass? && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);

    // B step: pts_active queues the child with the same gm
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm)]);
    bst1 := PT.PTS(inp, [(t.t, gm)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // the child pairing: raw witness steps by the proven Anchor core; the
    // erasure tie transports to the canonical child
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    assert traw.AnchorPass? by {
      if !traw.AnchorPass? {
        var acts: LS.Actions, b: BS.LoopBool :|
          AR.ActionsRepL(rer, qm, acts, code, pc)
          && EL.PikeLkActions(acts)
          && ATR.EaOf(b) == ea
          && EL.BoolTreeLk(rer, acts, inp, b, traw)
          && GateAheadClear(acts, gm)
          && WalkDefsOk(acts);
        assert TtLk(rer, qm, code, inp, traw, pc, ea);
        TtLkAtAnchor(rer, qm, code, inp, traw, pc, ea, a);
        assert traw == LT.Mismatch;
        assert CE.ProgErase(traw) == LT.Mismatch;
        assert CE.ProgErase(t).AnchorPass?;
        assert false;
      }
    }
    ThreadRepLkStepAnchorNested(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th,
                                ncap, nlook, nquant, a);
    assert ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm, th', ncap, nlook, nquant);
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == LT.AnchorPass(traw.a, CE.ProgErase(traw.t));
      assert CE.ProgErase(t) == LT.AnchorPass(t.a, CE.ProgErase(t.t));
    }
    assert (th.pc + 1) as nat == pc + 1;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                              ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm)] + ta[1..])[0] == (t.t, gm) && ([(t.t, gm)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm)] + ta[1..], vms2.active,
                              ncap, nlook, nquant);

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  /** ANCHOR, KILLING: the head canonical tree is `Mismatch`
      (`tr_anchorfail` via `ContextOkRE` + `AnchorAgreeInput`), B drops it. */
  lemma LiftPreserveAnchorKillLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                 crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                 bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                 a: R.anchor, vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires !rer.multiline
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.AnchorAssertion(a))
    requires !LAnc.is_satisfied(a, s.context, LAnc.Forward)
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, ta[0].1, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, th.exit_allowed);

    // the VM-side check IS the spec-side check
    assert PIV.ContextOkRE(str, s.cp, s.context);
    PSM.ContextOkIsCtxOf(str, s.cp as nat);
    assert !LAnc.is_satisfied(a, TREP.CtxOf(inp), LAnc.Forward);
    TREP.AnchorAgreeInput(rer, a, inp);
    assert !LS.AnchorSatisfied(rer, T.TrAnchor(a), inp);

    TreeRepLkREAtAnchor(rer, qm, code, inp, t, pc, th.exit_allowed, a);
    assert t == LT.Mismatch;
    assert PTL.TreeBfsStepLk(t, ta[0].1, inp) == PT.StepActive([]);
    bst1 := LiftDropDeadHeadLk(rer, qm, re, code, endl, crv, str, ov, S,
                               bst, s, s1, vms2, ncap, nlook, nquant);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);
  }

  /** (L4 NESTED) clone of `LiftPreserveAnchorKillLk` — GmtTieInside dropped. */
  lemma LiftPreserveAnchorKillLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                       crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                       bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                       a: R.anchor, vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkNestedRE(qm, re, code, endl)
    requires !rer.multiline
    requires bst.PTS?
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.AnchorAssertion(a))
    requires !LAnc.is_satisfied(a, s.context, LAnc.Forward)
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, t, ta[0].1, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, th.exit_allowed);

    // the VM-side check IS the spec-side check
    assert PIV.ContextOkRE(str, s.cp, s.context);
    PSM.ContextOkIsCtxOf(str, s.cp as nat);
    assert !LAnc.is_satisfied(a, TREP.CtxOf(inp), LAnc.Forward);
    TREP.AnchorAgreeInput(rer, a, inp);
    assert !LS.AnchorSatisfied(rer, T.TrAnchor(a), inp);

    TreeRepLkREAtAnchor(rer, qm, code, inp, t, pc, th.exit_allowed, a);
    assert t == LT.Mismatch;
    assert PTL.TreeBfsStepLk(t, ta[0].1, inp) == PT.StepActive([]);
    bst1 := LiftDropDeadHeadLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                     bst, s, s1, vms2, ncap, nlook, nquant);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);
  }

  /** (4) The epsilon-phase lift — THE COMPOSITE DISPATCHER (restructured
      2026-08-07 to carry `ptsA`): mirrors `FAdvanceEpsilon`'s worklist
      recursion case-for-case, stepping machine A by the PROVEN
      `PSM.Preserve*Case` lemmas (inheriting `PikeInvFullRE`'s per-thread
      facts — `ThreadNestRE`, the backbones, `LooksCapUnset` — at EVERY
      intermediate state, which the SetReg/gate value cases consume) and
      machine B by the `LiftPreserve*Lk` case tier.
      `WriteOracle`/`CheckNullable`/`Fail` are refuted outright by the
      canonical tie (no `TreeRepLkRE` rule). */
  lemma LiftAdvanceEpsilon(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                           ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                           S: set<LG.GroupId>, ptsA: PT.PikeTreeState, s: AI.VmState,
                           bst: PT.PikeTreeState, dir: LAnc.direction,
                           ncap: int, nlook: int, nquant: int)
    returns (ptsA': PT.PikeTreeState, bst1: PT.PikeTreeState)
    requires !rer.multiline && !rer.ignoreCase && qm.ov == ov
    requires |ov| == |str| + 1                                    // L3b: propagate to the backward LB gate
    requires PSM.StaticOkRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires S == PIV.CapIdsInLooks(re)   // the value-tie boundary (SetReg/gate cases)
    requires GateStaticsOk(qm, re, crv, ncap, nlook, nquant)   // per-lid look-table package (gate-pass case)
    requires LTB.LookUnique(re)           // (E3) cross-lid ownership pinning
    requires LTB.LookTablesOk(re, crv)    // (E4) row↔structure tie (gate converse)
    requires dir == LAnc.Forward
    requires ptsA.PTS? && bst.PTS?
    requires |s.processed.true_set| == RB.size(code) && |s.processed.false_set| == RB.size(code)
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, s, ncap, nlook, nquant)
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    ensures PSM.TrcRE(ptsA, ptsA')
    ensures ptsA'.PTS?
    ensures PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA',
                              AI.FAdvanceEpsilon(code, s, ov, dir).0, ncap, nlook, nquant)
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?           // the ε-phase never finalizes; pts_final is LiftConsume's
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1,
                    AI.FAdvanceEpsilon(code, s, ov, dir).0, ncap, nlook, nquant)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 {
      ptsA' := ptsA;
      bst1 := bst;
      PSM.TrcRefl(ptsA);
      TrcLkRefl(bst);
      return;
    }
    var th := s.active[0];
    var ac := s.active[1..];

    // Head bounds from the canonical tie (machine A used ThreadNestRE here).
    var PTS(inp, ta, best, tb, seen) := bst;
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0 && th.pc >= 0;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[0].0, ta[0].1, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    assert TreeRepLkRE(rer, qm, code, inp, ta[0].0, pc, th.exit_allowed);
    TreeRepLkREInRange(rer, qm, code, inp, ta[0].0, pc, th.exit_allowed);
    assert pc < |code| && RB.size(code) == |code|;
    var i := RB.get_instr(code, th.pc);
    assert i == code[pc] && NR.GetPcRE(code, pc) == Some(i);

    if AI.bpc_mem(s.processed, th.pc, th.exit_allowed) {
      var bstS := LiftPreserveSkipLk(rer, qm, re, code, endl, crv, str, ov, S, bst, s, ncap, nlook, nquant);
      var ptsS := PSM.PreserveSkipCase(rer, qm, re, code, endl, ngroups, str, ptsA, s, ncap, nlook, nquant);
      var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                            ptsS, s.(active := ac), bstS, dir, ncap, nlook, nquant);
      PSM.TrcCons(ptsA, ptsS, ptsA2);
      TrcLkCons(bst, bstS, bst2);
      ptsA' := ptsA2;
      bst1 := bst2;
      return;
    }

    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(s.processed, th.pc, th.exit_allowed));
    assert AI.unprocessed(s1.processed) <= AI.unprocessed(s.processed)
           && (0 <= th.pc < RB.size(code) ==> AI.unprocessed(s1.processed) < AI.unprocessed(s.processed))
    by { AI.UnprocessedAdd(s.processed, th.pc, th.exit_allowed); }
    assert AI.unprocessed(s1.processed) < AI.unprocessed(s.processed);
    assert |s1.processed.true_set| == RB.size(code) && |s1.processed.false_set| == RB.size(code);

    match i {
      case Accept =>
        var vms2 := s1.(active := [], bestmatch := Some(th));
        bst1 := LiftPreserveAcceptLk(rer, qm, re, code, endl, crv, str, ov, S,
                                     bst, s, s1, vms2, ncap, nlook, nquant);
        ptsA' := PSM.PreserveAcceptCase(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                        s1, vms2, ncap, nlook, nquant);
        PSM.TrcRefl(ptsA');
        PSM.TrcCons(ptsA, ptsA', ptsA');
        TrcLkRefl(bst1);
        TrcLkCons(bst, bst1, bst1);
        assert AI.FAdvanceEpsilon(code, s, ov, dir).0 == vms2;
      case Jmp(x) =>
        var th' := th.(pc := x);
        var vms2 := s1.(active := [th'] + ac);
        LiftPreserveStutterLk(rer, qm, re, code, endl, crv, str, ov, S,
                              bst, s, s1, th', vms2, ncap, nlook, nquant);
        PSM.PreserveStutterCase(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                s1, th', vms2, ncap, nlook, nquant);
        var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                              ptsA, vms2, bst, dir, ncap, nlook, nquant);
        ptsA' := ptsA2;
        bst1 := bst2;
      case BeginLoop =>
        var th' := th.(exit_allowed := false, pc := th.pc + 1);
        var vms2 := s1.(active := [th'] + ac);
        LiftPreserveStutterLk(rer, qm, re, code, endl, crv, str, ov, S,
                              bst, s, s1, th', vms2, ncap, nlook, nquant);
        PSM.PreserveStutterCase(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                s1, th', vms2, ncap, nlook, nquant);
        var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                              ptsA, vms2, bst, dir, ncap, nlook, nquant);
        ptsA' := ptsA2;
        bst1 := bst2;
      case Consume(ce) =>
        var (nb, ni) := AI.add_thread(th, ce, s1.blocked, s1.isblocked);
        if AI.pc_mem(s1.isblocked, th.pc) {
          assert nb == s1.blocked && ni == s1.isblocked;
          var vms2 := s1.(blocked := nb, isblocked := ni, active := ac);
          assert vms2 == s1.(active := ac);
          var bstS := LiftPreserveConsumeDropLk(rer, qm, re, code, endl, crv, str, ov, S,
                                                bst, s, s1, ce, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveConsumeDrop(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                              s1, ce, vms2, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        } else {
          assert nb == [(th, ce)] + s1.blocked && ni == AI.pc_add(s1.isblocked, th.pc);
          var vms2 := s1.(blocked := nb, isblocked := ni, active := ac);
          var bstS := LiftPreserveConsumeAddLk(rer, qm, re, code, endl, crv, str, ov, S,
                                               bst, s, s1, ce, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveConsumeAdd(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                             s1, ce, vms2, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        }
      case Fork(x, y) =>
        var newt := AI.Thread(x, th.capture_regs, th.look_regs, th.quant_regs, th.exit_allowed);
        var vms2 := s1.(active := [newt, th.(pc := y)] + ac);
        // backward-fork flag pin: a false-thread never sits at a Cold pc
        assert (x <= th.pc || y <= th.pc) ==> th.exit_allowed by {
          if (x <= th.pc || y <= th.pc) && !th.exit_allowed {
            assert th in s.active && PSM.EaColdOkRE(code, th);
            assert NI.ColdF(code, pc, 1);
            assert NI.ColdRE(code, pc);
          }
        }
        var bstS := LiftPreserveForkLk(rer, qm, re, code, endl, crv, str, ov, S,
                                       bst, s, s1, x, y, vms2, ncap, nlook, nquant);
        var ptsS := PSM.PreserveForkCase(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                         s1, x, y, vms2, ncap, nlook, nquant);
        var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                              ptsS, vms2, bstS, dir, ncap, nlook, nquant);
        PSM.TrcTrans(ptsA, ptsS, ptsA2);
        TrcLkTrans(bst, bstS, bst2);
        ptsA' := ptsA2;
        bst1 := bst2;
      case SetRegisterToCP(reg) =>
        var th' := th.(capture_regs := AReg.set_reg(th.capture_regs, reg, Some(s1.cp), s1.clock),
        pc := th.pc + 1);
        var vms2 := s1.(active := [th'] + ac);
        // A-side gm effect off ptsA's head (helper keeps the dispatcher VC small)
        DispatchSetRegEffect(rer, qm, re, code, endl, ngroups, str, ptsA, s, s1, reg, th',
                             ncap, nlook, nquant);
        assert th in s.active;
        assert CM.ThreadClocksLE(th, s.clock) && s.clock >= 0;   // PikeInvFullRE backbone
        var bstS := LiftPreserveSetRegLk(rer, qm, re, code, endl, crv, str, ov, S,
                                         bst, s, s1, reg, th', vms2, ncap, nlook, nquant);
        var ptsS: PT.PikeTreeState;
        if reg % 2 == 0 {
          ptsS := PSM.PreserveOpenCase(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                       s1, reg, vms2, ncap, nlook, nquant);
        } else {
          ptsS := PSM.PreserveCloseCase(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                        s1, reg, vms2, ncap, nlook, nquant);
        }
        var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                              ptsS, vms2, bstS, dir, ncap, nlook, nquant);
        PSM.TrcCons(ptsA, ptsS, ptsA2);
        TrcLkTrans(bst, bstS, bst2);
        ptsA' := ptsA2;
        bst1 := bst2;
      case SetQuantToClock(q, bq) =>
        var ocp := if bq then Some(s1.cp) else None;
        var th' := th.(quant_regs := AReg.set_reg(th.quant_regs, q, ocp, s1.clock), pc := th.pc + 1);
        var vms2 := s1.(active := [th'] + ac);
        // the canonical tie pins bq == false (compiled SQC sites write false);
        // then the A-side helper yields the GMReset gm effect.
        TreeRepLkREAtSetQuant(rer, qm, code, inp, ta[0].0, pc, th.exit_allowed, q, bq);
        assert !bq && q in qm.quants by { NoTrueStampsFromStaticRE(qm, re, code, endl); }   // §2.5b: the gated tiers stay stamp-free
        assert th in s.active;
        assert CM.ThreadRegsWf(th, ncap, nlook, nquant);   // PikeInvFullRE backbone
        assert CM.ThreadClocksLE(th, s.clock) && s.clock >= 0;
        DispatchResetEffect(rer, qm, re, code, endl, ngroups, str, ptsA, s, s1, q, th',
                            ncap, nlook, nquant);
        var bstS := LiftPreserveSetQuantLk(rer, qm, re, code, endl, crv, str, ov, S,
                                           bst, s, s1, q, bq, th', vms2, ncap, nlook, nquant);
        var ptsS := PSM.PreserveResetCase(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                          s1, q, bq, vms2, ncap, nlook, nquant);
        var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                              ptsS, vms2, bstS, dir, ncap, nlook, nquant);
        PSM.TrcCons(ptsA, ptsS, ptsA2);
        TrcLkTrans(bst, bstS, bst2);
        ptsA' := ptsA2;
        bst1 := bst2;
      case CheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var th' := th.(pc := th.pc + 1,
          look_regs := AReg.set_reg(th.look_regs, l, Some(s1.cp), s1.clock));
          var vms2 := s1.(active := [th'] + ac);
          assert th in s.active;
          assert CM.ThreadRegsWf(th, ncap, nlook, nquant);   // PikeInvFullRE backbone
          assert CM.ThreadClocksLE(th, s.clock) && s.clock >= 0;
          assert PSM.ThreadNestRE(re, code, endl, th.pc, th);
          var bstS := LiftPreserveGatePassLk(rer, qm, re, code, endl, crv, str, ov, S,
                                             bst, s, s1, l, th', vms2, ncap, nlook, nquant);
          PSM.PreserveOraclePass(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                 s1, th', vms2, l, true, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                ptsA, vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveGateKillLk(rer, qm, re, code, endl, crv, str, ov, S,
                                             bst, s, s1, l, true, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveOracleKill(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                             s1, vms2, l, true, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        }
      case NegCheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveGateKillLk(rer, qm, re, code, endl, crv, str, ov, S,
                                             bst, s, s1, l, false, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveOracleKill(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                             s1, vms2, l, false, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := [th.(pc := th.pc + 1)] + ac);
          var bstS := LiftPreserveNegGatePassLk(rer, qm, re, code, endl, crv, str, ov, S,
                                                bst, s, s1, l, vms2, ncap, nlook, nquant);
          PSM.PreserveOraclePass(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                 s1, th.(pc := th.pc + 1), vms2, l, false, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                ptsA, vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        }
      case WriteOracle(l) =>
        // no TreeRepLkRE rule at WriteOracle — the canonical head tie is refuted
        assert false;
        ptsA' := ptsA;
        bst1 := bst;
      case EndLoop =>
        if th.exit_allowed {
          var vms2 := s1.(active := [th.(pc := th.pc + 1)] + ac);
          var bstS := LiftPreserveEndLoopPassLk(rer, qm, re, code, endl, crv, str, ov, S,
                                                bst, s, s1, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveEndLoopPass(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                              s1, vms2, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveEndLoopKillLk(rer, qm, re, code, endl, crv, str, ov, S,
                                                bst, s, s1, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveEndLoopKill(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                              s1, vms2, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        }
      case CheckNullable(qid) =>
        // no TreeRepLkRE rule at CheckNullable — refuted
        assert false;
        ptsA' := ptsA;
        bst1 := bst;
      case AnchorAssertion(a) =>
        if LAnc.is_satisfied(a, s1.context, dir) {
          var vms2 := s1.(active := [th.(pc := th.pc + 1)] + ac);
          var bstS := LiftPreserveAnchorPassLk(rer, qm, re, code, endl, crv, str, ov, S,
                                               bst, s, s1, a, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveAnchorPass(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                             s1, vms2, a, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveAnchorKillLk(rer, qm, re, code, endl, crv, str, ov, S,
                                               bst, s, s1, a, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveAnchorKill(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                             s1, vms2, a, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        }
      case Fail =>
        // no TreeRepLkRE rule at Fail — refuted
        assert false;
        ptsA' := ptsA;
        bst1 := bst;
    }
  }

  /** (L4 NESTED) clone of `LiftAdvanceEpsilon` — GmtTieInside dropped. */
  lemma {:isolate_assertions} LiftAdvanceEpsilonNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                 ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                 S: set<LG.GroupId>, ptsA: PT.PikeTreeState, s: AI.VmState,
                                 bst: PT.PikeTreeState, dir: LAnc.direction,
                                 ncap: int, nlook: int, nquant: int)
    returns (ptsA': PT.PikeTreeState, bst1: PT.PikeTreeState)
    requires !rer.multiline && !rer.ignoreCase && qm.ov == ov
    requires |ov| == |str| + 1                                    // L3b: propagate to the backward LB gate
    requires PSM.StaticOkNestedRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires S == PIV.CapIdsInLooks(re)   // the value-tie boundary (SetReg/gate cases)
    requires GateStaticsOk(qm, re, crv, ncap, nlook, nquant)   // per-lid look-table package (gate-pass case)
    requires LTB.LookUnique(re)           // (E3) cross-lid ownership pinning
    requires LTB.LookTablesOk(re, crv)    // (E4) row↔structure tie (gate converse)
    requires dir == LAnc.Forward
    requires ptsA.PTS? && bst.PTS?
    requires |s.processed.true_set| == RB.size(code) && |s.processed.false_set| == RB.size(code)
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, s, ncap, nlook, nquant)
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    ensures PSM.TrcRE(ptsA, ptsA')
    ensures ptsA'.PTS?
    ensures PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA',
                              AI.FAdvanceEpsilon(code, s, ov, dir).0, ncap, nlook, nquant)
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?           // the ε-phase never finalizes; pts_final is LiftConsume's
    ensures LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1,
                          AI.FAdvanceEpsilon(code, s, ov, dir).0, ncap, nlook, nquant)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    // (§2.5b/z3 4.14) recursive nullability predicates + the CIN disjunct's
    // triggered existential storm the solver; all uses here are opaque.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    if |s.active| == 0 {
      ptsA' := ptsA;
      bst1 := bst;
      PSM.TrcRefl(ptsA);
      TrcLkRefl(bst);
      return;
    }
    var th := s.active[0];
    var ac := s.active[1..];

    // Head bounds from the canonical tie (machine A used ThreadNestRE here).
    var PTS(inp, ta, best, tb, seen) := bst;
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0 && th.pc >= 0;
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, ta[0].0, ta[0].1, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    assert TreeRepLkRE(rer, qm, code, inp, ta[0].0, pc, th.exit_allowed);
    TreeRepLkREInRange(rer, qm, code, inp, ta[0].0, pc, th.exit_allowed);
    assert pc < |code| && RB.size(code) == |code|;
    var i := RB.get_instr(code, th.pc);
    assert i == code[pc] && NR.GetPcRE(code, pc) == Some(i);

    if AI.bpc_mem(s.processed, th.pc, th.exit_allowed) {
      var bstS := LiftPreserveSkipLkNested(rer, qm, re, code, endl, crv, str, ov, S, bst, s, ncap, nlook, nquant);
      var ptsS := PSM.PreserveSkipCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s, ncap, nlook, nquant);
      var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                  ptsS, s.(active := ac), bstS, dir, ncap, nlook, nquant);
      PSM.TrcCons(ptsA, ptsS, ptsA2);
      TrcLkCons(bst, bstS, bst2);
      ptsA' := ptsA2;
      bst1 := bst2;
      return;
    }

    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(s.processed, th.pc, th.exit_allowed));
    assert AI.unprocessed(s1.processed) <= AI.unprocessed(s.processed)
           && (0 <= th.pc < RB.size(code) ==> AI.unprocessed(s1.processed) < AI.unprocessed(s.processed))
    by { AI.UnprocessedAdd(s.processed, th.pc, th.exit_allowed); }
    assert AI.unprocessed(s1.processed) < AI.unprocessed(s.processed);
    assert |s1.processed.true_set| == RB.size(code) && |s1.processed.false_set| == RB.size(code);

    match i {
      case Accept =>
        var vms2 := s1.(active := [], bestmatch := Some(th));
        bst1 := LiftPreserveAcceptLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                           bst, s, s1, vms2, ncap, nlook, nquant);
        ptsA' := PSM.PreserveAcceptCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                              s1, vms2, ncap, nlook, nquant);
        PSM.TrcRefl(ptsA');
        PSM.TrcCons(ptsA, ptsA', ptsA');
        TrcLkRefl(bst1);
        TrcLkCons(bst, bst1, bst1);
        assert AI.FAdvanceEpsilon(code, s, ov, dir).0 == vms2;
      case Jmp(x) =>
        var th' := th.(pc := x);
        var vms2 := s1.(active := [th'] + ac);
        LiftPreserveStutterLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                    bst, s, s1, th', vms2, ncap, nlook, nquant);
        PSM.PreserveStutterCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                      s1, th', vms2, ncap, nlook, nquant);
        var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                    ptsA, vms2, bst, dir, ncap, nlook, nquant);
        ptsA' := ptsA2;
        bst1 := bst2;
      case BeginLoop =>
        var th' := th.(exit_allowed := false, pc := th.pc + 1);
        var vms2 := s1.(active := [th'] + ac);
        LiftPreserveStutterLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                    bst, s, s1, th', vms2, ncap, nlook, nquant);
        PSM.PreserveStutterCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                      s1, th', vms2, ncap, nlook, nquant);
        var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                    ptsA, vms2, bst, dir, ncap, nlook, nquant);
        ptsA' := ptsA2;
        bst1 := bst2;
      case Consume(ce) =>
        var (nb, ni) := AI.add_thread(th, ce, s1.blocked, s1.isblocked);
        if AI.pc_mem(s1.isblocked, th.pc) {
          assert nb == s1.blocked && ni == s1.isblocked;
          var vms2 := s1.(blocked := nb, isblocked := ni, active := ac);
          assert vms2 == s1.(active := ac);
          var bstS := LiftPreserveConsumeDropLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                                      bst, s, s1, ce, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveConsumeDropNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                    s1, ce, vms2, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                      ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        } else {
          assert nb == [(th, ce)] + s1.blocked && ni == AI.pc_add(s1.isblocked, th.pc);
          var vms2 := s1.(blocked := nb, isblocked := ni, active := ac);
          var bstS := LiftPreserveConsumeAddLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                                     bst, s, s1, ce, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveConsumeAddNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                   s1, ce, vms2, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                      ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        }
      case Fork(x, y) =>
        var newt := AI.Thread(x, th.capture_regs, th.look_regs, th.quant_regs, th.exit_allowed);
        var vms2 := s1.(active := [newt, th.(pc := y)] + ac);
        // backward-fork flag pin: a false-thread never sits at a Cold pc
        assert (x <= th.pc || y <= th.pc) ==> th.exit_allowed by {
          if (x <= th.pc || y <= th.pc) && !th.exit_allowed {
            assert th in s.active && PSM.EaColdOkRE(code, th);
            assert NI.ColdF(code, pc, 1);
            assert NI.ColdRE(code, pc);
          }
        }
        var bstS := LiftPreserveForkLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                             bst, s, s1, x, y, vms2, ncap, nlook, nquant);
        var ptsS := PSM.PreserveForkCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                               s1, x, y, vms2, ncap, nlook, nquant);
        var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                    ptsS, vms2, bstS, dir, ncap, nlook, nquant);
        PSM.TrcTrans(ptsA, ptsS, ptsA2);
        TrcLkTrans(bst, bstS, bst2);
        ptsA' := ptsA2;
        bst1 := bst2;
      case SetRegisterToCP(reg) =>
        var th' := th.(capture_regs := AReg.set_reg(th.capture_regs, reg, Some(s1.cp), s1.clock),
        pc := th.pc + 1);
        var vms2 := s1.(active := [th'] + ac);
        // A-side gm effect off ptsA's head (helper keeps the dispatcher VC small)
        DispatchSetRegEffectNested(rer, qm, re, code, endl, ngroups, str, ptsA, s, s1, reg, th',
                                   ncap, nlook, nquant);
        assert th in s.active;
        assert CM.ThreadClocksLE(th, s.clock) && s.clock >= 0;   // PikeInvFullRE backbone
        var bstS := LiftPreserveSetRegLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                               bst, s, s1, reg, th', vms2, ncap, nlook, nquant);
        var ptsS: PT.PikeTreeState;
        if reg % 2 == 0 {
          ptsS := PSM.PreserveOpenCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                             s1, reg, vms2, ncap, nlook, nquant);
        } else {
          ptsS := PSM.PreserveCloseCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                              s1, reg, vms2, ncap, nlook, nquant);
        }
        var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                    ptsS, vms2, bstS, dir, ncap, nlook, nquant);
        PSM.TrcCons(ptsA, ptsS, ptsA2);
        TrcLkTrans(bst, bstS, bst2);
        ptsA' := ptsA2;
        bst1 := bst2;
      case SetQuantToClock(q, bq) =>
        var ocp := if bq then Some(s1.cp) else None;
        var th' := th.(quant_regs := AReg.set_reg(th.quant_regs, q, ocp, s1.clock), pc := th.pc + 1);
        var vms2 := s1.(active := [th'] + ac);
        // the canonical tie pins bq == false (compiled SQC sites write false);
        // then the A-side helper yields the GMReset gm effect.
        TreeRepLkREAtSetQuant(rer, qm, code, inp, ta[0].0, pc, th.exit_allowed, q, bq);
        assert !bq && q in qm.quants by { NoTrueStampsFromStaticNestedRE(qm, re, code, endl); }   // §2.5b: the gated tiers stay stamp-free
        assert th in s.active;
        assert CM.ThreadRegsWf(th, ncap, nlook, nquant);   // PikeInvFullRE backbone
        assert CM.ThreadClocksLE(th, s.clock) && s.clock >= 0;
        DispatchResetEffectNested(rer, qm, re, code, endl, ngroups, str, ptsA, s, s1, q, th',
                                  ncap, nlook, nquant);
        var bstS := LiftPreserveSetQuantLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                                 bst, s, s1, q, bq, th', vms2, ncap, nlook, nquant);
        var ptsS := PSM.PreserveResetCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                s1, q, bq, vms2, ncap, nlook, nquant);
        var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                    ptsS, vms2, bstS, dir, ncap, nlook, nquant);
        PSM.TrcCons(ptsA, ptsS, ptsA2);
        TrcLkTrans(bst, bstS, bst2);
        ptsA' := ptsA2;
        bst1 := bst2;
      case CheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var th' := th.(pc := th.pc + 1,
          look_regs := AReg.set_reg(th.look_regs, l, Some(s1.cp), s1.clock));
          var vms2 := s1.(active := [th'] + ac);
          assert th in s.active;
          assert CM.ThreadRegsWf(th, ncap, nlook, nquant);   // PikeInvFullRE backbone
          assert CM.ThreadClocksLE(th, s.clock) && s.clock >= 0;
          assert PSM.ThreadNestRE(re, code, endl, th.pc, th);
          // the callee's narrowed positional feed (the nesting conjunct alone)
          assert NI.NestTopRE(re, code, endl, th.pc as nat, th.capture_regs.a_clk, th.quant_regs.a_clk);
          var bstS := LiftPreserveGatePassLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                                   bst, s, s1, l, th', vms2, ncap, nlook, nquant);
          PSM.PreserveOraclePassNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                       s1, th', vms2, l, true, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                      ptsA, vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveGateKillLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                                   bst, s, s1, l, true, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveOracleKillNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                   s1, vms2, l, true, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                      ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        }
      case NegCheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveGateKillLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                                   bst, s, s1, l, false, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveOracleKillNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                   s1, vms2, l, false, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                      ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := [th.(pc := th.pc + 1)] + ac);
          var bstS := LiftPreserveNegGatePassLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                                      bst, s, s1, l, vms2, ncap, nlook, nquant);
          PSM.PreserveOraclePassNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                       s1, th.(pc := th.pc + 1), vms2, l, false, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                      ptsA, vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        }
      case WriteOracle(l) =>
        // no TreeRepLkRE rule at WriteOracle — the canonical head tie is refuted
        assert false;
        ptsA' := ptsA;
        bst1 := bst;
      case EndLoop =>
        if th.exit_allowed {
          var vms2 := s1.(active := [th.(pc := th.pc + 1)] + ac);
          var bstS := LiftPreserveEndLoopPassLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                                      bst, s, s1, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveEndLoopPassNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                    s1, vms2, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                      ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveEndLoopKillLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                                      bst, s, s1, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveEndLoopKillNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                    s1, vms2, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                      ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        }
      case CheckNullable(qid) =>
        // no TreeRepLkRE rule at CheckNullable — refuted
        assert false;
        ptsA' := ptsA;
        bst1 := bst;
      case AnchorAssertion(a) =>
        if LAnc.is_satisfied(a, s1.context, dir) {
          var vms2 := s1.(active := [th.(pc := th.pc + 1)] + ac);
          var bstS := LiftPreserveAnchorPassLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                                     bst, s, s1, a, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveAnchorPassNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                   s1, vms2, a, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                      ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveAnchorKillLkNested(rer, qm, re, code, endl, crv, str, ov, S,
                                                     bst, s, s1, a, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveAnchorKillNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                   s1, vms2, a, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                      ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        }
      case Fail =>
        // no TreeRepLkRE rule at Fail — refuted
        assert false;
        ptsA' := ptsA;
        bst1 := bst;
    }
  }

  /** THE COMPOSITE INVARIANT: machine-A sim (VM↔tstar, PROVEN) PLUS the
      machine-A↔machine-B tree pairing + value payload. `ptsA` is the tstar
      (gate-transparent) PikeTree state driven by `PikeInvFullRE`; `ptsB` is the
      `tcan` (LK-aware, planted-canonical) PikeTree state driven by
      `PTL.PikeTreeStepLk`. */
  ghost predicate LiftInvC(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                           endl: nat, ngroups: nat, crv: CP.FCompiled, str: string,
                           ov: LOr.OracleView, S: set<LG.GroupId>,
                           ptsA: PT.PikeTreeState, ptsB: PT.PikeTreeState, vms: AI.VmState,
                           ncap: int, nlook: int, nquant: int)
    requires NR.NfaRepRE(re, code, 0, endl)
  {
    PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, vms, ncap, nlook, nquant)
    // THREAD-ANCHORED pairing (audit 2026-08-03): each ptsB tree pairs with
    // the VM thread via ThreadRepLkC (canonical tie + raw erasure witness),
    // NOT with the tstar tree — so no ta↔tb link is needed (that was the
    // dead §K route). ptsA is carried only for PikeInvFullRE's VM backbone;
    // the whole B side IS the (canonical-keyed) standalone `LiftInv`.
    && (ptsB.PTS? ==> ptsA.PTS? && ptsA.inp == ptsB.inp)
    && LiftInv(rer, qm, re, code, crv, str, ov, S, ptsB, vms, ncap, nlook, nquant)
  }

  /** (L4 NESTED) The composite invariant carrying the `GmtTieInside`-free
      standalone `LiftInvNested`. The machine-A backbone (`PikeInvFullRE`) and
      the ptsA↔ptsB `inp` link are depth-agnostic and kept verbatim. */
  ghost predicate LiftInvCNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                 endl: nat, ngroups: nat, crv: CP.FCompiled, str: string,
                                 ov: LOr.OracleView, S: set<LG.GroupId>,
                                 ptsA: PT.PikeTreeState, ptsB: PT.PikeTreeState, vms: AI.VmState,
                                 ncap: int, nlook: int, nquant: int)
    requires NR.NfaRepRE(re, code, 0, endl)
  {
    PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, vms, ncap, nlook, nquant)
    && (ptsB.PTS? ==> ptsA.PTS? && ptsA.inp == ptsB.inp)
    && LiftInvNested(rer, qm, re, code, crv, str, ov, S, ptsB, vms, ncap, nlook, nquant)
  }

  /** (K-init) The composite holds at the start: `PSM.InitialPikeInvFullRE` gives
      the machine-A half; machine B starts on the PLANTED CANONICAL tree `tcan`
      (constructed here by `ActionsTreeRepLkRE` from the entry walk, with
      `WkE.WalkOkEntry` supplying the walk carrier), erasure-tied to the spec
      walk tree `t` — the endpoint glue is `FirstLeaf(tcan) == FirstLeaf(t)`
      via `ProgEraseLeavesEq`. The single active pair `(tcan, init_thread)`
      ties via `ThreadRepLkC` with raw witness `t` + a VACUOUS payload
      (init thread's live map is `LG.Empty`, no `g in S`). */
  lemma LiftInitC(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                  endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                  S: set<LG.GroupId>, tstar: LT.Tree, t: LT.Tree, inp: LC.Input, vms: AI.VmState,
                  ncap: int, nlook: int, nquant: int)
    returns (tcan: LT.Tree)
    requires AR.NoTrueStamps(code)   // §2.5b stage 2a: look-body code is stamp-free
    requires NR.NfaRepRE(re, code, 0, endl)
    requires code == CP.compile_to_bytecode(re)               // WalkOkEntry's carrier
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str,
                               PT.PikeTreeInitialState(tstar, inp), vms, ncap, nlook, nquant)
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re) && PIV.CapUnique(re)
    requires NR.NoNulledPlusRE(re)   // §2.5b interim: all stamps false
    requires AR.ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
    requires EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t)
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires inp == PIV.InpOfCp(str, vms.cp) && 0 <= vms.cp <= |str|
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.bestmatch.None?
    requires vms.blocked == []                                // genuine start: nothing blocked yet
    requires vms.processed == AI.init_bpcset(RB.size(code))   // genuine start: nothing processed yet
    requires vms.isblocked == AI.init_pcset(RB.size(code))
    requires PIV.ContextOkRE(str, vms.cp, vms.context)
    ensures TreeRepLkRE(rer, qm, code, inp, tcan, 0, false)
    ensures CE.ProgErase(tcan) == CE.ProgErase(t)             // endpoint glue: FirstLeaf(tcan) == FirstLeaf(t)
    ensures LiftInvC(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                     PT.PikeTreeInitialState(tstar, inp), PT.PikeTreeInitialState(tcan, inp), vms,
                     ncap, nlook, nquant)
  {
    // The single active pair (t, init_thread) ties via ThreadRepLk (THREAD-
    // anchored — no tstar↔t tree link); the payload is vacuous because a fresh
    // thread denotes Empty. PikeInvFullRE(ptsA, vms) is the hypothesis.
    PIV.GmOfLiveInit(re, ncap, nlook, nquant);        // GmOfLive(re, init...) == Empty
    var it := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
    var acts := [LS.Areg(T.Translate(re))];
    assert it.pc == 0 && it.exit_allowed == false;
    assert it.capture_regs == AReg.init_regs(ncap)
           && it.look_regs == AReg.init_regs(nlook) && it.quant_regs == AReg.init_regs(nquant);
    EL.TranslateFragmentPikeLk(re);                     // PikeLkRegex(Translate(re))
    EL.PikeLkActionsConsIff(LS.Areg(T.Translate(re)), []);
    assert EL.PikeLkActions(acts);
    assert GateAheadClear(acts, LG.Empty);              // Empty has no keys
    TranslateDefGroupsNoDup(re);                        // NoDupSeq(DefGroups(Translate(re)))
    WalkDefsOkEntry(T.Translate(re));
    M.AllDefsActsCons(LS.Areg(T.Translate(re)), []);
    assert M.AllDefsActs(acts) == L.DefGroups(T.Translate(re));   // AllDefsActs([]) == []
    assert WalkPairLk(rer, qm, code, inp, t, LG.Empty, it.pc as nat, it.exit_allowed) by {
      assert it.pc as nat == 0;
      assert AR.ActionsRepL(rer, qm, acts, code, 0);
      assert ATR.EaOf(BS.CannotExit) == it.exit_allowed;   // both false
      assert EL.BoolTreeLk(rer, acts, inp, BS.CannotExit, t);
      assert exists actsw: LS.Actions, bw: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, actsw, code, it.pc as nat)
          && EL.PikeLkActions(actsw)
          && ATR.EaOf(bw) == it.exit_allowed
          && EL.BoolTreeLk(rer, actsw, inp, bw, t)
          && GateAheadClear(actsw, LG.Empty)
          && WalkDefsOk(actsw);
    }
    assert GmtTieOutside(re, it, LG.Empty, S);          // gml == Empty, agrees with Empty
    assert GmtTieInside(crv, str, ov, it, LG.Empty, S, ncap, nlook, nquant);  // no g in Empty
    assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, t, LG.Empty, it, ncap, nlook, nquant);
    // Construct machine B's PLANTED CANONICAL entry tree; the raw walk tree
    // `t` is its value-layer erasure witness.
    WkE.WalkOkEntry(re);
    assert WO.WalkOk(acts, code, 0, false);
    assert ATR.EaOf(BS.CannotExit) == false;
    tcan := ActionsTreeRepLkRE(rer, qm, acts, code, 0, inp, BS.CannotExit, t);
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, tcan, LG.Empty, it,
                        ncap, nlook, nquant) by {
      assert TreeRepLkRE(rer, qm, code, inp, tcan, it.pc as nat, it.exit_allowed);
      assert CE.ProgErase(t) == CE.ProgErase(tcan)
             && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, t, LG.Empty, it, ncap, nlook, nquant);
    }
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, [(tcan, LG.Empty)], [it], ncap, nlook, nquant);
    // ptsB = PTS(inp, [(tcan, Empty)], None, [], InitialSeenTrees); best None both sides.
    assert PT.PikeTreeInitialState(tcan, inp) == PT.PTS(inp, [(tcan, LG.Empty)], None, [], SS.InitialSeenTrees);
    assert PT.PikeTreeInitialState(tstar, inp).PTS? && PT.PikeTreeInitialState(tstar, inp).inp == inp;
    assert BestTieLk(re, crv, str, ov, S, None, vms.bestmatch, ncap, nlook, nquant);
    // Blocked: genuine start — both sides empty.
    assert PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp) == [];
    forall nextinp | LC.AdvanceInput(inp, WP.Forward) == Some(nextinp)
      ensures BlockedRepLkC(rer, qm, re, code, inp, nextinp, crv, str, ov, S, [],
                            PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant)
    { }
    // B-side seen ↔ processed: at the genuine start nothing is processed, so
    // `SeenRepLk` holds vacuously (mirror of `PIV.InitialInclusionRE`).
    InitialSeenRepLk(rer, qm, code, inp,
                     PIV.HdTreeOf([(tcan, LG.Empty)]), PIV.HeadPcOf([it]), RB.size(code));
  }

  /** (L4 NESTED) clone of `LiftInitC` — GmtTieInside dropped. */
  lemma {:isolate_assertions} LiftInitCNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                        endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                        S: set<LG.GroupId>, tstar: LT.Tree, t: LT.Tree, inp: LC.Input, vms: AI.VmState,
                        ncap: int, nlook: int, nquant: int)
    returns (tcan: LT.Tree)
    requires AR.NoTrueStamps(code)   // §2.5b stage 2a: look-body code is stamp-free
    requires NR.NfaRepRE(re, code, 0, endl)
    requires code == CP.compile_to_bytecode(re)               // WalkOkEntry's carrier
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str,
                               PT.PikeTreeInitialState(tstar, inp), vms, ncap, nlook, nquant)
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re) && PIV.CapUnique(re)
    requires NR.NoNulledPlusRE(re)   // §2.5b interim: all stamps false
    requires AR.ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
    requires EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t)
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires inp == PIV.InpOfCp(str, vms.cp) && 0 <= vms.cp <= |str|
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.bestmatch.None?
    requires vms.blocked == []                                // genuine start: nothing blocked yet
    requires vms.processed == AI.init_bpcset(RB.size(code))   // genuine start: nothing processed yet
    requires vms.isblocked == AI.init_pcset(RB.size(code))
    requires PIV.ContextOkRE(str, vms.cp, vms.context)
    ensures TreeRepLkRE(rer, qm, code, inp, tcan, 0, false)
    ensures CE.ProgErase(tcan) == CE.ProgErase(t)             // endpoint glue: FirstLeaf(tcan) == FirstLeaf(t)
    ensures LiftInvCNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                           PT.PikeTreeInitialState(tstar, inp), PT.PikeTreeInitialState(tcan, inp), vms,
                           ncap, nlook, nquant)
  {
    // (§2.5b/z3 4.14) recursive nullability predicates + the CIN disjunct's
    // triggered existential storm the solver; all uses here are opaque.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    // The single active pair (t, init_thread) ties via ThreadRepLk (THREAD-
    // anchored — no tstar↔t tree link); the payload is vacuous because a fresh
    // thread denotes Empty. PikeInvFullRE(ptsA, vms) is the hypothesis.
    PIV.GmOfLiveInit(re, ncap, nlook, nquant);        // GmOfLive(re, init...) == Empty
    var it := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
    var acts := [LS.Areg(T.Translate(re))];
    assert it.pc == 0 && it.exit_allowed == false;
    assert it.capture_regs == AReg.init_regs(ncap)
           && it.look_regs == AReg.init_regs(nlook) && it.quant_regs == AReg.init_regs(nquant);
    EL.TranslateFragmentPikeLk(re);                     // PikeLkRegex(Translate(re))
    EL.PikeLkActionsConsIff(LS.Areg(T.Translate(re)), []);
    assert EL.PikeLkActions(acts);
    assert GateAheadClear(acts, LG.Empty);              // Empty has no keys
    TranslateDefGroupsNoDup(re);                        // NoDupSeq(DefGroups(Translate(re)))
    WalkDefsOkEntry(T.Translate(re));
    M.AllDefsActsCons(LS.Areg(T.Translate(re)), []);
    assert M.AllDefsActs(acts) == L.DefGroups(T.Translate(re));   // AllDefsActs([]) == []
    assert WalkPairLk(rer, qm, code, inp, t, LG.Empty, it.pc as nat, it.exit_allowed) by {
      assert it.pc as nat == 0;
      assert AR.ActionsRepL(rer, qm, acts, code, 0);
      assert ATR.EaOf(BS.CannotExit) == it.exit_allowed;   // both false
      assert EL.BoolTreeLk(rer, acts, inp, BS.CannotExit, t);
      assert exists actsw: LS.Actions, bw: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, actsw, code, it.pc as nat)
          && EL.PikeLkActions(actsw)
          && ATR.EaOf(bw) == it.exit_allowed
          && EL.BoolTreeLk(rer, actsw, inp, bw, t)
          && GateAheadClear(actsw, LG.Empty)
          && WalkDefsOk(actsw);
    }
    assert GmtTieOutside(re, it, LG.Empty, S);          // gml == Empty, agrees with Empty
    assert ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, t, LG.Empty, it, ncap, nlook, nquant);
    // Construct machine B's PLANTED CANONICAL entry tree; the raw walk tree
    // `t` is its value-layer erasure witness.
    WkE.WalkOkEntry(re);
    assert WO.WalkOk(acts, code, 0, false);
    assert ATR.EaOf(BS.CannotExit) == false;
    tcan := ActionsTreeRepLkRE(rer, qm, acts, code, 0, inp, BS.CannotExit, t);
    assert ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, tcan, LG.Empty, it,
                              ncap, nlook, nquant) by {
      assert TreeRepLkRE(rer, qm, code, inp, tcan, it.pc as nat, it.exit_allowed);
      assert CE.ProgErase(t) == CE.ProgErase(tcan)
             && ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, t, LG.Empty, it, ncap, nlook, nquant);
    }
    assert ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, [(tcan, LG.Empty)], [it], ncap, nlook, nquant);
    // ptsB = PTS(inp, [(tcan, Empty)], None, [], InitialSeenTrees); best None both sides.
    assert PT.PikeTreeInitialState(tcan, inp) == PT.PTS(inp, [(tcan, LG.Empty)], None, [], SS.InitialSeenTrees);
    assert PT.PikeTreeInitialState(tstar, inp).PTS? && PT.PikeTreeInitialState(tstar, inp).inp == inp;
    assert BestTieLkNested(re, crv, str, ov, S, None, vms.bestmatch, ncap, nlook, nquant);
    // Blocked: genuine start — both sides empty.
    assert PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp) == [];
    forall nextinp | LC.AdvanceInput(inp, WP.Forward) == Some(nextinp)
      ensures BlockedRepLkCNested(rer, qm, re, code, inp, nextinp, crv, str, ov, S, [],
                                  PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant)
    { }
    // B-side seen ↔ processed: at the genuine start nothing is processed, so
    // `SeenRepLk` holds vacuously (mirror of `PIV.InitialInclusionRE`).
    InitialSeenRepLk(rer, qm, code, inp,
                     PIV.HdTreeOf([(tcan, LG.Empty)]), PIV.HeadPcOf([it]), RB.size(code));
  }

  /** (K-step) The composite is preserved across ONE ε-phase. Machine A
      advances by the PROVEN `PSM.InvariantPreservationRE` (a whole-phase
      `TrcRE` — queue/priority/loop mechanics inherited, never re-proved);
      machine B advances by `LiftAdvanceEpsilon` (the B-side worklist
      recursion over the SAME VM steps). The two sides never link directly:
      each pins its `inp` to `InpOfCp(str, cp)` through its own invariant. */
  lemma LiftStepC(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                  endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                  S: set<LG.GroupId>, ptsA: PT.PikeTreeState, ptsB: PT.PikeTreeState, vms: AI.VmState,
                  ncap: int, nlook: int, nquant: int)
    returns (ptsA': PT.PikeTreeState, ptsB': PT.PikeTreeState)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires |ov| == |str| + 1                                    // L3b: propagate to the backward LB gate
    requires PSM.StaticOkRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires S == PIV.CapIdsInLooks(re)   // the value-tie boundary (SetReg/gate cases)
    requires GateStaticsOk(qm, re, crv, ncap, nlook, nquant)   // per-lid look-table package (gate-pass case)
    requires LTB.LookUnique(re)           // (E3) cross-lid ownership pinning
    requires LTB.LookTablesOk(re, crv)    // (E4) row↔structure tie (gate converse)
    requires ptsA.PTS? && ptsB.PTS?
    requires |vms.processed.true_set| == RB.size(code) && |vms.processed.false_set| == RB.size(code)
    requires LiftInvC(rer, qm, re, code, endl, ngroups, crv, str, ov, S, ptsA, ptsB, vms, ncap, nlook, nquant)
    ensures PTL.TrcPikeTreeLk(ptsB, ptsB')
    ensures ptsA'.PTS? && ptsB'.PTS?
    ensures LiftInvC(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                     ptsA', ptsB', AI.FAdvanceEpsilon(code, vms, ov, LAnc.Forward).0, ncap, nlook, nquant)
  {
    var vms' := AI.FAdvanceEpsilon(code, vms, ov, LAnc.Forward).0;
    // ONE call: the composite dispatcher steps machine A per-case by the
    // proven Preserve*Case lemmas and machine B by the LiftPreserve*Lk tier.
    ptsA', ptsB' := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                       ptsA, vms, ptsB, LAnc.Forward, ncap, nlook, nquant);
    // the inp link: both sides pin their inp to InpOfCp(str, vms'.cp)
    assert PIV.PikeInvRE(rer, qm, re, code, ngroups, str, ptsA', vms');
    assert ptsA'.inp == PIV.InpOfCp(str, vms'.cp);
    assert ptsB'.inp == PIV.InpOfCp(str, vms'.cp);
  }

  /** (L4 NESTED) clone of `LiftStepC` — GmtTieInside dropped. */
  lemma LiftStepCNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                        endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                        S: set<LG.GroupId>, ptsA: PT.PikeTreeState, ptsB: PT.PikeTreeState, vms: AI.VmState,
                        ncap: int, nlook: int, nquant: int)
    returns (ptsA': PT.PikeTreeState, ptsB': PT.PikeTreeState)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires |ov| == |str| + 1                                    // L3b: propagate to the backward LB gate
    requires PSM.StaticOkNestedRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires S == PIV.CapIdsInLooks(re)   // the value-tie boundary (SetReg/gate cases)
    requires GateStaticsOk(qm, re, crv, ncap, nlook, nquant)   // per-lid look-table package (gate-pass case)
    requires LTB.LookUnique(re)           // (E3) cross-lid ownership pinning
    requires LTB.LookTablesOk(re, crv)    // (E4) row↔structure tie (gate converse)
    requires ptsA.PTS? && ptsB.PTS?
    requires |vms.processed.true_set| == RB.size(code) && |vms.processed.false_set| == RB.size(code)
    requires LiftInvCNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S, ptsA, ptsB, vms, ncap, nlook, nquant)
    ensures PTL.TrcPikeTreeLk(ptsB, ptsB')
    ensures ptsA'.PTS? && ptsB'.PTS?
    ensures LiftInvCNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                           ptsA', ptsB', AI.FAdvanceEpsilon(code, vms, ov, LAnc.Forward).0, ncap, nlook, nquant)
  {
    var vms' := AI.FAdvanceEpsilon(code, vms, ov, LAnc.Forward).0;
    // ONE call: the composite dispatcher steps machine A per-case by the
    // proven Preserve*Case lemmas and machine B by the LiftPreserve*Lk tier.
    ptsA', ptsB' := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                             ptsA, vms, ptsB, LAnc.Forward, ncap, nlook, nquant);
    // the inp link: both sides pin their inp to InpOfCp(str, vms'.cp)
    assert PIV.PikeInvRE(rer, qm, re, code, ngroups, str, ptsA', vms');
    assert ptsA'.inp == PIV.InpOfCp(str, vms'.cp);
    assert ptsB'.inp == PIV.InpOfCp(str, vms'.cp);
  }

  /** THE WHOLE-SEARCH COMPOSITE (mirror of `PSM.FindMatchSimRE`, both
      machines in lockstep): `FFindMatch` from a paired state drives machine B
      to `PTS_final(bestT)` with `bestT` tied to the VM's result. The consume
      phase reactivates the blocked pairing (`BlockedToActiveLkC`) and
      re-establishes both invariants at the advanced position. */
  lemma LiftFindMatchC(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                       endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                       S: set<LG.GroupId>, ptsA: PT.PikeTreeState, bst: PT.PikeTreeState,
                       vms: AI.VmState, cdn: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    returns (bestT: Option<LT.Leaf>)
    requires PSM.StaticOkRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires |ov| == |str| + 1                                    // L3b: propagate to the backward LB gate
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires S == PIV.CapIdsInLooks(re)
    requires GateStaticsOk(qm, re, crv, ncap, nlook, nquant)
    requires LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires ptsA.PTS? && bst.PTS?
    requires |vms.processed.true_set| == RB.size(code) && |vms.processed.false_set| == RB.size(code)
    requires vms.context.nextchar == AI.get_char(str, vms.cp)
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, vms, ncap, nlook, nquant)
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, vms, ncap, nlook, nquant)
    ensures PTL.TrcPikeTreeLk(bst, PT.PTS_final(bestT))
    ensures BestTieLk(re, crv, str, ov, S, bestT,
                      AI.FFindMatch(code, str, vms, ov, LAnc.Forward, cdn).0, ncap, nlook, nquant)
    decreases |str| - vms.cp
  {
    var dir := LAnc.Forward;
    var s0 := vms.(cdn := LCdn.build_cdn_v(cdn, vms.cp, ov, vms.context, dir));
    // Neither invariant reads cdn.
    assert PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, s0, ncap, nlook, nquant);
    assert LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s0, ncap, nlook, nquant);
    var ptsA1, bst1 := LiftAdvanceEpsilon(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                          ptsA, s0, bst, dir, ncap, nlook, nquant);
    var (s1, ov1) := AI.FAdvanceEpsilon(code, s0, ov, dir);
    PSM.StaticOkNoWrite(qm, re, code, endl);
    CM.FAdvanceEpsilonOvStable(code, s0, ov, dir);
    assert ov1 == ov;
    PSM.FAdvanceEpsilonActiveEmpty(code, s0, ov, dir);
    assert s1.active == [] && s1.cp == s0.cp == vms.cp && s1.context == vms.context;
    assert PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA1, s1, ncap, nlook, nquant);
    assert LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, s1, ncap, nlook, nquant);

    assert bst1.PTS?;
    var PTS(inp1, ta1, best1, tb1, seen1) := bst1;
    assert ActiveRepLkC(rer, qm, re, code, inp1, crv, str, ov, S, ta1, s1.active, ncap, nlook, nquant);
    assert ta1 == [];
    assert inp1 == PIV.InpOfCp(str, s1.cp) && 0 <= s1.cp <= |str|;
    assert BestTieLk(re, crv, str, ov, S, best1, s1.bestmatch, ncap, nlook, nquant);

    if |s1.blocked| == 0 {
      assert LC.Reverse(s1.blocked) == [];
      assert tb1 == [] by {
        if LC.AdvanceInput(inp1, WP.Forward).Some? {
          var nx :| LC.AdvanceInput(inp1, WP.Forward) == Some(nx);
          assert BlockedRepLkC(rer, qm, re, code, inp1, nx, crv, str, ov, S, tb1,
                               PIV.MatchingBlocked(LC.Reverse(s1.blocked), inp1), ncap, nlook, nquant);
          assert PIV.MatchingBlocked([], inp1) == [];
        }
      }
      bestT := best1;
      assert PTL.PikeTreeStepLk(bst1, PT.PTS_final(best1));
      TrcLkRefl(PT.PTS_final(best1));
      TrcLkCons(bst1, PT.PTS_final(best1), PT.PTS_final(best1));
      TrcLkTrans(bst, bst1, PT.PTS_final(best1));
      assert AI.FFindMatch(code, str, vms, ov, dir, cdn).0 == s1.bestmatch;
    } else if s1.context.nextchar.None? {
      assert AI.get_char(str, vms.cp).None?;
      assert vms.cp >= |str| && s1.cp == |str|;
      assert inp1.next == str[s1.cp..] == [];
      assert LC.AdvanceInput(inp1, WP.Forward).None?;
      assert tb1 == [];
      bestT := best1;
      assert PTL.PikeTreeStepLk(bst1, PT.PTS_final(best1));
      TrcLkRefl(PT.PTS_final(best1));
      TrcLkCons(bst1, PT.PTS_final(best1), PT.PTS_final(best1));
      TrcLkTrans(bst, bst1, PT.PTS_final(best1));
      assert AI.FFindMatch(code, str, vms, ov, dir, cdn).0 == s1.bestmatch;
    } else {
      // A real character remains: consume it (the FFindMatch else-branch).
      assert AI.get_char(str, vms.cp).Some?;
      assert vms.cp < |str|;
      assert inp1.next == str[s1.cp..] && |inp1.next| > 0;
      assert s1.context.nextchar == Some(inp1.next[0]);
      PSM.FConsumeResumes(s1, inp1);
      var s2 := AI.FConsume(s1);
      var filter := PIV.MatchingBlocked(LC.Reverse(s1.blocked), inp1);
      assert PSM.ResumeAll(filter) + s1.active == PSM.ResumeAll(filter);
      assert s2 == s1.(active := PSM.ResumeAll(filter), blocked := []);
      var s3 := s2.(processed := AI.init_bpcset(RB.size(code)),
      isblocked := AI.init_pcset(RB.size(code)),
      cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
      var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
      var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
      assert s4.cp == vms.cp + 1;
      assert s4.context.nextchar == AI.get_char(str, s4.cp);
      assert AI.FFindMatch(code, str, vms, ov, dir, cdn)
          == AI.FFindMatch(code, str, s4, ov1, dir, cdn);

      PSM.AdvanceInpOfCpBridge(str, vms.cp);
      var nextinp := PT.NextInp(inp1);
      assert nextinp == PIV.InpOfCp(str, vms.cp + 1);
      assert LC.AdvanceInput(inp1, WP.Forward) == Some(nextinp);
      assert BlockedRepLkC(rer, qm, re, code, inp1, nextinp, crv, str, ov, S, tb1, filter,
                           ncap, nlook, nquant);

      if |tb1| == 0 {
        assert |filter| == 0;
        assert s4.active == [] && s4.blocked == [];
        PSM.FFindMatchInert(code, str, s4, ov1, dir, cdn);
        assert AI.FFindMatch(code, str, s4, ov1, dir, cdn).0 == s4.bestmatch == s1.bestmatch;
        bestT := best1;
        assert PTL.PikeTreeStepLk(bst1, PT.PTS_final(best1));
        TrcLkRefl(PT.PTS_final(best1));
        TrcLkCons(bst1, PT.PTS_final(best1), PT.PTS_final(best1));
        TrcLkTrans(bst, bst1, PT.PTS_final(best1));
      } else {
        // B: pts_nextchar — the blocked pairs become the next position's actives.
        var bst2 := PT.PTS(nextinp, tb1, best1, [], SS.InitialSeenTrees);
        assert PTL.PikeTreeStepLk(bst1, bst2);

        // ---- machine A: re-establish PikeInvFullRE at (ptsA2, s4) — the
        // FindMatchSimRE consume-phase block, verbatim.
        assert ptsA1.PTS?;
        var PTS(inpA1, taA1, bestA1, tbA1, seenA1) := ptsA1;
        assert PIV.ActiveRepRE(rer, qm, re, code, str, inpA1, taA1, s1.active);
        assert taA1 == [] && inpA1 == PIV.InpOfCp(str, s1.cp);
        assert PIV.BlockedRepRE(rer, qm, re, code, str, inpA1, nextinp, tbA1, filter);
        var ptsA2 := PT.PTS(nextinp, tbA1, bestA1, [], SS.InitialSeenTrees);
        PSM.BlockedToActiveRE(rer, qm, re, code, str, inpA1, nextinp, tbA1, filter);
        assert PIV.ActiveRepRE(rer, qm, re, code, str, nextinp, tbA1, s4.active);
        CM.FConsumeClocksLE(s1);
        CM.FConsumeRegsWf(s1, ncap, nlook, nquant);
        CM.FConsumeCapsLE(s1);
        assert CM.VmClocksLE(s4) by {
          assert s4.active == s2.active && s4.blocked == s2.blocked
                 && s4.bestmatch == s2.bestmatch && s4.clock == s2.clock;
        }
        assert CM.VmRegsWf(s4, ncap, nlook, nquant) by {
          assert s4.active == s2.active && s4.blocked == s2.blocked && s4.bestmatch == s2.bestmatch;
        }
        assert CM.VmCapsLE(s4) by { CM.VmCapsLEAdvance(s2, s4); }
        assert forall t2 | t2 in s4.active :: PSM.ThreadNestRE(re, code, endl, t2.pc, t2) by {
          forall p | p in filter ensures PSM.ThreadNestRE(re, code, endl, p.0.pc + 1, p.0) {
            PSM.MatchingBlockedSubset(LC.Reverse(s1.blocked), inp1, p);
            PSM.ReverseMembership(s1.blocked, p);
            assert p in s1.blocked;
          }
          PSM.ResumeAllNest(re, code, endl, filter);
        }
        PIV.InitialInclusionRE(rer, qm, code, nextinp, PIV.HdTreeOf(tbA1),
                               PIV.HeadPcOf(s4.active), RB.size(code));
        assert PSM.IsblockedInclusionRE(rer, qm, code, nextinp, SS.InitialSeenTrees, s4.isblocked) by {
          forall pc0: nat | AI.pc_mem(s4.isblocked, pc0)
            ensures exists t0: LT.Tree, b0: bool ::
                      SS.Inseen(SS.InitialSeenTrees, t0) && TT.TreeThreadRE(rer, qm, code, nextinp, t0, pc0, b0)
          {
            assert s4.isblocked[pc0] == false;
            assert false;
          }
        }
        assert forall t2 | t2 in s4.active :: PSM.EaColdOkRE(code, t2) by {
          PSM.ResumeAllEa(filter);
          assert s4.active == PSM.ResumeAll(filter);
        }
        assert forall t2 | t2 in s4.active :: PIV.LooksCapUnset(re, t2.capture_regs.a_clk) by {
          forall p | p in filter ensures PIV.LooksCapUnset(re, p.0.capture_regs.a_clk) {
            PSM.MatchingBlockedSubset(LC.Reverse(s1.blocked), inp1, p);
            PSM.ReverseMembership(s1.blocked, p);
            assert p in s1.blocked;
          }
          PSM.ResumeAllCapUnset(re, filter);
          assert s4.active == PSM.ResumeAll(filter);
        }
        assert PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA2, s4, ncap, nlook, nquant);

        // ---- machine B: LiftInv at (bst2, s4).
        BlockedToActiveLkC(rer, qm, re, code, inp1, nextinp, crv, str, ov, S, tb1, filter,
                           ncap, nlook, nquant);
        assert ActiveRepLkC(rer, qm, re, code, nextinp, crv, str, ov, S, tb1, s4.active,
                            ncap, nlook, nquant);
        assert PIV.ContextOkRE(str, s4.cp, s4.context);
        forall nx2 | LC.AdvanceInput(nextinp, WP.Forward) == Some(nx2)
          ensures BlockedRepLkC(rer, qm, re, code, nextinp, nx2, crv, str, ov, S, [],
                                PIV.MatchingBlocked(LC.Reverse(s4.blocked), nextinp), ncap, nlook, nquant)
        {
          assert LC.Reverse(s4.blocked) == [];
          assert PIV.MatchingBlocked([], nextinp) == [];
        }
        InitialSeenRepLk(rer, qm, code, nextinp, PIV.HdTreeOf(tb1), PIV.HeadPcOf(s4.active),
                         RB.size(code));
        assert IsblockedRepLk(rer, qm, code, nextinp, SS.InitialSeenTrees, s4.isblocked) by {
          forall pc0: nat | AI.pc_mem(s4.isblocked, pc0)
            ensures exists t0: LT.Tree, b0: bool ::
                      SS.Inseen(SS.InitialSeenTrees, t0) && TreeRepLkRE(rer, qm, code, nextinp, t0, pc0, b0)
          {
            assert s4.isblocked[pc0] == false;
            assert false;
          }
        }
        assert SSx.IsStrictSuffix(nextinp, inp1, WP.Forward);
        LL.OracleOkSuffixStep(rer, qm, inp1, nextinp);

        // ---- (E3) the carrier crosses the consume: reactivation keeps registers ----
        assert LookNestRepB(re, S, tb1, filter) by {
          assert LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, s1, ncap, nlook, nquant);
          assert bst1 == PT.PTS(inp1, ta1, best1, tb1, seen1);
          assert LC.AdvanceInput(inp1, WP.Forward).Some?;
          assert filter == PIV.MatchingBlocked(LC.Reverse(s1.blocked), inp1);
        }
        assert LookNestRepC(re, S, tb1, s4.active) by {
          assert |tb1| == |filter|;                        // LookNestRepB lengths
          assert s4.active == PSM.ResumeAll(filter);
          ResumeAllLen(filter);
          forall i | 0 <= i < |tb1|
            ensures LookNestOkT(re, S, tb1[i].1, s4.active[i])
          {
            assert LookNestOkT(re, S, tb1[i].1, filter[i].0);
            ResumeAllIndex(filter, i);
            assert s4.active[i] == filter[i].0.(exit_allowed := true, pc := filter[i].0.pc + 1);
            assert s4.active[i].capture_regs == filter[i].0.capture_regs
                   && s4.active[i].look_regs == filter[i].0.look_regs
                   && s4.active[i].quant_regs == filter[i].0.quant_regs;
          }
        }
        assert LC.AdvanceInput(nextinp, WP.Forward).Some? ==>
            LookNestRepB(re, S, [], PIV.MatchingBlocked(LC.Reverse(s4.blocked), nextinp)) by {
          assert LC.Reverse(s4.blocked) == [];
          assert PIV.MatchingBlocked([], nextinp) == [];
        }
        assert LookNestBackRepB(re, crv, str, ov, S, tb1, filter, ncap, nlook, nquant) by {
          assert LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, s1, ncap, nlook, nquant);
          assert bst1 == PT.PTS(inp1, ta1, best1, tb1, seen1);
          assert LC.AdvanceInput(inp1, WP.Forward).Some?;
        }
        assert LookNestBackRepC(re, crv, str, ov, S, tb1, s4.active, ncap, nlook, nquant) by {
          assert s4.active == PSM.ResumeAll(filter);
          ResumeAllLen(filter);
          forall i | 0 <= i < |tb1|
            ensures LookNestBackT(re, crv, str, ov, S, tb1[i].1, s4.active[i], ncap, nlook, nquant)
          {
            assert LookNestBackT(re, crv, str, ov, S, tb1[i].1, filter[i].0, ncap, nlook, nquant);
            ResumeAllIndex(filter, i);
            assert s4.active[i] == filter[i].0.(exit_allowed := true, pc := filter[i].0.pc + 1);
            assert s4.active[i].look_regs == filter[i].0.look_regs
                   && s4.active[i].quant_regs == filter[i].0.quant_regs;
            LookNestBackTRegSame(re, crv, str, ov, S, tb1[i].1, tb1[i].1, filter[i].0, s4.active[i],
                                 ncap, nlook, nquant);
          }
        }
        assert LC.AdvanceInput(nextinp, WP.Forward).Some? ==>
            LookNestBackRepB(re, crv, str, ov, S, [],
                             PIV.MatchingBlocked(LC.Reverse(s4.blocked), nextinp), ncap, nlook, nquant) by {
          assert LC.Reverse(s4.blocked) == [];
          assert PIV.MatchingBlocked([], nextinp) == [];
        }
        assert LiftInv(rer, qm, re, code, crv, str, ov, S, bst2, s4, ncap, nlook, nquant);

        // recurse and chain.
        bestT := LiftFindMatchC(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                ptsA2, bst2, s4, cdn, ncap, nlook, nquant);
        TrcLkCons(bst1, bst2, PT.PTS_final(bestT));
        TrcLkTrans(bst, bst1, PT.PTS_final(bestT));
        assert AI.FFindMatch(code, str, s4, ov1, dir, cdn).0
            == AI.FFindMatch(code, str, vms, ov, dir, cdn).0;
      }
    }
  }

  /** (L4 NESTED) clone of `LiftFindMatchC` — GmtTieInside dropped. */
  lemma LiftFindMatchCNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                             endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                             S: set<LG.GroupId>, ptsA: PT.PikeTreeState, bst: PT.PikeTreeState,
                             vms: AI.VmState, cdn: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    returns (bestT: Option<LT.Leaf>)
    requires PSM.StaticOkNestedRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires |ov| == |str| + 1                                    // L3b: propagate to the backward LB gate
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires S == PIV.CapIdsInLooks(re)
    requires GateStaticsOk(qm, re, crv, ncap, nlook, nquant)
    requires LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires ptsA.PTS? && bst.PTS?
    requires |vms.processed.true_set| == RB.size(code) && |vms.processed.false_set| == RB.size(code)
    requires vms.context.nextchar == AI.get_char(str, vms.cp)
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, vms, ncap, nlook, nquant)
    requires LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, vms, ncap, nlook, nquant)
    ensures PTL.TrcPikeTreeLk(bst, PT.PTS_final(bestT))
    ensures BestTieLkNested(re, crv, str, ov, S, bestT,
                            AI.FFindMatch(code, str, vms, ov, LAnc.Forward, cdn).0, ncap, nlook, nquant)
    decreases |str| - vms.cp
  {
    var dir := LAnc.Forward;
    var s0 := vms.(cdn := LCdn.build_cdn_v(cdn, vms.cp, ov, vms.context, dir));
    // Neither invariant reads cdn.
    assert PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, s0, ncap, nlook, nquant);
    assert LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst, s0, ncap, nlook, nquant);
    var ptsA1, bst1 := LiftAdvanceEpsilonNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                ptsA, s0, bst, dir, ncap, nlook, nquant);
    var (s1, ov1) := AI.FAdvanceEpsilon(code, s0, ov, dir);
    PSM.StaticOkNoWriteNested(qm, re, code, endl);
    CM.FAdvanceEpsilonOvStable(code, s0, ov, dir);
    assert ov1 == ov;
    PSM.FAdvanceEpsilonActiveEmpty(code, s0, ov, dir);
    assert s1.active == [] && s1.cp == s0.cp == vms.cp && s1.context == vms.context;
    assert PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA1, s1, ncap, nlook, nquant);
    assert LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, s1, ncap, nlook, nquant);

    assert bst1.PTS?;
    var PTS(inp1, ta1, best1, tb1, seen1) := bst1;
    assert ActiveRepLkCNested(rer, qm, re, code, inp1, crv, str, ov, S, ta1, s1.active, ncap, nlook, nquant);
    assert ta1 == [];
    assert inp1 == PIV.InpOfCp(str, s1.cp) && 0 <= s1.cp <= |str|;
    assert BestTieLkNested(re, crv, str, ov, S, best1, s1.bestmatch, ncap, nlook, nquant);

    if |s1.blocked| == 0 {
      assert LC.Reverse(s1.blocked) == [];
      assert tb1 == [] by {
        if LC.AdvanceInput(inp1, WP.Forward).Some? {
          var nx :| LC.AdvanceInput(inp1, WP.Forward) == Some(nx);
          assert BlockedRepLkCNested(rer, qm, re, code, inp1, nx, crv, str, ov, S, tb1,
                                     PIV.MatchingBlocked(LC.Reverse(s1.blocked), inp1), ncap, nlook, nquant);
          assert PIV.MatchingBlocked([], inp1) == [];
        }
      }
      bestT := best1;
      assert PTL.PikeTreeStepLk(bst1, PT.PTS_final(best1));
      TrcLkRefl(PT.PTS_final(best1));
      TrcLkCons(bst1, PT.PTS_final(best1), PT.PTS_final(best1));
      TrcLkTrans(bst, bst1, PT.PTS_final(best1));
      assert AI.FFindMatch(code, str, vms, ov, dir, cdn).0 == s1.bestmatch;
    } else if s1.context.nextchar.None? {
      assert AI.get_char(str, vms.cp).None?;
      assert vms.cp >= |str| && s1.cp == |str|;
      assert inp1.next == str[s1.cp..] == [];
      assert LC.AdvanceInput(inp1, WP.Forward).None?;
      assert tb1 == [];
      bestT := best1;
      assert PTL.PikeTreeStepLk(bst1, PT.PTS_final(best1));
      TrcLkRefl(PT.PTS_final(best1));
      TrcLkCons(bst1, PT.PTS_final(best1), PT.PTS_final(best1));
      TrcLkTrans(bst, bst1, PT.PTS_final(best1));
      assert AI.FFindMatch(code, str, vms, ov, dir, cdn).0 == s1.bestmatch;
    } else {
      // A real character remains: consume it (the FFindMatch else-branch).
      assert AI.get_char(str, vms.cp).Some?;
      assert vms.cp < |str|;
      assert inp1.next == str[s1.cp..] && |inp1.next| > 0;
      assert s1.context.nextchar == Some(inp1.next[0]);
      PSM.FConsumeResumes(s1, inp1);
      var s2 := AI.FConsume(s1);
      var filter := PIV.MatchingBlocked(LC.Reverse(s1.blocked), inp1);
      assert PSM.ResumeAll(filter) + s1.active == PSM.ResumeAll(filter);
      assert s2 == s1.(active := PSM.ResumeAll(filter), blocked := []);
      var s3 := s2.(processed := AI.init_bpcset(RB.size(code)),
      isblocked := AI.init_pcset(RB.size(code)),
      cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
      var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
      var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
      assert s4.cp == vms.cp + 1;
      assert s4.context.nextchar == AI.get_char(str, s4.cp);
      assert AI.FFindMatch(code, str, vms, ov, dir, cdn)
          == AI.FFindMatch(code, str, s4, ov1, dir, cdn);

      PSM.AdvanceInpOfCpBridge(str, vms.cp);
      var nextinp := PT.NextInp(inp1);
      assert nextinp == PIV.InpOfCp(str, vms.cp + 1);
      assert LC.AdvanceInput(inp1, WP.Forward) == Some(nextinp);
      assert BlockedRepLkCNested(rer, qm, re, code, inp1, nextinp, crv, str, ov, S, tb1, filter,
                                 ncap, nlook, nquant);

      if |tb1| == 0 {
        assert |filter| == 0;
        assert s4.active == [] && s4.blocked == [];
        PSM.FFindMatchInert(code, str, s4, ov1, dir, cdn);
        assert AI.FFindMatch(code, str, s4, ov1, dir, cdn).0 == s4.bestmatch == s1.bestmatch;
        bestT := best1;
        assert PTL.PikeTreeStepLk(bst1, PT.PTS_final(best1));
        TrcLkRefl(PT.PTS_final(best1));
        TrcLkCons(bst1, PT.PTS_final(best1), PT.PTS_final(best1));
        TrcLkTrans(bst, bst1, PT.PTS_final(best1));
      } else {
        // B: pts_nextchar — the blocked pairs become the next position's actives.
        var bst2 := PT.PTS(nextinp, tb1, best1, [], SS.InitialSeenTrees);
        assert PTL.PikeTreeStepLk(bst1, bst2);

        // ---- machine A: re-establish PikeInvFullRE at (ptsA2, s4) — the
        // FindMatchSimRE consume-phase block, verbatim.
        assert ptsA1.PTS?;
        var PTS(inpA1, taA1, bestA1, tbA1, seenA1) := ptsA1;
        assert PIV.ActiveRepRE(rer, qm, re, code, str, inpA1, taA1, s1.active);
        assert taA1 == [] && inpA1 == PIV.InpOfCp(str, s1.cp);
        assert PIV.BlockedRepRE(rer, qm, re, code, str, inpA1, nextinp, tbA1, filter);
        var ptsA2 := PT.PTS(nextinp, tbA1, bestA1, [], SS.InitialSeenTrees);
        PSM.BlockedToActiveRE(rer, qm, re, code, str, inpA1, nextinp, tbA1, filter);
        assert PIV.ActiveRepRE(rer, qm, re, code, str, nextinp, tbA1, s4.active);
        CM.FConsumeClocksLE(s1);
        CM.FConsumeRegsWf(s1, ncap, nlook, nquant);
        CM.FConsumeCapsLE(s1);
        assert CM.VmClocksLE(s4) by {
          assert s4.active == s2.active && s4.blocked == s2.blocked
                 && s4.bestmatch == s2.bestmatch && s4.clock == s2.clock;
        }
        assert CM.VmRegsWf(s4, ncap, nlook, nquant) by {
          assert s4.active == s2.active && s4.blocked == s2.blocked && s4.bestmatch == s2.bestmatch;
        }
        assert CM.VmCapsLE(s4) by { CM.VmCapsLEAdvance(s2, s4); }
        assert forall t2 | t2 in s4.active :: PSM.ThreadNestRE(re, code, endl, t2.pc, t2) by {
          forall p | p in filter ensures PSM.ThreadNestRE(re, code, endl, p.0.pc + 1, p.0) {
            PSM.MatchingBlockedSubset(LC.Reverse(s1.blocked), inp1, p);
            PSM.ReverseMembership(s1.blocked, p);
            assert p in s1.blocked;
          }
          PSM.ResumeAllNest(re, code, endl, filter);
        }
        PIV.InitialInclusionRE(rer, qm, code, nextinp, PIV.HdTreeOf(tbA1),
                               PIV.HeadPcOf(s4.active), RB.size(code));
        assert PSM.IsblockedInclusionRE(rer, qm, code, nextinp, SS.InitialSeenTrees, s4.isblocked) by {
          forall pc0: nat | AI.pc_mem(s4.isblocked, pc0)
            ensures exists t0: LT.Tree, b0: bool ::
                      SS.Inseen(SS.InitialSeenTrees, t0) && TT.TreeThreadRE(rer, qm, code, nextinp, t0, pc0, b0)
          {
            assert s4.isblocked[pc0] == false;
            assert false;
          }
        }
        assert forall t2 | t2 in s4.active :: PSM.EaColdOkRE(code, t2) by {
          PSM.ResumeAllEa(filter);
          assert s4.active == PSM.ResumeAll(filter);
        }
        assert forall t2 | t2 in s4.active :: PIV.LooksCapUnset(re, t2.capture_regs.a_clk) by {
          forall p | p in filter ensures PIV.LooksCapUnset(re, p.0.capture_regs.a_clk) {
            PSM.MatchingBlockedSubset(LC.Reverse(s1.blocked), inp1, p);
            PSM.ReverseMembership(s1.blocked, p);
            assert p in s1.blocked;
          }
          PSM.ResumeAllCapUnset(re, filter);
          assert s4.active == PSM.ResumeAll(filter);
        }
        assert PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA2, s4, ncap, nlook, nquant);

        // ---- machine B: LiftInv at (bst2, s4).
        BlockedToActiveLkCNested(rer, qm, re, code, inp1, nextinp, crv, str, ov, S, tb1, filter,
                                 ncap, nlook, nquant);
        assert ActiveRepLkCNested(rer, qm, re, code, nextinp, crv, str, ov, S, tb1, s4.active,
                                  ncap, nlook, nquant);
        assert PIV.ContextOkRE(str, s4.cp, s4.context);
        forall nx2 | LC.AdvanceInput(nextinp, WP.Forward) == Some(nx2)
          ensures BlockedRepLkCNested(rer, qm, re, code, nextinp, nx2, crv, str, ov, S, [],
                                      PIV.MatchingBlocked(LC.Reverse(s4.blocked), nextinp), ncap, nlook, nquant)
        {
          assert LC.Reverse(s4.blocked) == [];
          assert PIV.MatchingBlocked([], nextinp) == [];
        }
        InitialSeenRepLk(rer, qm, code, nextinp, PIV.HdTreeOf(tb1), PIV.HeadPcOf(s4.active),
                         RB.size(code));
        assert IsblockedRepLk(rer, qm, code, nextinp, SS.InitialSeenTrees, s4.isblocked) by {
          forall pc0: nat | AI.pc_mem(s4.isblocked, pc0)
            ensures exists t0: LT.Tree, b0: bool ::
                      SS.Inseen(SS.InitialSeenTrees, t0) && TreeRepLkRE(rer, qm, code, nextinp, t0, pc0, b0)
          {
            assert s4.isblocked[pc0] == false;
            assert false;
          }
        }
        assert SSx.IsStrictSuffix(nextinp, inp1, WP.Forward);
        LL.OracleOkSuffixStep(rer, qm, inp1, nextinp);

        // ---- (E3) the carrier crosses the consume: reactivation keeps registers ----
        assert LookNestRepB(re, S, tb1, filter) by {
          assert LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, s1, ncap, nlook, nquant);
          assert bst1 == PT.PTS(inp1, ta1, best1, tb1, seen1);
          assert LC.AdvanceInput(inp1, WP.Forward).Some?;
          assert filter == PIV.MatchingBlocked(LC.Reverse(s1.blocked), inp1);
        }
        assert LookNestRepC(re, S, tb1, s4.active) by {
          assert |tb1| == |filter|;                        // LookNestRepB lengths
          assert s4.active == PSM.ResumeAll(filter);
          ResumeAllLen(filter);
          forall i | 0 <= i < |tb1|
            ensures LookNestOkT(re, S, tb1[i].1, s4.active[i])
          {
            assert LookNestOkT(re, S, tb1[i].1, filter[i].0);
            ResumeAllIndex(filter, i);
            assert s4.active[i] == filter[i].0.(exit_allowed := true, pc := filter[i].0.pc + 1);
            assert s4.active[i].capture_regs == filter[i].0.capture_regs
                   && s4.active[i].look_regs == filter[i].0.look_regs
                   && s4.active[i].quant_regs == filter[i].0.quant_regs;
          }
        }
        assert LC.AdvanceInput(nextinp, WP.Forward).Some? ==>
            LookNestRepB(re, S, [], PIV.MatchingBlocked(LC.Reverse(s4.blocked), nextinp)) by {
          assert LC.Reverse(s4.blocked) == [];
          assert PIV.MatchingBlocked([], nextinp) == [];
        }
        assert LookNestBackRepB(re, crv, str, ov, S, tb1, filter, ncap, nlook, nquant) by {
          assert LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst1, s1, ncap, nlook, nquant);
          assert bst1 == PT.PTS(inp1, ta1, best1, tb1, seen1);
          assert LC.AdvanceInput(inp1, WP.Forward).Some?;
        }
        assert LookNestBackRepC(re, crv, str, ov, S, tb1, s4.active, ncap, nlook, nquant) by {
          assert s4.active == PSM.ResumeAll(filter);
          ResumeAllLen(filter);
          forall i | 0 <= i < |tb1|
            ensures LookNestBackT(re, crv, str, ov, S, tb1[i].1, s4.active[i], ncap, nlook, nquant)
          {
            assert LookNestBackT(re, crv, str, ov, S, tb1[i].1, filter[i].0, ncap, nlook, nquant);
            ResumeAllIndex(filter, i);
            assert s4.active[i] == filter[i].0.(exit_allowed := true, pc := filter[i].0.pc + 1);
            assert s4.active[i].look_regs == filter[i].0.look_regs
                   && s4.active[i].quant_regs == filter[i].0.quant_regs;
            LookNestBackTRegSame(re, crv, str, ov, S, tb1[i].1, tb1[i].1, filter[i].0, s4.active[i],
                                 ncap, nlook, nquant);
          }
        }
        assert LC.AdvanceInput(nextinp, WP.Forward).Some? ==>
            LookNestBackRepB(re, crv, str, ov, S, [],
                             PIV.MatchingBlocked(LC.Reverse(s4.blocked), nextinp), ncap, nlook, nquant) by {
          assert LC.Reverse(s4.blocked) == [];
          assert PIV.MatchingBlocked([], nextinp) == [];
        }
        assert LiftInvNested(rer, qm, re, code, crv, str, ov, S, bst2, s4, ncap, nlook, nquant);

        // recurse and chain.
        bestT := LiftFindMatchCNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                      ptsA2, bst2, s4, cdn, ncap, nlook, nquant);
        TrcLkCons(bst1, bst2, PT.PTS_final(bestT));
        TrcLkTrans(bst, bst1, PT.PTS_final(bestT));
        assert AI.FFindMatch(code, str, s4, ov1, dir, cdn).0
            == AI.FFindMatch(code, str, vms, ov, dir, cdn).0;
      }
    }
  }

  lemma L3aCompositeClose(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                          endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                          S: set<LG.GroupId>, tstar: LT.Tree, t: LT.Tree, inp: LC.Input,
                          vms: AI.VmState, cdn: LCdn.cdns, result: Option<AI.Thread>,
                          ncap: int, nlook: int, nquant: int)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires |ov| == |str| + 1                                    // L3b: propagate to the backward LB gate
    requires PSM.StaticOkRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.multiline
    requires !rer.ignoreCase
    requires S == PIV.CapIdsInLooks(re)
    requires GateStaticsOk(qm, re, crv, ncap, nlook, nquant)
    requires LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires code == CP.compile_to_bytecode(re)
    requires vms.blocked == []
    requires vms.processed == AI.init_bpcset(RB.size(code))
    requires vms.isblocked == AI.init_pcset(RB.size(code))
    requires PIV.ContextOkRE(str, vms.cp, vms.context)
    // Thread-anchored entry facts (feed LiftInitC) — replace the dead
    // LeavesAgreeAtOutside(tstar, t) tree link.
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re)
    requires AR.ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
    requires EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t)
    requires PTL.PikeSubtreeLk(t)
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str,
                               PT.PikeTreeInitialState(tstar, inp), vms, ncap, nlook, nquant)
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires inp == PIV.InpOfCp(str, vms.cp) && 0 <= vms.cp <= |str|
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.bestmatch.None?
    requires |vms.processed.true_set| == RB.size(code) && |vms.processed.false_set| == RB.size(code)
    requires vms.context.nextchar == AI.get_char(str, vms.cp)
    requires result == AI.FFindMatch(code, str, vms, ov, LAnc.Forward, cdn).0
    ensures BestTieLk(re, crv, str, ov, S, LT.FirstLeaf(t, inp), result, ncap, nlook, nquant)
  {
    NoTrueStampsFromStaticRE(qm, re, code, endl);   // §2.5b stage 2a
    var tcan := LiftInitC(rer, qm, re, code, endl, ngroups, crv, str, ov, S, tstar, t, inp, vms,
                          ncap, nlook, nquant);
    assert LiftInv(rer, qm, re, code, crv, str, ov, S,
                   PT.PikeTreeInitialState(tcan, inp), vms, ncap, nlook, nquant);
    var bestT := LiftFindMatchC(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                PT.PikeTreeInitialState(tstar, inp),
                                PT.PikeTreeInitialState(tcan, inp),
                                vms, cdn, ncap, nlook, nquant);
    // bestT IS the canonical tree's first leaf ...
    PikeSubtreeLkEraseIff(t);
    PikeSubtreeLkEraseIff(tcan);
    assert PTL.PikeSubtreeLk(tcan);
    PTL.PikeTreeLkComputesFirstLeaf(tcan, inp, bestT);
    assert bestT == LT.FirstLeaf(tcan, inp);
    // ... which is the RAW entry tree's first leaf (Progress is leaf-transparent)
    assert CE.LeavesAgree(tcan, t) by {
      forall gm: LG.GroupMap, xinp: LC.Input, dr: WP.Direction
        ensures LT.TreeLeaves(tcan, gm, xinp, dr) == LT.TreeLeaves(t, gm, xinp, dr)
      {
        ProgEraseLeavesEq(tcan, gm, xinp, dr);
        ProgEraseLeavesEq(t, gm, xinp, dr);
      }
    }
    CE.LAFirstLeaf(tcan, t, inp);
    assert LT.FirstLeaf(t, inp) == bestT;
  }

  /** (L4 NESTED) clone of `L3aCompositeClose` — GmtTieInside dropped. */
  lemma L3aCompositeCloseNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                S: set<LG.GroupId>, tstar: LT.Tree, t: LT.Tree, inp: LC.Input,
                                vms: AI.VmState, cdn: LCdn.cdns, result: Option<AI.Thread>,
                                ncap: int, nlook: int, nquant: int)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires |ov| == |str| + 1                                    // L3b: propagate to the backward LB gate
    requires PSM.StaticOkRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.multiline
    requires !rer.ignoreCase
    requires S == PIV.CapIdsInLooks(re)
    requires GateStaticsOk(qm, re, crv, ncap, nlook, nquant)
    requires LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires code == CP.compile_to_bytecode(re)
    requires vms.blocked == []
    requires vms.processed == AI.init_bpcset(RB.size(code))
    requires vms.isblocked == AI.init_pcset(RB.size(code))
    requires PIV.ContextOkRE(str, vms.cp, vms.context)
    // Thread-anchored entry facts (feed LiftInitC) — replace the dead
    // LeavesAgreeAtOutside(tstar, t) tree link.
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re)
    requires AR.ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
    requires EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t)
    requires PTL.PikeSubtreeLk(t)
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str,
                               PT.PikeTreeInitialState(tstar, inp), vms, ncap, nlook, nquant)
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires inp == PIV.InpOfCp(str, vms.cp) && 0 <= vms.cp <= |str|
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.bestmatch.None?
    requires |vms.processed.true_set| == RB.size(code) && |vms.processed.false_set| == RB.size(code)
    requires vms.context.nextchar == AI.get_char(str, vms.cp)
    requires result == AI.FFindMatch(code, str, vms, ov, LAnc.Forward, cdn).0
    ensures BestTieLkNested(re, crv, str, ov, S, LT.FirstLeaf(t, inp), result, ncap, nlook, nquant)
  {
    NoTrueStampsFromStaticRE(qm, re, code, endl);   // §2.5b stage 2a
    var tcan := LiftInitCNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S, tstar, t, inp, vms,
                                ncap, nlook, nquant);
    assert LiftInvNested(rer, qm, re, code, crv, str, ov, S,
                         PT.PikeTreeInitialState(tcan, inp), vms, ncap, nlook, nquant);
    // (L4 NESTED) the preservation/consume chain is genuinely nested-typed; the
    // depth-1 STATIC package embeds into it. The ENTRY (LiftInitCNested) remains
    // depth-1 — its `WalkPairLk` uses the depth-1 `EL.PikeLkActions` (positive
    // look bodies must be look-free); a recursive walk tower is the residual
    // sub-brick, so this endpoint keeps `StaticOkRE` and bridges for the sweep.
    PSM.StaticOkRENestedFromRE(qm, re, code, endl);
    var bestT := LiftFindMatchCNested(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                      PT.PikeTreeInitialState(tstar, inp),
                                      PT.PikeTreeInitialState(tcan, inp),
                                      vms, cdn, ncap, nlook, nquant);
    // bestT IS the canonical tree's first leaf ...
    PikeSubtreeLkEraseIff(t);
    PikeSubtreeLkEraseIff(tcan);
    assert PTL.PikeSubtreeLk(tcan);
    PTL.PikeTreeLkComputesFirstLeaf(tcan, inp, bestT);
    assert bestT == LT.FirstLeaf(tcan, inp);
    // ... which is the RAW entry tree's first leaf (Progress is leaf-transparent)
    assert CE.LeavesAgree(tcan, t) by {
      forall gm: LG.GroupMap, xinp: LC.Input, dr: WP.Direction
        ensures LT.TreeLeaves(tcan, gm, xinp, dr) == LT.TreeLeaves(t, gm, xinp, dr)
      {
        ProgEraseLeavesEq(tcan, gm, xinp, dr);
        ProgEraseLeavesEq(t, gm, xinp, dr);
      }
    }
    CE.LAFirstLeaf(tcan, t, inp);
    assert LT.FirstLeaf(t, inp) == bestT;
  }

  lemma LiftDropDeadHeadLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                              crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                              bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                              vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires |bst.active| > 0
    requires PTL.TreeBfsStepLk(bst.active[0].0, bst.active[0].1, bst.inp) == PT.StepActive([])
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.PikeTreeStepLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // pts_active with an empty successor list: the branch dies on both sides.
    bst1 := PT.PTS(inp, ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert [] + ta[1..] == ta[1..];
    assert PTL.PikeTreeStepLk(bst, bst1);

    // bookkeeping at the successor
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                           ncap, nlook, nquant);
    assert vms2.active == s.active[1..];
  }

  lemma LiftPreserveSkipLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                              crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                              bst: PT.PikeTreeState, s: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    ensures PTL.PikeTreeStepLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, s.(active := s.active[1..]),
                       ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;

    // The processed slot resolves LEFT: the stutter escape would need
    // StutterChainTo(pc, pc), impossible in tame code.
    assert AI.bpc_mem(s.processed, pc, ea);
    assert (exists t': LT.Tree :: SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, ea))
           || (TT.StuttersRE(pc, code)
               && exists t': LT.Tree ::
                 PIV.StutterChainTo(code, pc, pc) && Some(t) == Some(t')
                 && TreeRepLkRE(rer, qm, code, inp, t', pc, ea));
    if !(exists t': LT.Tree :: SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, ea)) {
      PIV.NoStutterCycle(code, pc);
      assert false;
    }
    var t': LT.Tree :| SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, ea);
    TreeRepLkDetermRE(rer, qm, code, inp, t, t', pc, ea);
    assert SS.Inseen(seen, t);

    // pts_skip
    bst1 := PT.PTS(inp, ta[1..], best, tb, seen);
    assert PTL.PikeTreeStepLk(bst, bst1);

    // invariant at the successor
    SkipSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc,
                  PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(s.active[1..]));
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                           ncap, nlook, nquant);
  }

  lemma LiftPreserveStutterLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                 crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                 bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState, th': AI.Thread,
                                 vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires (exists x: int ::
                NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Jmp(x))
                && th' == s.active[0].(pc := x))
             || (NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.BeginLoop)
                 && th' == s.active[0].(exit_allowed := false, pc := s.active[0].pc + 1))
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);

    // the relocated head pairing
    var pc': nat;
    if exists x: int :: NR.GetPcRE(code, pc) == Some(RB.Jmp(x)) && th' == th.(pc := x) {
      var x: int :| NR.GetPcRE(code, pc) == Some(RB.Jmp(x)) && th' == th.(pc := x);
      TreeRepLkREAtJmp(rer, qm, code, inp, t, pc, ea, x);
      WalkPairLkAtJmpRec(rer, qm, code, inp, traw, gm, pc, ea, x);
      pc' := x as nat;
      assert PIV.StutterSuccIs(code, pc, pc');
    } else {
      TreeRepLkREAtBeginLoop(rer, qm, code, inp, t, pc, ea);
      WalkPairLkAtBeginLoopRec(rer, qm, code, inp, traw, gm, pc, ea);
      pc' := pc + 1;
      assert PIV.StutterSuccIs(code, pc, pc');
    }
    assert th'.pc == pc' as int;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc', th'.exit_allowed);
    assert WalkPairLkRec(rer, qm, code, inp, traw, gm, pc', th'.exit_allowed);
    assert th'.capture_regs == th.capture_regs && th'.look_regs == th.look_regs
           && th'.quant_regs == th.quant_regs;
    assert GmtTieOutside(re, th', gm, S);
    assert ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th', ncap, nlook, nquant);
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th', ncap, nlook, nquant);

    // active: same (tree, gm) list against the relocated head
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                           ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ta == [ta[0]] + ta[1..];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, vms2.active, ncap, nlook, nquant);

    // seen: the escape chain extends by one stutter step
    assert TT.StuttersRE(pc, code);
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    StutterSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea, pc');
    assert PIV.HeadPcOf(vms2.active) == pc';
  }

  lemma LiftPreserveAcceptLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Accept)
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [], bestmatch := Some(s.active[0]))
    ensures PTL.PikeTreeStepLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    TreeRepLkREAtAccept(rer, qm, code, inp, t, pc, ea);
    assert t == LT.Match;
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepMatch;

    // pts_match
    bst1 := PT.PTS(inp, [], Some((inp, gm)), tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);

    // the value tie for the recorded best — straight from the head's payload
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    assert GmtTieOutside(re, th, gm, S);
    // (D3) the head's `*Top` carriers feed the best-match tie's `*Top` conjuncts.
    assert LookNestRepCTop(re, S, ta, s.active);
    assert LookNestBackRepCTop(re, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert LookNestOkTTop(re, S, gm, th);
    assert LookNestBackTTop(re, crv, str, ov, S, gm, th, ncap, nlook, nquant);
    // (R2 DEEP CARRIER) the head's deep carrier feeds the best-match tie's deep conjunct.
    assert LookNestBackRepCTopDeep(rer, re, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert LookNestBackTTopDeep(rer, re, crv, str, ov, S, gm, th, ncap, nlook, nquant);
    assert BestTieLkNestedTop(rer, re, crv, str, ov, S, Some((inp, gm)), vms2.bestmatch, ncap, nlook, nquant);

    // bookkeeping: seen grows with the memoized head; active empty both sides
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, [], vms2.active, ncap, nlook, nquant);
  }

  lemma LiftPreserveConsumeAddLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                    crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                    bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                    ce: RC.char_expectation, vms2: AI.VmState,
                                    ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Consume(ce))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires !AI.pc_mem(s1.isblocked, s.active[0].pc)
    requires vms2 == s1.(blocked := [(s.active[0], ce)] + s1.blocked,
                     isblocked := AI.pc_add(s1.isblocked, s.active[0].pc),
                     active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    TreeRepLkREAtConsume(rer, qm, code, inp, t, pc, ea, ce);

    // shared list bookkeeping
    PSM.ReversePrepend((th, ce), s.blocked);
    PSM.MatchingBlockedSnoc(LC.Reverse(s.blocked), (th, ce), inp);

    // the new isblocked entry pc is covered by the freshly-seen head tree
    assert IsblockedRepLk(rer, qm, code, inp, SS.AddSeenTrees(seen, t), vms2.isblocked) by {
      forall pc0: nat | AI.pc_mem(vms2.isblocked, pc0)
        ensures exists t0: LT.Tree, b0: bool ::
                  SS.Inseen(SS.AddSeenTrees(seen, t), t0) && TreeRepLkRE(rer, qm, code, inp, t0, pc0, b0)
      {
        PIV.PcAddMemFwd(s1.isblocked, th.pc, pc0);
        if pc0 == pc {
          SS.InAdd(seen, t, t);
          assert SS.Inseen(SS.AddSeenTrees(seen, t), t) && TreeRepLkRE(rer, qm, code, inp, t, pc0, ea);
        } else {
          assert AI.pc_mem(s.isblocked, pc0);
          var t0: LT.Tree, b0: bool :| SS.Inseen(seen, t0) && TreeRepLkRE(rer, qm, code, inp, t0, pc0, b0);
          SS.InAdd(seen, t0, t);
        }
      }
    }

    if AR.ReadCharE(ce, inp).Some? {
      // MATCHING: pts_blocked pairs the appended entries.
      var (c, nextinp0) := AR.ReadCharE(ce, inp).value;
      assert t.Read? && t.c == c
             && TreeRepLkRE(rer, qm, code, nextinp0, t.t, pc + 1, true);
      assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepBlocked(t.t);
      bst1 := PT.PTS(inp, ta[1..], best, tb + [(t.t, gm)], SS.AddSeenTrees(seen, t));
      assert PTL.PikeTreeStepLk(bst, bst1);
      TrcLkRefl(bst1);
      TrcLkCons(bst, bst1, bst1);

      // the raw child witness for the blocked pair: the head's raw witness
      // reads the same character (erasure pins the Read root)
      var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                           && ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
      assert WalkPairLkRec(rer, qm, code, inp, traw, gm, pc, ea);
      WalkPairLkAtConsumeRec(rer, qm, code, inp, traw, gm, pc, ea, ce);
      assert traw.Read? by {
        if !traw.Read? {
          assert traw == LT.Mismatch;
          assert CE.ProgErase(traw) == LT.Mismatch;
          assert CE.ProgErase(t).Read?;
          assert false;
        }
      }
      var nextinpw: LC.Input :| AR.ReadCharE(ce, inp) == Some((traw.c, nextinpw))
                                && WalkPairLkRec(rer, qm, code, nextinpw, traw.t, gm, pc + 1, true);
      assert traw.c == c && nextinpw == nextinp0;    // ReadCharE is a function
      assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
        assert CE.ProgErase(traw) == LT.Read(traw.c, CE.ProgErase(traw.t));
        assert CE.ProgErase(t) == LT.Read(t.c, CE.ProgErase(t.t));
      }

      // blocked correspondence: the filter gains exactly the new pair
      forall nextinp | LC.AdvanceInput(inp, WP.Forward) == Some(nextinp)
        ensures BlockedRepLkCRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tb + [(t.t, gm)],
                                 PIV.MatchingBlocked(LC.Reverse(vms2.blocked), inp), ncap, nlook, nquant)
      {
        assert nextinp == nextinp0;
        assert PIV.MatchingBlocked(LC.Reverse(vms2.blocked), inp)
            == PIV.MatchingBlocked(LC.Reverse(s.blocked), inp) + [(th, ce)];
        assert GmtTieOutside(re, th, gm, S);
        BlockedRepLkCSnocRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tb,
                             PIV.MatchingBlocked(LC.Reverse(s.blocked), inp), (t.t, gm), (th, ce),
                             ncap, nlook, nquant);
      }
      assert |inp.next| > 0;                          // ReadCharE Some
      assert LC.AdvanceInput(inp, WP.Forward).Some?;

      AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                   PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
      assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                             ncap, nlook, nquant);
      assert vms2.active == s.active[1..];
    } else {
      // MISMATCH: the tree is Mismatch and dies; the doomed blocked thread is
      // invisible to the filter.
      assert t == LT.Mismatch;
      assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([]);
      bst1 := PT.PTS(inp, ta[1..], best, tb, SS.AddSeenTrees(seen, t));
      assert [] + ta[1..] == ta[1..];
      assert PTL.PikeTreeStepLk(bst, bst1);
      TrcLkRefl(bst1);
      TrcLkCons(bst, bst1, bst1);

      assert PIV.MatchingBlocked(LC.Reverse(vms2.blocked), inp)
          == PIV.MatchingBlocked(LC.Reverse(s.blocked), inp);

      AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                   PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
      assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                             ncap, nlook, nquant);
      assert vms2.active == s.active[1..];
    }
  }

  lemma LiftPreserveConsumeDropLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                     crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                     bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                     ce: RC.char_expectation, vms2: AI.VmState,
                                     ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Consume(ce))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires AI.pc_mem(s1.isblocked, s.active[0].pc)
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // the blocked pc's memoized canonical tree IS the head's — the Consume
    // rules are flag-independent, so the recorded flag transfers.
    assert IsblockedRepLk(rer, qm, code, inp, seen, s.isblocked);
    assert AI.pc_mem(s.isblocked, th.pc) && th.pc == pc as int;
    assert AI.pc_mem(s.isblocked, pc);
    var t': LT.Tree, b': bool :| SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, b');
    TreeRepLkREAtConsume(rer, qm, code, inp, t', pc, b', ce);
    assert TreeRepLkRE(rer, qm, code, inp, t', pc, ea) by {
      match AR.ReadCharE(ce, inp) {
        case None =>
    assert t' == LT.Mismatch;      // tr_readfail — flag-independent
        case Some(pair) =>
    assert t'.Read? && t'.c == pair.0
           && TreeRepLkRE(rer, qm, code, pair.1, t'.t, pc + 1, true);   // tr_read — flag-independent
      }
    }
    TreeRepLkDetermRE(rer, qm, code, inp, t, t', pc, ea);
    assert SS.Inseen(seen, t);

    // pts_skip
    bst1 := PT.PTS(inp, ta[1..], best, tb, seen);
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // bookkeeping: the new processed slot's tree is already memoized
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    SeenAddProcessedSlotRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                              PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                           ncap, nlook, nquant);
    assert vms2.active == s.active[1..];
  }

  lemma LiftPreserveSetRegLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                reg: int, th': AI.Thread, vms2: AI.VmState,
                                ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.SetRegisterToCP(reg))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(capture_regs := AReg.set_reg(s.active[0].capture_regs, reg, Some(s1.cp), s1.clock),
                    pc := s.active[0].pc + 1)
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    // the value-tie boundary: SetReg gids are outside-look, hence outside S
    requires S == PIV.CapIdsInLooks(re)
    requires reg >= 0 && 0 <= s1.cp
    // (E3) freshness feed for the look-path carrier (from PikeInvFullRE's BBOf)
    requires s.clock >= 0 && CM.ThreadClocksLE(s.active[0], s.clock)
    // the register-level gm effect, supplied by the dispatcher from machine A's
    // proven step helpers (OpenStepThreadRE/CloseStepThreadRE)
    requires PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs)
          == (if reg % 2 == 0
              then LG.GMOpen(s1.cp as nat, (reg / 2) as nat,
                             PIV.GmOfLive(re, s.active[0].capture_regs, s.active[0].look_regs,
                                          s.active[0].quant_regs))
              else LG.GMClose(s1.cp as nat, (reg / 2) as nat,
                              PIV.GmOfLive(re, s.active[0].capture_regs, s.active[0].look_regs,
                                           s.active[0].quant_regs)))
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // canonical head: GroupActionT(Open/Close) with canonical child at (pc+1, ea)
    TreeRepLkREAtSetReg(rer, qm, code, inp, t, pc, ea, reg);
    assert t.GroupActionT? && (t.g.Open? || t.g.Close?);
    assert TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);
    var gid: LG.GroupId := t.g.g;

    // position: the B-side update index IS the VM's cp
    assert 0 <= s.cp <= |str| && inp == PIV.InpOfCp(str, s.cp);
    PIV.IdxInpOfCp(str, s.cp);
    var cpn: nat := s1.cp as nat;
    assert LC.Idx(inp) == cpn;
    var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);

    // the written gid is outside-look, hence outside S
    assert pc < endl by {
      TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
      assert pc < |code| == endl + 1;
      if pc == endl {
        assert NR.GetPcRE(code, pc) == Some(RB.Accept);
        assert false;
      }
    }
    var OL := PIV.CapIdsOutsideLooks(re);
    PIV.CaptureWriteIdsOutsideRENested(re, code, 0, endl, pc);
    assert reg in PIV.CaptureRegsSet(OL);
    assert gid in OL by {
      if t.g.Open? { assert reg == CP.start_reg(gid as int) == 2 * (gid as int); }
      else { assert reg == CP.end_reg(gid as int) == 2 * (gid as int) + 1; }
      if reg in (set cid: nat | cid in OL :: CP.start_reg(cid)) {
        var cid: nat :| cid in OL && reg == CP.start_reg(cid);
        assert reg == 2 * (cid as int);
        assert t.g.Open?;                              // parity
        assert cid == gid;
      } else {
        var cid: nat :| cid in OL && reg == CP.end_reg(cid);
        assert reg == 2 * (cid as int) + 1;
        assert t.g.Close?;                             // parity
        assert cid == gid;
      }
    }
    PIV.CapIdsLooksDisjoint(re);
    assert gid !in S by {
      if gid in PIV.CapIdsInLooks(re) { assert gid in OL * PIV.CapIdsInLooks(re); }
    }

    // B step: pts_active queues the child with the GMUpdate-moved gm
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm2)]);
    bst1 := PT.PTS(inp, [(t.t, gm2)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // raw witness: its walk peels the same GroupActionT (same reg pins the
    // same action via the erasure congruence), child walks at gm2
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtSetRegRec(rer, qm, code, inp, traw, gm, pc, ea, reg);
    assert traw.GroupActionT?;
    assert traw.g == t.g && CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == LT.GroupActionT(traw.g, CE.ProgErase(traw.t));
      assert CE.ProgErase(t) == LT.GroupActionT(t.g, CE.ProgErase(t.t));
    }
    assert WalkPairLkRec(rer, qm, code, inp, traw.t, gm2, pc + 1, ea);

    // value ties for th': both sides move by the SAME GMUpdate at cpn
    var gml := PIV.GmOfLive(re, th.capture_regs, th.look_regs, th.quant_regs);
    var gml2 := PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs);
    assert gml2 == LG.GMUpdate(t.g, cpn, gml) by {
      if t.g.Open? {
        assert reg == 2 * (gid as int);
        assert reg % 2 == 0 && (reg / 2) as nat == gid;
      } else {
        assert reg == 2 * (gid as int) + 1;
        assert reg % 2 == 1 && (reg / 2) as nat == gid;
      }
    }
    assert gm2 == LG.GMUpdate(t.g, cpn, gm);
    assert GmtTieOutside(re, th, gm, S);

    assert GmtTieOutside(re, th', gm2, S) by {
      forall g: LG.GroupId | g !in S
        ensures (g in gm2 <==> g in gml2) && (g in gm2 ==> gm2[g] == gml2[g])
      {
        assert (g in gm <==> g in gml) && (g in gm ==> gm[g] == gml[g]);
        if g == gid {
          if t.g.Close? {
            // GMClose reads the incoming entry — it agrees on both sides
            assert (gid in gm <==> gid in gml) && (gid in gm ==> gm[gid] == gml[gid]);
          }
        }
        // g != gid: GMUpdate touches only gid, both maps unchanged at g
      }
    }
    assert th'.look_regs == th.look_regs && th'.quant_regs == th.quant_regs;
    assert (th.pc + 1) as nat == pc + 1;
    assert ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm2, th', ncap, nlook, nquant);
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm2, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                           ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm2)] + ta[1..])[0] == (t.t, gm2) && ([(t.t, gm2)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                           ncap, nlook, nquant);

    // ---- (E3) the look-path carrier: fresh cap stamp, no new inside-S group ----
    assert LookNestRepCTop(re, S, ta, s.active);
    assert LookNestOkTTop(re, S, gm, th);
    var Bc := s1.clock;
    assert forall k :: AI.get_idx(th.quant_regs.a_clk, k) <= Bc by {
      assert CM.RegsClocksLE(th.quant_regs, s.clock);
    }
    assert forall j: int ::
        AI.get_idx(th'.capture_regs.a_clk, j) == AI.get_idx(th.capture_regs.a_clk, j)
        || (AI.get_idx(th'.capture_regs.a_clk, j) >= 0 && AI.get_idx(th'.capture_regs.a_clk, j) >= Bc)
    by {
      RL.ASetLaws(th.capture_regs, reg, Some(s1.cp), s1.clock);
    }
    assert forall g: LG.GroupId :: g in S && g in gm2 ==> g in gm by {
      forall g: LG.GroupId | g in S && g in gm2 ensures g in gm {
        assert g != gid;
      }
    }
    LookNestOkTFreshCapTop(re, S, gm, gm2, th, th', Bc);
    assert LookNestRepCTop(re, S, [(t.t, gm2)] + ta[1..], vms2.active) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestOkTTop(re, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i])
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    // ---- (E4) the converse carrier: look/quant banks untouched, gm grows ----
    assert LookNestBackRepCTop(re, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert forall g: LG.GroupId :: g in gm ==> g in gm2;   // GMOpen adds / GMClose keeps domain
    LookNestBackTRegSameTop(re, crv, str, ov, S, gm, gm2, th, th', ncap, nlook, nquant);
    assert LookNestBackRepCTop(re, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                               ncap, nlook, nquant) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestBackTTop(re, crv, str, ov, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i],
                                 ncap, nlook, nquant)
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    // ---- (E4 DEEP) the deep carrier: register-inert (inside-S regions verbatim) ----
    assert LookNestBackRepCTopDeep(rer, re, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert forall g: LG.GroupId :: g in S ==>
                                     ((g in gm <==> g in gm2) && (g in gm ==> gm2[g] == gm[g]))
    by {
      forall g: LG.GroupId | g in S
        ensures (g in gm <==> g in gm2) && (g in gm ==> gm2[g] == gm[g])
      {
        assert g != gid;                       // SetReg gids are outside S
        // GMOpen/GMClose are single-key updates at gid
      }
    }
    LookNestBackTRegSameTopDeep(rer, re, crv, str, ov, S, gm, gm2, th, th', ncap, nlook, nquant);
    assert LookNestBackRepCTopDeep(rer, re, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                                   ncap, nlook, nquant) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestBackTTopDeep(rer, re, crv, str, ov, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i],
                                     ncap, nlook, nquant)
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm2)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  lemma LiftPreserveSetQuantLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                  crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                  bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                  q: int, bq: bool, th': AI.Thread, vms2: AI.VmState,
                                  ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.SetQuantToClock(q, bq))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(quant_regs := AReg.set_reg(s.active[0].quant_regs, q,
                                                            if bq then Some(s1.cp) else None, s1.clock),
                    pc := s.active[0].pc + 1)
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    // the register-level gm effect, supplied by the dispatcher from machine A's
    // proven step helper (ResetStepThreadRE); q's table binding rides along
    requires q in qm.quants
    // (E3) look-id uniqueness (cross-lid ownership pinning for the carrier)
    requires LTB.LookUnique(re)
    // (E4) converse-carrier feeds
    requires PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires CM.ThreadRegsWf(s.active[0], ncap, nlook, nquant)
    requires s.clock >= 0 && CM.ThreadClocksLE(s.active[0], s.clock)
    requires PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs)
          == LG.GMReset(qm.quants[q],
                        PIV.GmOfLive(re, s.active[0].capture_regs, s.active[0].look_regs,
                                     s.active[0].quant_regs))
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // canonical head: Reset(qm.quants[q]) with canonical child at (pc+1, ea) —
    // the clock-mark AND (§2.5b F-c) the nulled-exit stamp, a plain Reset on the B side
    TreeRepLkREAtSetQuant(rer, qm, code, inp, t, pc, ea, q, bq);
    var gidl := qm.quants[q];
    assert t.GroupActionT? && t.g == LG.Reset(gidl);
    assert TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);

    var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);
    assert gm2 == LG.GMReset(gidl, gm);

    // B step: pts_active queues the child with the Reset-moved gm
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm2)]);
    bst1 := PT.PTS(inp, [(t.t, gm2)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // raw witness: same Reset head via the SetQuant walk wrapper
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtSetQuantRec(rer, qm, code, inp, traw, gm, pc, ea, q, bq);
    assert traw.GroupActionT? && traw.g == LG.Reset(gidl) == t.g;
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == LT.GroupActionT(traw.g, CE.ProgErase(traw.t));
      assert CE.ProgErase(t) == LT.GroupActionT(t.g, CE.ProgErase(t.t));
    }
    assert WalkPairLkRec(rer, qm, code, inp, traw.t, gm2, pc + 1, ea);

    // value ties: both maps shed the SAME set(gidl); everything else unchanged
    var gml := PIV.GmOfLive(re, th.capture_regs, th.look_regs, th.quant_regs);
    var gml2 := PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs);
    assert gml2 == LG.GMReset(gidl, gml);
    assert GmtTieOutside(re, th, gm, S);

    assert GmtTieOutside(re, th', gm2, S) by {
      forall g: LG.GroupId | g !in S
        ensures (g in gm2 <==> g in gml2) && (g in gm2 ==> gm2[g] == gml2[g])
      {
        assert (g in gm <==> g in gml) && (g in gm ==> gm[g] == gml[g]);
      }
    }
    assert th'.look_regs == th.look_regs;
    assert (th.pc + 1) as nat == pc + 1;
    assert ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm2, th', ncap, nlook, nquant);
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm2, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                           ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm2)] + ta[1..])[0] == (t.t, gm2) && ([(t.t, gm2)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                           ncap, nlook, nquant);

    // ---- (E3) the look-path carrier: the Reset vacates on-path lids ----
    assert LookNestRepCTop(re, S, ta, s.active);
    assert LookNestOkTTop(re, S, gm, th);
    assert pc < endl by {
      TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
      assert pc < |code| == endl + 1;
      if pc == endl { assert NR.GetPcRE(code, pc) == Some(RB.Accept); assert false; }
    }
    PIV.QuantWriteIdsRENested(re, code, 0, endl, pc);
    assert q >= 0 && (q as nat) in PIV.QuantIds(re);
    var qn: nat := q as nat;
    M.TransWfQidBody(re, qn);
    QmapOkAtQid(re, qm, qn);
    assert gidl == L.DefGroups(T.Translate(PIV.QidBody(re, qn)));
    M.TranslateDefGroupsEqCapIds(PIV.QidBody(re, qn));
    assert forall g: nat :: g in PIV.CapIds(PIV.QidBody(re, qn)) ==> g !in gm2 by {
      forall g: nat | g in PIV.CapIds(PIV.QidBody(re, qn)) ensures g !in gm2 {
        assert g in (set gx | gx in L.DefGroups(T.Translate(PIV.QidBody(re, qn))));
        assert g in gidl;                        // seq membership via the set identity
      }
    }
    assert forall g: LG.GroupId :: g in gm2 ==> g in gm;   // GMReset only removes
    assert forall j: int :: j != q ==>
                              AI.get_idx(th'.quant_regs.a_clk, j) == AI.get_idx(th.quant_regs.a_clk, j)
    by { RL.ASetLaws(th.quant_regs, q, if bq then Some(s1.cp) else None, s1.clock); }
    LookNestOkTSetQuantTop(re, S, gm, gm2, th, th', qn);
    assert LookNestRepCTop(re, S, [(t.t, gm2)] + ta[1..], vms2.active) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestOkTTop(re, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i])
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    // ---- (E4) converse: on-path dominance breaks; off-path scopes disjoint ----
    assert LookNestBackRepCTop(re, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert 0 <= q < nquant by {
      NI.QuantIdsLEMaxQuant(re);
      assert (q as nat) <= R.max_quant(re);
    }
    assert AI.get_idx(th'.quant_regs.a_clk, q) == s1.clock by {
      assert |th.quant_regs.a_clk| == nquant;
      RL.ASetLaws(th.quant_regs, q, if bq then Some(s1.cp) else None, s1.clock);
    }
    assert forall j: int :: AI.get_idx(th.look_regs.a_clk, j) < AI.get_idx(th'.quant_regs.a_clk, q as int) by {
      assert CM.RegsClocksLE(th.look_regs, s.clock);
    }
    assert forall g: LG.GroupId :: g in gm && g !in PIV.CapIds(PIV.QidBody(re, qn)) ==> g in gm2 by {
      forall g: LG.GroupId | g in gm && g !in PIV.CapIds(PIV.QidBody(re, qn))
        ensures g in gm2
      {
        assert g !in (set gx | gx in gidl);
        assert g !in gidl;
      }
    }
    LookNestBackTSetQuantNestedTop(re, crv, str, ov, S, gm, gm2, th, th', qn, ncap, nlook, nquant);
    assert LookNestBackRepCTop(re, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                               ncap, nlook, nquant) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestBackTTop(re, crv, str, ov, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i],
                                 ncap, nlook, nquant)
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    // ---- (E4 DEEP) the deep carrier: off-path SetQuant re-stamp (same shape) ----
    assert LookNestBackRepCTopDeep(rer, re, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert forall g: LG.GroupId :: g in S && g !in PIV.CapIds(PIV.QidBody(re, qn)) ==>
                                     ((g in gm <==> g in gm2) && (g in gm ==> gm2[g] == gm[g]))
    by {
      forall g: LG.GroupId | g in S && g !in PIV.CapIds(PIV.QidBody(re, qn))
        ensures (g in gm <==> g in gm2) && (g in gm ==> gm2[g] == gm[g])
      {
        assert g !in (set gx | gx in gidl);
        assert g !in gidl;
        // GMReset is map-domain subtraction: off-list entries survive verbatim
      }
    }
    LookNestBackTSetQuantNestedTopDeep(rer, re, crv, str, ov, S, gm, gm2, th, th', qn, ncap, nlook, nquant);
    assert LookNestBackRepCTopDeep(rer, re, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                                   ncap, nlook, nquant) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestBackTTopDeep(rer, re, crv, str, ov, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i],
                                     ncap, nlook, nquant)
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm2)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  lemma LiftPreserveForkLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                              crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                              bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                              x: int, y: int, vms2: AI.VmState,
                              ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Fork(x, y))
    // backward-fork flag pin (the dispatcher discharges it from EaColdOkRE)
    requires (x <= s.active[0].pc || y <= s.active[0].pc) ==> s.active[0].exit_allowed
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [AI.Thread(x, s.active[0].capture_regs, s.active[0].look_regs,
                                              s.active[0].quant_regs, s.active[0].exit_allowed),
                                    s.active[0].(pc := y)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tbl, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    TreeRepLkREAtFork(rer, qm, code, inp, t, pc, ea, x, y);
    assert x >= 0 && y >= 0;
    var th1 := AI.Thread(x, th.capture_regs, th.look_regs, th.quant_regs, ea);
    var th2 := th.(pc := y);
    assert vms2.active == [th1, th2] + s.active[1..];

    // raw witness + its arms (erased-Choice existential)
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtForkArmsRec(rer, qm, code, inp, traw, gm, pc, ea, x, y);

    // value ties carry: both arm threads keep th's registers
    assert GmtTieOutside(re, th, gm, S);
    assert th1.capture_regs == th.capture_regs && th1.look_regs == th.look_regs
           && th1.quant_regs == th.quant_regs;
    assert GmtTieOutside(re, th1, gm, S);
    assert GmtTieOutside(re, th2, gm, S);

    if x as nat > pc && y as nat > pc {
      // ---- FORWARD: canonical Choice; one B step -------------------------
      assert t.Choice?
             && TreeRepLkRE(rer, qm, code, inp, t.t1, x as nat, ea)
             && TreeRepLkRE(rer, qm, code, inp, t.t2, y as nat, ea);
      assert CE.ProgErase(traw) == LT.Choice(CE.ProgErase(t.t1), CE.ProgErase(t.t2));
      assert CE.ProgErase(traw) != LT.Mismatch;
      var ta1: LT.Tree, ta2: LT.Tree :|
        CE.ProgErase(traw) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
        && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ea)
        && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ea);
      assert CE.ProgErase(ta1) == CE.ProgErase(t.t1) && CE.ProgErase(ta2) == CE.ProgErase(t.t2);
      assert th1.pc >= 0 && th2.pc >= 0;
      assert ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, ta1, gm, th1, ncap, nlook, nquant);
      assert ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, ta2, gm, th2, ncap, nlook, nquant);
      assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t.t1, gm, th1, ncap, nlook, nquant);
      assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t.t2, gm, th2, ncap, nlook, nquant);

      var na := [(t.t1, gm), (t.t2, gm)];
      assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive(na);
      bst1 := PT.PTS(inp, na + ta[1..], best, tbl, SS.AddSeenTrees(seen, t));
      assert PTL.PikeTreeStepLk(bst, bst1);
      TrcLkRefl(bst1);
      TrcLkCons(bst, bst1, bst1);

      assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                             ncap, nlook, nquant);
      assert (na + ta[1..])[0] == (t.t1, gm) && (na + ta[1..])[1..] == [(t.t2, gm)] + ta[1..];
      assert ([(t.t2, gm)] + ta[1..])[0] == (t.t2, gm) && ([(t.t2, gm)] + ta[1..])[1..] == ta[1..];
      assert vms2.active[0] == th1 && vms2.active[1..] == [th2] + s.active[1..];
      assert ([th2] + s.active[1..])[0] == th2 && ([th2] + s.active[1..])[1..] == s.active[1..];
      assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, na + ta[1..], vms2.active,
                             ncap, nlook, nquant);

      assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
      AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                   PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
      IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
    } else {
      // ---- BACKWARD (do-while): ea pinned; TWO B steps -------------------
      assert ea;
      assert t.Progress? && t.t.Choice?
             && TreeRepLkRE(rer, qm, code, inp, t.t.t1, x as nat, true)
             && TreeRepLkRE(rer, qm, code, inp, t.t.t2, y as nat, true);
      assert CE.ProgErase(t) == LT.Choice(CE.ProgErase(t.t.t1), CE.ProgErase(t.t.t2));
      assert CE.ProgErase(traw) != LT.Mismatch;
      var ta1: LT.Tree, ta2: LT.Tree :|
        CE.ProgErase(traw) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
        && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ea)
        && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ea);
      assert CE.ProgErase(ta1) == CE.ProgErase(t.t.t1) && CE.ProgErase(ta2) == CE.ProgErase(t.t.t2);
      assert th1.pc >= 0 && th2.pc >= 0 && th1.exit_allowed && th2.exit_allowed;
      assert ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, ta1, gm, th1, ncap, nlook, nquant);
      assert ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, ta2, gm, th2, ncap, nlook, nquant);
      assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t.t.t1, gm, th1, ncap, nlook, nquant);
      assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t.t.t2, gm, th2, ncap, nlook, nquant);

      var mta := [(t.t, gm)] + ta[1..];
      assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm)]);
      var mid := PT.PTS(inp, mta, best, tbl, SS.AddSeenTrees(seen, t));
      assert PTL.PikeTreeStepLk(bst, mid);
      var na := [(t.t.t1, gm), (t.t.t2, gm)];
      assert mta[0] == (t.t, gm) && mta[1..] == ta[1..];
      assert PTL.TreeBfsStepLk(t.t, gm, inp) == PT.StepActive(na);
      bst1 := PT.PTS(inp, na + ta[1..], best, tbl,
                     SS.AddSeenTrees(SS.AddSeenTrees(seen, t), t.t));
      assert PTL.PikeTreeStepLk(mid, bst1);
      TrcLkRefl(bst1);
      TrcLkCons(mid, bst1, bst1);
      TrcLkCons(bst, mid, bst1);

      assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                             ncap, nlook, nquant);
      assert (na + ta[1..])[0] == (t.t.t1, gm) && (na + ta[1..])[1..] == [(t.t.t2, gm)] + ta[1..];
      assert ([(t.t.t2, gm)] + ta[1..])[0] == (t.t.t2, gm) && ([(t.t.t2, gm)] + ta[1..])[1..] == ta[1..];
      assert vms2.active[0] == th1 && vms2.active[1..] == [th2] + s.active[1..];
      assert ([th2] + s.active[1..])[0] == th2 && ([th2] + s.active[1..])[1..] == s.active[1..];
      assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, na + ta[1..], vms2.active,
                             ncap, nlook, nquant);

      assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
      AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                   PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
      SeenGrowSeenRepLk(rer, qm, code, inp, SS.AddSeenTrees(seen, t),
                        AI.bpc_add(s.processed, th.pc, ea), t.t,
                        PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
      IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
      IsblockedGrowLk(rer, qm, code, inp, SS.AddSeenTrees(seen, t), s.isblocked, t.t);
    }
  }

  lemma LiftPreserveGatePassLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                                        crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                                        bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                                        l: int, th': AI.Thread, vms2: AI.VmState,
                                                        ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires |ov| == |str| + 1                                    // L3b: the backward LB gate needs the mirror
    requires OE.OracleColsOk(rer, qm, str)                    // (L5 F7d) whole-string oracle correctness (backward keystone)
    requires S == PIV.CapIdsInLooks(re)
    // (BRICK D5) NON-VACUITY FLIP: the driver's per-lid static package is the
    // depth-AGNOSTIC `GateStaticsOkNested` (nested gate bodies), qualified by the
    // positive-lookahead-nesting scope `M.NoPosLookbehindRE(re)` — the composite
    // sim is now non-vacuous at nesting depth >= 2.
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires NR.L5ScopeRE(re) && L5ScopeV1RE(re)   // (L5 F7f) v1: kind-split hub
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires CM.ThreadRegsWf(s.active[0], ncap, nlook, nquant)
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.CheckOracle(l))
    requires LOr.view_get_oracle(ov, s.cp, l)
    // (E3) carrier feeds: freshness, positional invariant, look uniqueness
    requires s.clock >= 0 && CM.ThreadClocksLE(s.active[0], s.clock)
    requires PSM.ThreadNestRE(re, code, endl, s.active[0].pc, s.active[0])
    requires LTB.LookUnique(re)
    // (E4) the row↔structure tie for the converse coverage
    requires LTB.LookTablesOk(re, crv)
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(pc := s.active[0].pc + 1,
                    look_regs := AReg.set_reg(s.active[0].look_regs, l, Some(s1.cp), s1.clock))
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    // (L4 NESTED) NestedFragmentRE(re) is now DIRECT from StaticOkNestedRE
    var PTS(inp, ta, best, tbl, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // gate pc interior + polarity pin
    TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
    assert |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept);
    assert pc < endl;
    GatePolarityRE(re, qm, code, 0, endl, pc);
    assert l in qm.looks;
    var lk := qm.looks[l].0;
    var r1 := qm.looks[l].1;
    assert AR.PositiveL(lk) && L.Positivity(lk);

    // position glue
    assert 0 <= s.cp <= |str| && inp == PIV.InpOfCp(str, s.cp);
    var cp: nat := s.cp as nat;
    PIV.IdxInpOfCp(str, cp);
    assert TREP.CpOf(inp) == cp && TR_CpOf(inp) == cp;
    assert LL.OracleOkAt(rer, qm, inp);

    // raw witness at the gate: the walk lemma keys on the (true) oracle bit
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    assert WalkPairLkRec(rer, qm, code, inp, traw, gm, pc, ea);
    WalkPairLkAtCheckOracleRec(rer, qm, code, inp, traw, gm, pc, ea, l);
    assert LOr.view_get_oracle(qm.ov, TR_CpOf(inp), l);
    assert traw.LK? && traw.lk == lk;
    assert EL.LkGateOk(rer, lk, r1, inp, traw.tlk, true);
    var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
    assert traw.tlk == tlk;                                   // LkGateOk pins tlk functionally
    assert LS.LkResult(lk, tlk, LG.Empty, inp).Some?;
    assert LS.LkResult(lk, tlk, gm, inp).Some?;
    var gm2 := LS.LkResult(lk, tlk, gm, inp).value;
    assert WalkPairLkRec(rer, qm, code, inp, traw.t, gm2, pc + 1, ea);
    assert forall gg :: gg in L.DefGroups(r1) ==> gg !in gm;  // the gate's own clear instance

    // canonical head: the LK branch of the gate rule (functional verdict Some)
    TreeRepLkREAtCheckOracle(rer, qm, code, inp, t, pc, ea, l);
    assert t.LK? && t.lk == lk && t.tlk == tlk
           && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);

    // erasure congruence: children tie
    assert CE.ProgErase(traw) == LT.LK(lk, CE.ProgErase(traw.tlk), CE.ProgErase(traw.t));
    assert CE.ProgErase(t) == LT.LK(lk, CE.ProgErase(t.tlk), CE.ProgErase(t.t));
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t);

    // B step on the canonical LK head: pts_active with the merged gm
    assert LS.LkResult(t.lk, t.tlk, gm, inp) == Some(gm2);
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm2)]);
    bst1 := PT.PTS(inp, [(t.t, gm2)] + ta[1..], best, tbl, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // (BRICK D5) the per-lid NESTED static package (off `GateStaticsOkNested`):
    // the gate body may nest positive looks to ANY depth (negative bodies stay
    // look-free, `NR.NegLooksLookFreeRE`; positive nesting is lookAHEAD-only,
    // `M.NoPosLookbehindRE`), with the body's compile statics as `StaticOkNestedRE`.
    assert GateStaticAtNested(qm, re, crv, l, ncap, nlook, nquant);
    var la: R.lookaround, body: R.regex :|
      LTB.LookEntryOk(crv, l, la, body)
      && T.TransWf(body) && NR.NestedFragmentRE(body)
      && NR.NegLooksLookFreeRE(body)
      && qm.looks[l].0 == T.TrLookaround(la)
      && qm.looks[l].1 == T.Translate(body)
      && (set g: LG.GroupId | g in L.DefGroups(T.Translate(body))) <= PIV.CapIdsInLooks(re)
      && var bodycode := CP.compile_to_bytecode(body);
      |bodycode| >= 1
      && PSM.StaticCoreNestedRE(qm, body, bodycode, |bodycode| - 1)
      && PSM.SizesOkRE(body, ncap, nlook, nquant)
      && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
    assert lk == T.TrLookaround(la) && r1 == T.Translate(body);
    assert body == M.VBody(crv, l);
    assert 0 <= l < nlook;

    var clk := s1.clock;
    assert th' == th.(pc := th.pc + 1, look_regs := AReg.set_reg(th.look_regs, l, Some(cp as int), clk));

    // the polarity pin refutes the negative flavours
    assert !la.NegLookahead? && !la.NegLookbehind? by {
      if la.NegLookahead? || la.NegLookbehind? { assert !L.Positivity(lk); }
    }
    // (BRICK D5) `M.NoPosLookbehindRE(re)` forbids a positive LOOKBEHIND at lid l:
    // the functional row (`LTB.LookEntryOk` pins `la == crv.f_look_types[l]`)
    // matches `M.LookBodyFactsNested`'s `!la0.Lookbehind?`. Combined with the
    // polarity pin this leaves ONLY the capturing lookAHEAD arm live.
    PIV.LookCheckIdsRENested(re, code, 0, endl, pc);
    assert l >= 0 && (l as nat) in LTB.LookIds(re);
    NI.LookBodyOfTablesTie(re, crv, l as nat);
    assert body == NI.LookBodyOfRE(re, l as nat);
    assert NR.NoNulledPlusRE(body);   // (§2.5b F-c) the per-lid package carries it (look bodies stay stamp-free)
    // (L5 F7f) the L5 per-lid dispatch: a positive LOOKBEHIND is in scope iff its
    // body is lookbehind-only (`LBOnlyLooksRE`) — the LB arms below consume it.
    assert la.Lookahead? || la.Lookbehind?;
    assert la.Lookbehind? ==> FST.LBOnlyLooksRE(body) by {
      M.LookBodyFactsL5(re, crv, l as nat);
      var la0: R.lookaround :| LTB.LookEntryOk(crv, l as int, la0, NI.LookBodyOfRE(re, l as nat))
                               && (la0.Lookbehind? ==> NR.LBOnlyLooksRE(NI.LookBodyOfRE(re, l as nat)));
      assert la0 == crv.f_look_types[l] == la;   // LookEntryOk pins f_look_types[l]
      if la.Lookbehind? { FG.LBOnlyEquiv(body); }
    }
    M.LkBodyGroupsEqCapIdsInLooks(re);
    assert S == LL.LkBodyGroups(T.Translate(re));

    if la.Lookahead? {
      // ---- capturing-lookahead half: the proven crux core -------------------
      assert crv.f_look_types[l] == la && crv.f_look_types[l].Lookahead?;
      assert AI.capture_type(crv.f_look_types[l]);
      assert L.LkDir(lk) == WP.Forward;
      assert RL.ASize(th.look_regs) == nlook;
      var bodycode := CP.compile_to_bytecode(body);
      assert LT.LK(lk, tlk, traw.t) == traw;
      // (BRICK D5) the gate-step lemma takes the body in the positive-nesting
      // sub-fragment DIRECTLY from the nested package: `NestedFragmentRE(body)` +
      // `NegLooksLookFreeRE(body)` are hypotheses of the package (no LookFree
      // conversions), and the value body-package requires are DROPPED with the call.
      ThreadRepLkStepCheckOracleRec(rer, qm, re, code, crv, str, ov, S, lk, r1, tlk, traw.t,
                                    gm, th, l, cp, clk, body, la, bodycode, |bodycode| - 1, 0,
                                    th.quant_regs, ncap, nlook, nquant);
      assert ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm2, th', ncap, nlook, nquant);
    } else {
      // ---- (L5 F7f) capturing-LOOKBEHIND half: the F6c twin of the gate step ----
      // (every ingredient is direction-generic; only the direction pin differs)
      assert la.Lookbehind?;
      assert crv.f_look_types[l] == la && crv.f_look_types[l].Lookbehind?;
      assert AI.capture_type(crv.f_look_types[l]);
      assert L.LkDir(lk) == WP.Backward;
      assert RL.ASize(th.look_regs) == nlook;
      var bodycode := CP.compile_to_bytecode(body);
      assert LT.LK(lk, tlk, traw.t) == traw;
      ThreadRepLkStepCheckOracleRecLB(rer, qm, re, code, crv, str, ov, S, lk, r1, tlk, traw.t,
                                      gm, th, l, cp, clk, body, la, bodycode, |bodycode| - 1, 0,
                                      th.quant_regs, ncap, nlook, nquant);
      assert ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm2, th', ncap, nlook, nquant);
    }

    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm2, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                           ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm2)] + ta[1..])[0] == (t.t, gm2) && ([(t.t, gm2)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                           ncap, nlook, nquant);

    // ---- (E3) the look-path carrier: the crossing establishes lid l fresh ----
    // (D3) `*Top` carrier: only the TOP-LEVEL gate lid l fires an obligation.
    assert LookNestRepCTop(re, S, ta, s.active);   // (BRICK D5) Rec/Top carrier anchor
    assert LookNestOkTTop(re, S, gm, th);
    assert NI.NestInvRE(re, code, 0, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk, -1) by {
      assert PSM.ThreadNestRE(re, code, endl, th.pc, th);
      assert pc < endl;
    }
    RL.ASetLaws(th.look_regs, l, Some(cp as int), clk);
    assert AI.get_idx(th'.look_regs.a_clk, l) == clk && clk >= 0;
    assert forall k :: AI.get_idx(th.quant_regs.a_clk, k) <= AI.get_idx(th'.look_regs.a_clk, l) by {
      assert CM.RegsClocksLE(th.quant_regs, s.clock);
    }
    assert forall j: int :: j != l ==>
                              AI.get_idx(th'.look_regs.a_clk, j) == AI.get_idx(th.look_regs.a_clk, j);
    // ownership: the fold adds only l-owned groups (LmapOk row + fold confinement)
    PIV.LookCheckIdsRENested(re, code, 0, endl, pc);
    assert l >= 0 && (l as nat) in LTB.LookIds(re);
    LmapOkAtLid(re, qm, l as nat);
    var LB := NI.LookBodyOfRE(re, l as nat);
    assert r1 == T.Translate(LB);
    M.TranslateDefGroupsEqCapIds(LB);
    assert (set gx | gx in L.DefGroups(r1)) == PIV.CapIds(LB);
    // (BRICK D5) the gate body may nest looks: the DEPTH-K outside-S agreement
    // (`LkResultAgreeOutsideNested` on the recursive `PikeLkRegexRec(r1)`) replaces
    // the depth-1 look-free `NoLkBrL(r1)` frame. The fold still writes only
    // `DefGroups(r1)`, so any newly-set S-group of gm2 lies in the gate body.
    assert NR.NoNulledPlusRE(body);   // (§2.5b F-c) the per-lid package carries it (look bodies stay stamp-free)
    EL.TranslateFragmentPikeLkRec(body);
    assert EL.PikeLkRegexRec(r1);
    LkResultAgreeOutsideNested(rer, lk, r1, inp, tlk, gm);
    assert forall g: LG.GroupId :: g in S && g in gm2 && g !in gm ==>
                                     l >= 0 && (l as nat) in LTB.LookIds(re) && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
    by {
      forall g: LG.GroupId | g in S && g in gm2 && g !in gm
        ensures g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
      {
        if g !in (set gx | gx in L.DefGroups(r1)) {
          assert g in gm;                          // GmAgreeOutside membership
          assert false;
        }
      }
    }
    // (D3) fresh folds may land inner-look groups of l's body, but inner looks
    // are NOT in TopLookIds — no obligation. `LookNestOkTGatePassNestedTop` DROPS
    // the DIRECT-ownership hypothesis (cross-lid folds killed by top-level
    // disjointness), so the gate body need NOT be look-free.
    NI.LookBodyOfTablesTie(re, crv, l as nat);       // VBody(crv,l) == LookBodyOfRE(re,l) == body
    LookNestOkTGatePassNestedTop(re, code, endl, S, gm, gm2, th, th', pc, l);
    assert LookNestRepCTop(re, S, [(t.t, gm2)] + ta[1..], vms2.active) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestOkTTop(re, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i])
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    // ---- (E4) converse: the crossing's coverage from the replay↔spec tie ----
    assert LookNestBackRepCTop(re, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    // structural body == row body (both pin f_look_ast[l])
    NI.LookBodyOfTablesTie(re, crv, l as nat);
    var la3: R.lookaround :| LTB.LookEntryOk(crv, l, la3, NI.LookBodyOfRE(re, l as nat));
    assert NI.LookBodyOfRE(re, l as nat) == body;
    // gm only grows across the fold (its S-body keys were CLEAR coming in)
    assert forall g: LG.GroupId :: g in gm ==> g in gm2 by {
      forall g: LG.GroupId | g in gm ensures g in gm2 {
        assert g !in (set gx | gx in L.DefGroups(r1)) by {
          if g in (set gx | gx in L.DefGroups(r1)) { assert g !in gm; }
        }
      }
    }
    // the crossing coverage for l itself
    assert var rfx := M.FreshBodyMatch(crv, str, l, th'.look_regs, ov, ncap, nlook, nquant);
           rfx.Some? ==>
             forall g: LG.GroupId ::
               g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
               && g in PIV.GmOfLive(NI.LookBodyOfRE(re, l as nat), rfx.value.capture_regs,
                                    rfx.value.look_regs, rfx.value.quant_regs)
               ==> g in gm2
    by {
      var rfx := M.FreshBodyMatch(crv, str, l, th'.look_regs, ov, ncap, nlook, nquant);
      if rfx.Some? {
        if la.Lookahead? {
          M.TranslateDefGroupsEqCapIds(body);
          M.LkBodyGroupsEqCapIdsInLooks(body);
          PIV.CapIdsLooksDisjoint(body);
          // (BRICK D5) depth-k gm-independence (recursive PikeLkRegexRec body).
          EL.TranslateFragmentPikeLkRec(body);
          EL.ComputeTrGmIndepLkRec(rer, r1, inp, gm, WP.Forward);
          assert tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], inp, gm, WP.Forward);
          assert M.GmAgreeOn(gm, LG.Empty, set gx | gx in L.DefGroups(r1)) by {
            forall g: LG.GroupId | g in (set gx | gx in L.DefGroups(r1))
              ensures (g in gm <==> g in LG.Empty) && (g in gm ==> gm[g] == LG.Empty[g])
            {
              assert g !in gm;
            }
          }
          var bodycode3 := CP.compile_to_bytecode(body);
          assert AReg.get_cp(th'.look_regs, l) == Some(s1.cp) by {
            RL.ASetLaws(th.look_regs, l, Some(cp as int), clk);
          }
          // (BRICK D5) the NESTED value keystone: agreement on the OUTER groups
          // `Sout = DefGroups(tr) \ LkBodyGroups(tr)` (fresh cap == cap here).
          M.LkReplayMatchesSpecNested(rer, qm, body, bodycode3, |bodycode3| - 1, 0, str, cp,
                                      AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                      ov, LCdn.compile_cdns(body), la, tlk, gm, ncap, nlook, nquant);
          assert crv.f_look_cdns[l] == LCdn.compile_cdns(body);      // LookEntryOk row
          var rfSpec := AI.FFindMatch(bodycode3, str,
                                      AI.FInitState(bodycode3, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                    AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                                      ov, LAnc.Forward, LCdn.compile_cdns(body)).0;
          assert rfx == rfSpec;
          assert LS.LkResult(T.TrLookaround(la), tlk, gm, inp).Some?
                 && LS.LkResult(T.TrLookaround(la), tlk, gm, inp).value == gm2 by {
            assert lk == T.TrLookaround(la);
          }
          var Sout := set gx | gx in L.DefGroups(T.Translate(body))
                               && gx !in LL.LkBodyGroups(T.Translate(body));
          assert M.GmAgreeOn(gm2,
                             PIV.GmOfLive(body, rfSpec.value.capture_regs,
                                          rfSpec.value.look_regs, rfSpec.value.quant_regs),
                             Sout);
          // (BRICK D5) the INNER groups (`LkBodyGroups(tr) == CapIdsInLooks(body)`)
          // are ABSENT from the fresh body match's live denotation — a lookaround
          // compiles to a single CheckOracle leaf, so the fresh match records none
          // of them (`FreshBodyMatchGmOuter`). So the (E4) coverage reduces to the
          // OUTER groups, discharged by `LkReplayMatchesSpecNested`.
          FreshBodyMatchGmOuter(qm, body, bodycode3, |bodycode3| - 1, str, cp, ov,
                                LCdn.compile_cdns(body), ncap, nlook, nquant);
          forall g: LG.GroupId |
            g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
            && g in PIV.GmOfLive(NI.LookBodyOfRE(re, l as nat), rfx.value.capture_regs,
                                 rfx.value.look_regs, rfx.value.quant_regs)
            ensures g in gm2
          {
            assert g in PIV.CapIds(body);                                  // body == LookBodyOfRE(re,l)
            assert g in PIV.GmOfLive(body, rfSpec.value.capture_regs,
                                     rfSpec.value.look_regs, rfSpec.value.quant_regs);  // rfx == rfSpec
            assert g in (set gx | gx in L.DefGroups(T.Translate(body)));   // TranslateDefGroupsEqCapIds
            if g in PIV.CapIdsInLooks(body) {
              // fresh match records no inner-look captures ⇒ contradicts g live
              assert g !in PIV.GmOfLive(body, rfSpec.value.capture_regs,
                                        rfSpec.value.look_regs, rfSpec.value.quant_regs);
              assert false;
            }
            assert g !in LL.LkBodyGroups(T.Translate(body));   // == CapIdsInLooks(body)
            assert g in Sout;                                  // hence g in the OUTER set
          }
        } else {
          // (L5 F7f) capturing-LOOKBEHIND lid: the fresh body match is the BACKWARD
          // run of `reverse_regex(body)` at the recorded cp (`FreshBodyMatchLBUnfold`);
          // F6's crossing coverage `GateCrossCoverageLBNested` lands every live
          // surface group of the body in the passing gate's `LkResult` (inner-look
          // groups are never live in the backward fresh run, F6b).
          assert la.Lookbehind?;
          assert L.LkDir(lk) == WP.Backward;
          EL.TranslateFragmentPikeLkRec(body);
          EL.ComputeTrGmIndepLkRec(rer, r1, inp, gm, WP.Backward);
          assert tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], inp, gm, WP.Backward);
          assert M.GmAgreeOn(gm, LG.Empty, set gx | gx in L.DefGroups(r1)) by {
            forall g: LG.GroupId | g in (set gx | gx in L.DefGroups(r1))
              ensures (g in gm <==> g in LG.Empty) && (g in gm ==> gm[g] == LG.Empty[g])
            {
              assert g !in gm;
            }
          }
          assert AReg.get_cp(th'.look_regs, l) == Some(s1.cp) by {
            RL.ASetLaws(th.look_regs, l, Some(cp as int), clk);
          }
          // site statics of the F6 atom: LB-only body (the L5 dispatch), body-level
          // uniqueness, LmapOk on the body, the whole-string oracle (F7d)
          assert FST.LBOnlyLooksRE(body);
          assert PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body) by {
            M.LookBodyFactsL5(re, crv, l as nat);
          }
          assert AR.LmapOk(body, qm) by { FG.LmapOkLookBody(re, qm, l as nat); }
          assert 0 <= l < |crv.f_look_types| && crv.f_look_types[l].Lookbehind?
                 && 0 <= l < |crv.f_look_cdns|;                                   // LookEntryOk row
          FG.FreshBodyMatchLBUnfold(crv, str, l, th'.look_regs, ov, body, ncap, nlook, nquant);
          var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
          assert rfx == AI.FFindMatch(bcB, str,
                                      AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                    AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                                      ov, LAnc.Backward, crv.f_look_cdns[l]).0;
          FG.GateCrossCoverageLBNested(rer, qm, body, str, cp, ov, crv.f_look_cdns[l], la, tlk, gm,
                                       ncap, nlook, nquant, |str|);
          assert LS.LkResult(T.TrLookaround(la), tlk, gm, inp).Some?
                 && LS.LkResult(T.TrLookaround(la), tlk, gm, inp).value == gm2 by {
            assert lk == T.TrLookaround(la);
          }
          forall g: LG.GroupId |
            g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat))
            && g in PIV.GmOfLive(NI.LookBodyOfRE(re, l as nat), rfx.value.capture_regs,
                                 rfx.value.look_regs, rfx.value.quant_regs)
            ensures g in gm2
          {
            assert g in PIV.CapIds(body);                                  // body == LookBodyOfRE(re,l)
          }
        }
      }
    }
    assert forall j: int :: j != l ==>
                              AI.get_idx(th'.look_regs.a_clk, j) == AI.get_idx(th.look_regs.a_clk, j)
                              && AI.get_idx(th'.look_regs.a_cp, j) == AI.get_idx(th.look_regs.a_cp, j)
    by {
      RL.ASetLaws(th.look_regs, l, Some(cp as int), clk);
    }
    LookNestBackTGatePassTop(re, crv, str, ov, S, gm, gm2, th, th', l, ncap, nlook, nquant);
    assert LookNestBackRepCTop(re, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                               ncap, nlook, nquant) by {
      forall i | 0 <= i < |[(t.t, gm2)] + ta[1..]|
        ensures LookNestBackTTop(re, crv, str, ov, S, ([(t.t, gm2)] + ta[1..])[i].1, vms2.active[i],
                                 ncap, nlook, nquant)
      {
        if i == 0 {
        } else {
          assert ([(t.t, gm2)] + ta[1..])[i] == ta[i];
          assert vms2.active[i] == s.active[i];
        }
      }
    }

    // ---- (E4 DEEP) the crossing's coverage for the DEEP carrier ----
    // Delegated to `GatePassDeepRepStep` (a standalone lemma) so the crossing
    // discharge + gate-pass congruence do NOT balloon this isolate-assertions
    // lemma's VC count. `la.Lookahead?` holds (dead else-arm above); the seam
    // facts (`GmAgreeOn`, `get_cp`, `LkDir`) are established here.
    assert LookNestBackRepCTopDeep(rer, re, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    // (L5 F7f) direction-GENERIC: both capturing kinds go through the same
    // `GatePassDeepRepStep` (F7a), pinned by `L.LkDir(lk) == LidDir(crv, l)`.
    assert la.Lookahead? || la.Lookbehind?;
    assert L.LkDir(lk) == LidDir(crv, l) by {
      assert crv.f_look_types[l] == la;
      assert lk == T.TrLookaround(la);
    }
    assert M.GmAgreeOn(gm, LG.Empty, set g | g in L.DefGroups(r1)) by {
      forall g: LG.GroupId | g in (set gx | gx in L.DefGroups(r1))
        ensures (g in gm <==> g in LG.Empty) && (g in gm ==> gm[g] == LG.Empty[g])
      {
        assert g !in gm;
      }
    }
    assert AReg.get_cp(th'.look_regs, l) == Some(cp as int) by {
      RL.ASetLaws(th.look_regs, l, Some(cp as int), clk);
    }
    NI.LookSiteTopNested(re, code, 0, endl, pc);
    assert l >= 0 && (l as nat) in NI.TopLookIds(re);
    GatePassDeepRepStep(rer, re, crv, str, ov, S, ta, s.active, t.t, gm, gm2, th, th', l, lk, r1,
                        tlk, body, cp, ncap, nlook, nquant);
    assert LookNestBackRepCTopDeep(rer, re, crv, str, ov, S, [(t.t, gm2)] + ta[1..], vms2.active,
                                   ncap, nlook, nquant) by {
      assert vms2.active == [th'] + s.active[1..];
    }

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm2)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  lemma LiftPreserveNegGatePassLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                     crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                     bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                     l: int, vms2: AI.VmState,
                                     ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires qm.ov == ov
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.NegCheckOracle(l))
    requires !LOr.view_get_oracle(ov, s.cp, l)
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [s.active[0].(pc := s.active[0].pc + 1)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    var th' := th.(pc := th.pc + 1);
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // polarity + the bit ⟹ the functional verdict is Some (negative passes)
    TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
    assert |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept);
    assert pc < endl;
    GatePolarityRE(re, qm, code, 0, endl, pc);
    assert l in qm.looks;
    var lk := qm.looks[l].0;
    var r1 := qm.looks[l].1;
    assert AR.PositiveL(lk) == L.Positivity(lk);
    assert !L.Positivity(lk);
    var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
    assert LL.OracleOkAt(rer, qm, inp);
    PIV.IdxInpOfCp(str, s.cp as nat);
    assert TREP.CpOf(inp) == s.cp as nat;
    assert qm.looks[l] == (lk, r1);
    assert LOr.view_get_oracle(qm.ov, TREP.CpOf(inp), l)
      <==> LT.TreeRes(tlk, LG.Empty, inp, L.LkDir(lk)).Some?;
    assert LS.LkResult(lk, tlk, LG.Empty, inp).Some?;      // clear bit + negative

    // canonical head: the LK branch of the gate rule
    TreeRepLkREAtNegCheckOracle(rer, qm, code, inp, t, pc, ea, l);
    assert t.LK? && t.lk == lk && t.tlk == tlk
           && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);

    // B step: the merge at the RUNNING map is Some(gm) — the identity
    EL.LkResultGmIndep(lk, tlk, gm, inp);
    assert LS.LkResult(lk, tlk, gm, inp).Some?;
    assert LS.LkResult(lk, tlk, gm, inp).value == gm;      // negative: Some(gm)
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm)]);
    bst1 := PT.PTS(inp, [(t.t, gm)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // the child pairing: the raw witness steps by the neg-gate walk core; the
    // erasure tie transports the child
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtNegCheckOracleRec(rer, qm, code, inp, traw, gm, pc, ea, l);
    assert traw.LK? && WalkPairLkRec(rer, qm, code, inp, traw.t, gm, pc + 1, ea);
    assert (th.pc + 1) as nat == pc + 1;
    assert GmtTieOutside(re, th', gm, S);
    assert ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm, th', ncap, nlook, nquant);
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == LT.LK(traw.lk, CE.ProgErase(traw.tlk), CE.ProgErase(traw.t));
      assert CE.ProgErase(t) == LT.LK(t.lk, CE.ProgErase(t.tlk), CE.ProgErase(t.t));
    }
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                           ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm)] + ta[1..])[0] == (t.t, gm) && ([(t.t, gm)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm)] + ta[1..], vms2.active,
                           ncap, nlook, nquant);

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  lemma LiftPreserveGateKillLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                  crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                  bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                  l: int, pos: bool, vms2: AI.VmState,
                                  ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires qm.ov == ov
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat)
          == Some(if pos then RB.CheckOracle(l) else RB.NegCheckOracle(l))
    requires LOr.view_get_oracle(ov, s.cp, l) != pos
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // the gate pc is interior (endl holds Accept), so the polarity pin applies
    TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
    assert |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept);
    assert pc < endl;
    GatePolarityRE(re, qm, code, 0, endl, pc);
    assert l in qm.looks;
    var lk := qm.looks[l].0;
    var r1 := qm.looks[l].1;
    assert AR.PositiveL(lk) == L.Positivity(lk);
    assert L.Positivity(lk) == pos;

    // the bit at this position IS the body tree's verdict (oracle column)
    var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
    assert LL.OracleOkAt(rer, qm, inp);          // inp == inp0 instance of OracleOkSuffix
    PIV.IdxInpOfCp(str, s.cp as nat);
    assert TREP.CpOf(inp) == s.cp as nat;
    assert qm.looks[l] == (lk, r1);
    assert LOr.view_get_oracle(qm.ov, TREP.CpOf(inp), l)
      <==> LT.TreeRes(tlk, LG.Empty, inp, L.LkDir(lk)).Some?;
    // failing bit + polarity ⟹ the functional verdict is None (both flavours)
    assert LS.LkResult(lk, tlk, LG.Empty, inp).None?;

    // canonical head: the LKFail branch of the gate rule
    if pos {
      TreeRepLkREAtCheckOracle(rer, qm, code, inp, t, pc, ea, l);
    } else {
      TreeRepLkREAtNegCheckOracle(rer, qm, code, inp, t, pc, ea, l);
    }
    assert t == LT.LKFail(lk, tlk);
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([]);
    bst1 := LiftDropDeadHeadLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                  bst, s, s1, vms2, ncap, nlook, nquant);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);
  }

  lemma LiftPreserveEndLoopPassLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                     crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                     bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                     vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.EndLoop)
    requires s.active[0].exit_allowed
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [s.active[0].(pc := s.active[0].pc + 1)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    var th' := th.(pc := th.pc + 1);
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // canonical head: Progress with canonical child at (pc+1, true)
    TreeRepLkREAtEndLoop(rer, qm, code, inp, t, pc, ea);
    assert t.Progress? && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, true);

    // B step: pts_active queues the child with the same gm
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm)]);
    bst1 := PT.PTS(inp, [(t.t, gm)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // the child pairing: the raw witness unwraps its own Progress; erasure is
    // transparent to the guard on BOTH sides
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtEndLoopRec(rer, qm, code, inp, traw, gm, pc, ea);
    assert traw.Progress? && WalkPairLkRec(rer, qm, code, inp, traw.t, gm, pc + 1, true);
    assert (th.pc + 1) as nat == pc + 1;
    assert th'.exit_allowed == true;
    assert GmtTieOutside(re, th', gm, S);
    assert ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm, th', ncap, nlook, nquant);
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == CE.ProgErase(traw.t);   // Progress transparent
      assert CE.ProgErase(t) == CE.ProgErase(t.t);
    }
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                           ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm)] + ta[1..])[0] == (t.t, gm) && ([(t.t, gm)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm)] + ta[1..], vms2.active,
                           ncap, nlook, nquant);

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  lemma LiftPreserveEndLoopKillLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                     crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                     bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                     vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.EndLoop)
    requires !s.active[0].exit_allowed
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, ta[0].1, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, th.exit_allowed);
    TreeRepLkREAtEndLoop(rer, qm, code, inp, t, pc, th.exit_allowed);
    assert t == LT.Mismatch;
    assert PTL.TreeBfsStepLk(t, ta[0].1, inp) == PT.StepActive([]);
    bst1 := LiftDropDeadHeadLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                  bst, s, s1, vms2, ncap, nlook, nquant);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);
  }

  lemma LiftPreserveAnchorPassLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                    crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                    bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                    a: R.anchor, vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires !rer.multiline
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.AnchorAssertion(a))
    requires LAnc.is_satisfied(a, s.context, LAnc.Forward)
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [s.active[0].(pc := s.active[0].pc + 1)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    var th' := th.(pc := th.pc + 1);
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // the VM-side check IS the spec-side check
    assert PIV.ContextOkRE(str, s.cp, s.context);
    PSM.ContextOkIsCtxOf(str, s.cp as nat);
    assert LAnc.is_satisfied(a, TREP.CtxOf(inp), LAnc.Forward);
    TREP.AnchorAgreeInput(rer, a, inp);
    assert LS.AnchorSatisfied(rer, T.TrAnchor(a), inp);

    // canonical head: AnchorPass with canonical child at (pc+1, ea)
    TreeRepLkREAtAnchor(rer, qm, code, inp, t, pc, ea, a);
    assert t.AnchorPass? && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);

    // B step: pts_active queues the child with the same gm
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm)]);
    bst1 := PT.PTS(inp, [(t.t, gm)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // the child pairing: raw witness steps by the proven Anchor core; the
    // erasure tie transports to the canonical child
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
                         && ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    assert traw.AnchorPass? by {
      if !traw.AnchorPass? {
        var acts: LS.Actions, b: BS.LoopBool :|
          AR.ActionsRepL(rer, qm, acts, code, pc)
          && EL.PikeLkActionsRec(acts)
          && ATR.EaOf(b) == ea
          && CW.BoolTreeLkX(rer, acts, inp, b, traw)
          && GateAheadClear(acts, gm)
          && WalkDefsOk(acts);
        assert TtLkRec(rer, qm, code, inp, traw, pc, ea);
        TtLkAtAnchorRec(rer, qm, code, inp, traw, pc, ea, a);
        assert traw == LT.Mismatch;
        assert CE.ProgErase(traw) == LT.Mismatch;
        assert CE.ProgErase(t).AnchorPass?;
        assert false;
      }
    }
    ThreadRepLkStepAnchorRec(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th,
                             ncap, nlook, nquant, a);
    assert ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm, th', ncap, nlook, nquant);
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == LT.AnchorPass(traw.a, CE.ProgErase(traw.t));
      assert CE.ProgErase(t) == LT.AnchorPass(t.a, CE.ProgErase(t.t));
    }
    assert (th.pc + 1) as nat == pc + 1;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                           ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm)] + ta[1..])[0] == (t.t, gm) && ([(t.t, gm)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm)] + ta[1..], vms2.active,
                           ncap, nlook, nquant);

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  lemma LiftPreserveAnchorKillLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                    crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                    bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                    a: R.anchor, vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires !rer.multiline
    requires bst.PTS?
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.AnchorAssertion(a))
    requires !LAnc.is_satisfied(a, s.context, LAnc.Forward)
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, t, ta[0].1, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, th.exit_allowed);

    // the VM-side check IS the spec-side check
    assert PIV.ContextOkRE(str, s.cp, s.context);
    PSM.ContextOkIsCtxOf(str, s.cp as nat);
    assert !LAnc.is_satisfied(a, TREP.CtxOf(inp), LAnc.Forward);
    TREP.AnchorAgreeInput(rer, a, inp);
    assert !LS.AnchorSatisfied(rer, T.TrAnchor(a), inp);

    TreeRepLkREAtAnchor(rer, qm, code, inp, t, pc, th.exit_allowed, a);
    assert t == LT.Mismatch;
    assert PTL.TreeBfsStepLk(t, ta[0].1, inp) == PT.StepActive([]);
    bst1 := LiftDropDeadHeadLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                  bst, s, s1, vms2, ncap, nlook, nquant);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);
  }

  lemma LiftAdvanceEpsilonRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                              ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                              S: set<LG.GroupId>, ptsA: PT.PikeTreeState, s: AI.VmState,
                              bst: PT.PikeTreeState, dir: LAnc.direction,
                              ncap: int, nlook: int, nquant: int)
    returns (ptsA': PT.PikeTreeState, bst1: PT.PikeTreeState)
    requires !rer.multiline && !rer.ignoreCase && qm.ov == ov
    requires |ov| == |str| + 1                                    // L3b: propagate to the backward LB gate
    requires OE.OracleColsOk(rer, qm, str)                    // (L5 F7d) whole-string oracle correctness (backward keystone)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires S == PIV.CapIdsInLooks(re)   // the value-tie boundary (SetReg/gate cases)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)   // (BRICK D5) NESTED per-lid package
    requires NR.L5ScopeRE(re) && L5ScopeV1RE(re)   // (L5 F7f) the v1 L5 scope
    requires LTB.LookUnique(re)           // (E3) cross-lid ownership pinning
    requires LTB.LookTablesOk(re, crv)    // (E4) row↔structure tie (gate converse)
    requires dir == LAnc.Forward
    requires ptsA.PTS? && bst.PTS?
    requires |s.processed.true_set| == RB.size(code) && |s.processed.false_set| == RB.size(code)
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, s, ncap, nlook, nquant)
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    ensures PSM.TrcRE(ptsA, ptsA')
    ensures ptsA'.PTS?
    ensures PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA',
                              AI.FAdvanceEpsilon(code, s, ov, dir).0, ncap, nlook, nquant)
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?           // the ε-phase never finalizes; pts_final is LiftConsume's
    ensures LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1,
                       AI.FAdvanceEpsilon(code, s, ov, dir).0, ncap, nlook, nquant)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 {
      ptsA' := ptsA;
      bst1 := bst;
      PSM.TrcRefl(ptsA);
      TrcLkRefl(bst);
      return;
    }
    var th := s.active[0];
    var ac := s.active[1..];

    // Head bounds from the canonical tie (machine A used ThreadNestRE here).
    var PTS(inp, ta, best, tb, seen) := bst;
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0 && th.pc >= 0;
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, ta[0].0, ta[0].1, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    assert TreeRepLkRE(rer, qm, code, inp, ta[0].0, pc, th.exit_allowed);
    TreeRepLkREInRange(rer, qm, code, inp, ta[0].0, pc, th.exit_allowed);
    assert pc < |code| && RB.size(code) == |code|;
    var i := RB.get_instr(code, th.pc);
    assert i == code[pc] && NR.GetPcRE(code, pc) == Some(i);

    if AI.bpc_mem(s.processed, th.pc, th.exit_allowed) {
      var bstS := LiftPreserveSkipLkRec(rer, qm, re, code, endl, crv, str, ov, S, bst, s, ncap, nlook, nquant);
      var ptsS := PSM.PreserveSkipCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s, ncap, nlook, nquant);
      var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                               ptsS, s.(active := ac), bstS, dir, ncap, nlook, nquant);
      PSM.TrcCons(ptsA, ptsS, ptsA2);
      TrcLkCons(bst, bstS, bst2);
      ptsA' := ptsA2;
      bst1 := bst2;
      return;
    }

    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(s.processed, th.pc, th.exit_allowed));
    assert AI.unprocessed(s1.processed) <= AI.unprocessed(s.processed)
           && (0 <= th.pc < RB.size(code) ==> AI.unprocessed(s1.processed) < AI.unprocessed(s.processed))
    by { AI.UnprocessedAdd(s.processed, th.pc, th.exit_allowed); }
    assert AI.unprocessed(s1.processed) < AI.unprocessed(s.processed);
    assert |s1.processed.true_set| == RB.size(code) && |s1.processed.false_set| == RB.size(code);

    match i {
      case Accept =>
        var vms2 := s1.(active := [], bestmatch := Some(th));
        bst1 := LiftPreserveAcceptLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                        bst, s, s1, vms2, ncap, nlook, nquant);
        ptsA' := PSM.PreserveAcceptCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                              s1, vms2, ncap, nlook, nquant);
        PSM.TrcRefl(ptsA');
        PSM.TrcCons(ptsA, ptsA', ptsA');
        TrcLkRefl(bst1);
        TrcLkCons(bst, bst1, bst1);
        assert AI.FAdvanceEpsilon(code, s, ov, dir).0 == vms2;
      case Jmp(x) =>
        var th' := th.(pc := x);
        var vms2 := s1.(active := [th'] + ac);
        LiftPreserveStutterLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                 bst, s, s1, th', vms2, ncap, nlook, nquant);
        PSM.PreserveStutterCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                      s1, th', vms2, ncap, nlook, nquant);
        var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                 ptsA, vms2, bst, dir, ncap, nlook, nquant);
        ptsA' := ptsA2;
        bst1 := bst2;
      case BeginLoop =>
        var th' := th.(exit_allowed := false, pc := th.pc + 1);
        var vms2 := s1.(active := [th'] + ac);
        LiftPreserveStutterLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                 bst, s, s1, th', vms2, ncap, nlook, nquant);
        PSM.PreserveStutterCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                      s1, th', vms2, ncap, nlook, nquant);
        var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                 ptsA, vms2, bst, dir, ncap, nlook, nquant);
        ptsA' := ptsA2;
        bst1 := bst2;
      case Consume(ce) =>
        var (nb, ni) := AI.add_thread(th, ce, s1.blocked, s1.isblocked);
        if AI.pc_mem(s1.isblocked, th.pc) {
          assert nb == s1.blocked && ni == s1.isblocked;
          var vms2 := s1.(blocked := nb, isblocked := ni, active := ac);
          assert vms2 == s1.(active := ac);
          var bstS := LiftPreserveConsumeDropLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                                   bst, s, s1, ce, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveConsumeDropNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                    s1, ce, vms2, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                   ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        } else {
          assert nb == [(th, ce)] + s1.blocked && ni == AI.pc_add(s1.isblocked, th.pc);
          var vms2 := s1.(blocked := nb, isblocked := ni, active := ac);
          var bstS := LiftPreserveConsumeAddLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                                  bst, s, s1, ce, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveConsumeAddNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                   s1, ce, vms2, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                   ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        }
      case Fork(x, y) =>
        var newt := AI.Thread(x, th.capture_regs, th.look_regs, th.quant_regs, th.exit_allowed);
        var vms2 := s1.(active := [newt, th.(pc := y)] + ac);
        // backward-fork flag pin: a false-thread never sits at a Cold pc
        assert (x <= th.pc || y <= th.pc) ==> th.exit_allowed by {
          if (x <= th.pc || y <= th.pc) && !th.exit_allowed {
            assert th in s.active && PSM.EaColdOkRE(code, th);
            assert NI.ColdF(code, pc, 1);
            assert NI.ColdRE(code, pc);
          }
        }
        var bstS := LiftPreserveForkLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                          bst, s, s1, x, y, vms2, ncap, nlook, nquant);
        var ptsS := PSM.PreserveForkCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                               s1, x, y, vms2, ncap, nlook, nquant);
        var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                 ptsS, vms2, bstS, dir, ncap, nlook, nquant);
        PSM.TrcTrans(ptsA, ptsS, ptsA2);
        TrcLkTrans(bst, bstS, bst2);
        ptsA' := ptsA2;
        bst1 := bst2;
      case SetRegisterToCP(reg) =>
        var th' := th.(capture_regs := AReg.set_reg(th.capture_regs, reg, Some(s1.cp), s1.clock),
        pc := th.pc + 1);
        var vms2 := s1.(active := [th'] + ac);
        // A-side gm effect off ptsA's head (helper keeps the dispatcher VC small)
        DispatchSetRegEffectNested(rer, qm, re, code, endl, ngroups, str, ptsA, s, s1, reg, th',
                                   ncap, nlook, nquant);
        assert th in s.active;
        assert CM.ThreadClocksLE(th, s.clock) && s.clock >= 0;   // PikeInvFullRE backbone
        var bstS := LiftPreserveSetRegLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                            bst, s, s1, reg, th', vms2, ncap, nlook, nquant);
        var ptsS: PT.PikeTreeState;
        if reg % 2 == 0 {
          ptsS := PSM.PreserveOpenCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                             s1, reg, vms2, ncap, nlook, nquant);
        } else {
          ptsS := PSM.PreserveCloseCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                              s1, reg, vms2, ncap, nlook, nquant);
        }
        var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                 ptsS, vms2, bstS, dir, ncap, nlook, nquant);
        PSM.TrcCons(ptsA, ptsS, ptsA2);
        TrcLkTrans(bst, bstS, bst2);
        ptsA' := ptsA2;
        bst1 := bst2;
      case SetQuantToClock(q, bq) =>
        var ocp := if bq then Some(s1.cp) else None;
        var th' := th.(quant_regs := AReg.set_reg(th.quant_regs, q, ocp, s1.clock), pc := th.pc + 1);
        var vms2 := s1.(active := [th'] + ac);
        // the canonical tie: a Reset either way (§2.5b F-c: the stamp too); the
        // A-side helpers yield the GMReset gm effect (GmOfLive reads clocks only)
        TreeRepLkREAtSetQuant(rer, qm, code, inp, ta[0].0, pc, th.exit_allowed, q, bq);
        assert q in qm.quants;
        assert th in s.active;
        assert CM.ThreadRegsWf(th, ncap, nlook, nquant);   // PikeInvFullRE backbone
        assert CM.ThreadClocksLE(th, s.clock) && s.clock >= 0;
        if bq {
          DispatchStampEffectNested(rer, qm, re, code, endl, ngroups, str, ptsA, s, s1, q, th',
                                    ncap, nlook, nquant);
        } else {
          DispatchResetEffectNested(rer, qm, re, code, endl, ngroups, str, ptsA, s, s1, q, th',
                                    ncap, nlook, nquant);
        }
        var bstS := LiftPreserveSetQuantLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                              bst, s, s1, q, bq, th', vms2, ncap, nlook, nquant);
        var ptsS := PSM.PreserveQuantCaseNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                s1, q, bq, vms2, ncap, nlook, nquant);
        var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                 ptsS, vms2, bstS, dir, ncap, nlook, nquant);
        PSM.TrcTrans(ptsA, ptsS, ptsA2);
        TrcLkTrans(bst, bstS, bst2);
        ptsA' := ptsA2;
        bst1 := bst2;
      case CheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var th' := th.(pc := th.pc + 1,
          look_regs := AReg.set_reg(th.look_regs, l, Some(s1.cp), s1.clock));
          var vms2 := s1.(active := [th'] + ac);
          assert th in s.active;
          assert CM.ThreadRegsWf(th, ncap, nlook, nquant);   // PikeInvFullRE backbone
          assert CM.ThreadClocksLE(th, s.clock) && s.clock >= 0;
          assert PSM.ThreadNestRE(re, code, endl, th.pc, th);
          var bstS := LiftPreserveGatePassLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                                bst, s, s1, l, th', vms2, ncap, nlook, nquant);
          PSM.PreserveOraclePassNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                       s1, th', vms2, l, true, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                   ptsA, vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveGateKillLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                                bst, s, s1, l, true, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveOracleKillNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                   s1, vms2, l, true, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                   ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        }
      case NegCheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveGateKillLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                                bst, s, s1, l, false, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveOracleKillNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                   s1, vms2, l, false, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                   ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := [th.(pc := th.pc + 1)] + ac);
          var bstS := LiftPreserveNegGatePassLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                                   bst, s, s1, l, vms2, ncap, nlook, nquant);
          PSM.PreserveOraclePassNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                       s1, th.(pc := th.pc + 1), vms2, l, false, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                   ptsA, vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        }
      case WriteOracle(l) =>
        // no TreeRepLkRE rule at WriteOracle — the canonical head tie is refuted
        assert false;
        ptsA' := ptsA;
        bst1 := bst;
      case EndLoop =>
        if th.exit_allowed {
          var vms2 := s1.(active := [th.(pc := th.pc + 1)] + ac);
          var bstS := LiftPreserveEndLoopPassLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                                   bst, s, s1, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveEndLoopPassNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                    s1, vms2, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                   ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveEndLoopKillLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                                   bst, s, s1, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveEndLoopKillNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                    s1, vms2, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                   ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        }
      case CheckNullable(qid) =>
        // no TreeRepLkRE rule at CheckNullable — refuted
        assert false;
        ptsA' := ptsA;
        bst1 := bst;
      case AnchorAssertion(a) =>
        if LAnc.is_satisfied(a, s1.context, dir) {
          var vms2 := s1.(active := [th.(pc := th.pc + 1)] + ac);
          var bstS := LiftPreserveAnchorPassLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                                  bst, s, s1, a, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveAnchorPassNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                   s1, vms2, a, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                   ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveAnchorKillLkRec(rer, qm, re, code, endl, crv, str, ov, S,
                                                  bst, s, s1, a, vms2, ncap, nlook, nquant);
          var ptsS := PSM.PreserveAnchorKillNested(rer, qm, re, code, endl, ngroups, str, ptsA, s,
                                                   s1, vms2, a, ncap, nlook, nquant);
          var ptsA2, bst2 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                                   ptsS, vms2, bstS, dir, ncap, nlook, nquant);
          PSM.TrcCons(ptsA, ptsS, ptsA2);
          TrcLkTrans(bst, bstS, bst2);
          ptsA' := ptsA2;
          bst1 := bst2;
        }
      case Fail =>
        // no TreeRepLkRE rule at Fail — refuted
        assert false;
        ptsA' := ptsA;
        bst1 := bst;
    }
  }

  lemma LiftStepCRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                     endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                     S: set<LG.GroupId>, ptsA: PT.PikeTreeState, ptsB: PT.PikeTreeState, vms: AI.VmState,
                     ncap: int, nlook: int, nquant: int)
    returns (ptsA': PT.PikeTreeState, ptsB': PT.PikeTreeState)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires |ov| == |str| + 1                                    // L3b: propagate to the backward LB gate
    requires OE.OracleColsOk(rer, qm, str)                    // (L5 F7d) whole-string oracle correctness (backward keystone)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires S == PIV.CapIdsInLooks(re)   // the value-tie boundary (SetReg/gate cases)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)   // (BRICK D5) NESTED per-lid package
    requires NR.L5ScopeRE(re) && L5ScopeV1RE(re)   // (L5 F7f) the v1 L5 scope
    requires LTB.LookUnique(re)           // (E3) cross-lid ownership pinning
    requires LTB.LookTablesOk(re, crv)    // (E4) row↔structure tie (gate converse)
    requires ptsA.PTS? && ptsB.PTS?
    requires |vms.processed.true_set| == RB.size(code) && |vms.processed.false_set| == RB.size(code)
    requires LiftInvCRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S, ptsA, ptsB, vms, ncap, nlook, nquant)
    ensures PTL.TrcPikeTreeLk(ptsB, ptsB')
    ensures ptsA'.PTS? && ptsB'.PTS?
    ensures LiftInvCRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                        ptsA', ptsB', AI.FAdvanceEpsilon(code, vms, ov, LAnc.Forward).0, ncap, nlook, nquant)
  {
    var vms' := AI.FAdvanceEpsilon(code, vms, ov, LAnc.Forward).0;
    // ONE call: the composite dispatcher steps machine A per-case by the
    // proven Preserve*Case lemmas and machine B by the LiftPreserve*Lk tier.
    ptsA', ptsB' := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                          ptsA, vms, ptsB, LAnc.Forward, ncap, nlook, nquant);
    // the inp link: both sides pin their inp to InpOfCp(str, vms'.cp)
    assert PIV.PikeInvRE(rer, qm, re, code, ngroups, str, ptsA', vms');
    assert ptsA'.inp == PIV.InpOfCp(str, vms'.cp);
    assert ptsB'.inp == PIV.InpOfCp(str, vms'.cp);
  }

  lemma LiftFindMatchCRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                          endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                          S: set<LG.GroupId>, ptsA: PT.PikeTreeState, bst: PT.PikeTreeState,
                          vms: AI.VmState, cdn: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    returns (bestT: Option<LT.Leaf>)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires |ov| == |str| + 1                                    // L3b: propagate to the backward LB gate
    requires OE.OracleColsOk(rer, qm, str)                    // (L5 F7d) whole-string oracle correctness (backward keystone)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires S == PIV.CapIdsInLooks(re)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)   // (BRICK D5) NESTED per-lid package
    requires NR.L5ScopeRE(re) && L5ScopeV1RE(re)                     // (L5 F7f) the v1 L5 scope
    requires LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires ptsA.PTS? && bst.PTS?
    requires |vms.processed.true_set| == RB.size(code) && |vms.processed.false_set| == RB.size(code)
    requires vms.context.nextchar == AI.get_char(str, vms.cp)
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, vms, ncap, nlook, nquant)
    requires LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, vms, ncap, nlook, nquant)
    ensures PTL.TrcPikeTreeLk(bst, PT.PTS_final(bestT))
    ensures BestTieLkNestedTop(rer, re, crv, str, ov, S, bestT,
                               AI.FFindMatch(code, str, vms, ov, LAnc.Forward, cdn).0, ncap, nlook, nquant)
    decreases |str| - vms.cp
  {
    var dir := LAnc.Forward;
    var s0 := vms.(cdn := LCdn.build_cdn_v(cdn, vms.cp, ov, vms.context, dir));
    // Neither invariant reads cdn.
    assert PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, s0, ncap, nlook, nquant);
    assert LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst, s0, ncap, nlook, nquant);
    var ptsA1, bst1 := LiftAdvanceEpsilonRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                             ptsA, s0, bst, dir, ncap, nlook, nquant);
    var (s1, ov1) := AI.FAdvanceEpsilon(code, s0, ov, dir);
    PSM.StaticOkNoWriteNested(qm, re, code, endl);
    CM.FAdvanceEpsilonOvStable(code, s0, ov, dir);
    assert ov1 == ov;
    PSM.FAdvanceEpsilonActiveEmpty(code, s0, ov, dir);
    assert s1.active == [] && s1.cp == s0.cp == vms.cp && s1.context == vms.context;
    assert PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA1, s1, ncap, nlook, nquant);
    assert LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, s1, ncap, nlook, nquant);

    assert bst1.PTS?;
    var PTS(inp1, ta1, best1, tb1, seen1) := bst1;
    assert ActiveRepLkCRec(rer, qm, re, code, inp1, crv, str, ov, S, ta1, s1.active, ncap, nlook, nquant);
    assert ta1 == [];
    assert inp1 == PIV.InpOfCp(str, s1.cp) && 0 <= s1.cp <= |str|;
    assert BestTieLkNestedTop(rer, re, crv, str, ov, S, best1, s1.bestmatch, ncap, nlook, nquant);

    if |s1.blocked| == 0 {
      assert LC.Reverse(s1.blocked) == [];
      assert tb1 == [] by {
        if LC.AdvanceInput(inp1, WP.Forward).Some? {
          var nx :| LC.AdvanceInput(inp1, WP.Forward) == Some(nx);
          assert BlockedRepLkCRec(rer, qm, re, code, inp1, nx, crv, str, ov, S, tb1,
                                  PIV.MatchingBlocked(LC.Reverse(s1.blocked), inp1), ncap, nlook, nquant);
          assert PIV.MatchingBlocked([], inp1) == [];
        }
      }
      bestT := best1;
      assert PTL.PikeTreeStepLk(bst1, PT.PTS_final(best1));
      TrcLkRefl(PT.PTS_final(best1));
      TrcLkCons(bst1, PT.PTS_final(best1), PT.PTS_final(best1));
      TrcLkTrans(bst, bst1, PT.PTS_final(best1));
      assert AI.FFindMatch(code, str, vms, ov, dir, cdn).0 == s1.bestmatch;
    } else if s1.context.nextchar.None? {
      assert AI.get_char(str, vms.cp).None?;
      assert vms.cp >= |str| && s1.cp == |str|;
      assert inp1.next == str[s1.cp..] == [];
      assert LC.AdvanceInput(inp1, WP.Forward).None?;
      assert tb1 == [];
      bestT := best1;
      assert PTL.PikeTreeStepLk(bst1, PT.PTS_final(best1));
      TrcLkRefl(PT.PTS_final(best1));
      TrcLkCons(bst1, PT.PTS_final(best1), PT.PTS_final(best1));
      TrcLkTrans(bst, bst1, PT.PTS_final(best1));
      assert AI.FFindMatch(code, str, vms, ov, dir, cdn).0 == s1.bestmatch;
    } else {
      // A real character remains: consume it (the FFindMatch else-branch).
      assert AI.get_char(str, vms.cp).Some?;
      assert vms.cp < |str|;
      assert inp1.next == str[s1.cp..] && |inp1.next| > 0;
      assert s1.context.nextchar == Some(inp1.next[0]);
      PSM.FConsumeResumes(s1, inp1);
      var s2 := AI.FConsume(s1);
      var filter := PIV.MatchingBlocked(LC.Reverse(s1.blocked), inp1);
      assert PSM.ResumeAll(filter) + s1.active == PSM.ResumeAll(filter);
      assert s2 == s1.(active := PSM.ResumeAll(filter), blocked := []);
      var s3 := s2.(processed := AI.init_bpcset(RB.size(code)),
      isblocked := AI.init_pcset(RB.size(code)),
      cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
      var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
      var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
      assert s4.cp == vms.cp + 1;
      assert s4.context.nextchar == AI.get_char(str, s4.cp);
      assert AI.FFindMatch(code, str, vms, ov, dir, cdn)
          == AI.FFindMatch(code, str, s4, ov1, dir, cdn);

      PSM.AdvanceInpOfCpBridge(str, vms.cp);
      var nextinp := PT.NextInp(inp1);
      assert nextinp == PIV.InpOfCp(str, vms.cp + 1);
      assert LC.AdvanceInput(inp1, WP.Forward) == Some(nextinp);
      assert BlockedRepLkCRec(rer, qm, re, code, inp1, nextinp, crv, str, ov, S, tb1, filter,
                              ncap, nlook, nquant);

      if |tb1| == 0 {
        assert |filter| == 0;
        assert s4.active == [] && s4.blocked == [];
        PSM.FFindMatchInert(code, str, s4, ov1, dir, cdn);
        assert AI.FFindMatch(code, str, s4, ov1, dir, cdn).0 == s4.bestmatch == s1.bestmatch;
        bestT := best1;
        assert PTL.PikeTreeStepLk(bst1, PT.PTS_final(best1));
        TrcLkRefl(PT.PTS_final(best1));
        TrcLkCons(bst1, PT.PTS_final(best1), PT.PTS_final(best1));
        TrcLkTrans(bst, bst1, PT.PTS_final(best1));
      } else {
        // B: pts_nextchar — the blocked pairs become the next position's actives.
        var bst2 := PT.PTS(nextinp, tb1, best1, [], SS.InitialSeenTrees);
        assert PTL.PikeTreeStepLk(bst1, bst2);

        // ---- machine A: re-establish PikeInvFullRE at (ptsA2, s4) — the
        // FindMatchSimRE consume-phase block, verbatim.
        assert ptsA1.PTS?;
        var PTS(inpA1, taA1, bestA1, tbA1, seenA1) := ptsA1;
        assert PIV.ActiveRepRE(rer, qm, re, code, str, inpA1, taA1, s1.active);
        assert taA1 == [] && inpA1 == PIV.InpOfCp(str, s1.cp);
        assert PIV.BlockedRepRE(rer, qm, re, code, str, inpA1, nextinp, tbA1, filter);
        var ptsA2 := PT.PTS(nextinp, tbA1, bestA1, [], SS.InitialSeenTrees);
        PSM.BlockedToActiveRE(rer, qm, re, code, str, inpA1, nextinp, tbA1, filter);
        assert PIV.ActiveRepRE(rer, qm, re, code, str, nextinp, tbA1, s4.active);
        CM.FConsumeClocksLE(s1);
        CM.FConsumeRegsWf(s1, ncap, nlook, nquant);
        CM.FConsumeCapsLE(s1);
        assert CM.VmClocksLE(s4) by {
          assert s4.active == s2.active && s4.blocked == s2.blocked
                 && s4.bestmatch == s2.bestmatch && s4.clock == s2.clock;
        }
        assert CM.VmRegsWf(s4, ncap, nlook, nquant) by {
          assert s4.active == s2.active && s4.blocked == s2.blocked && s4.bestmatch == s2.bestmatch;
        }
        assert CM.VmCapsLE(s4) by { CM.VmCapsLEAdvance(s2, s4); }
        assert forall t2 | t2 in s4.active :: PSM.ThreadNestRE(re, code, endl, t2.pc, t2) by {
          forall p | p in filter ensures PSM.ThreadNestRE(re, code, endl, p.0.pc + 1, p.0) {
            PSM.MatchingBlockedSubset(LC.Reverse(s1.blocked), inp1, p);
            PSM.ReverseMembership(s1.blocked, p);
            assert p in s1.blocked;
          }
          PSM.ResumeAllNest(re, code, endl, filter);
        }
        PIV.InitialInclusionRE(rer, qm, code, nextinp, PIV.HdTreeOf(tbA1),
                               PIV.HeadPcOf(s4.active), RB.size(code));
        assert PSM.IsblockedInclusionRE(rer, qm, code, nextinp, SS.InitialSeenTrees, s4.isblocked) by {
          forall pc0: nat | AI.pc_mem(s4.isblocked, pc0)
            ensures exists t0: LT.Tree, b0: bool ::
                      SS.Inseen(SS.InitialSeenTrees, t0) && TT.TreeThreadRE(rer, qm, code, nextinp, t0, pc0, b0)
          {
            assert s4.isblocked[pc0] == false;
            assert false;
          }
        }
        assert forall t2 | t2 in s4.active :: PSM.EaColdOkRE(code, t2) by {
          PSM.ResumeAllEa(filter);
          assert s4.active == PSM.ResumeAll(filter);
        }
        assert forall t2 | t2 in s4.active :: PIV.LooksCapUnset(re, t2.capture_regs.a_clk) by {
          forall p | p in filter ensures PIV.LooksCapUnset(re, p.0.capture_regs.a_clk) {
            PSM.MatchingBlockedSubset(LC.Reverse(s1.blocked), inp1, p);
            PSM.ReverseMembership(s1.blocked, p);
            assert p in s1.blocked;
          }
          PSM.ResumeAllCapUnset(re, filter);
          assert s4.active == PSM.ResumeAll(filter);
        }
        assert PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA2, s4, ncap, nlook, nquant);

        // ---- machine B: LiftInv at (bst2, s4).
        BlockedToActiveLkCRec(rer, qm, re, code, inp1, nextinp, crv, str, ov, S, tb1, filter,
                              ncap, nlook, nquant);
        assert ActiveRepLkCRec(rer, qm, re, code, nextinp, crv, str, ov, S, tb1, s4.active,
                               ncap, nlook, nquant);
        assert PIV.ContextOkRE(str, s4.cp, s4.context);
        forall nx2 | LC.AdvanceInput(nextinp, WP.Forward) == Some(nx2)
          ensures BlockedRepLkCRec(rer, qm, re, code, nextinp, nx2, crv, str, ov, S, [],
                                   PIV.MatchingBlocked(LC.Reverse(s4.blocked), nextinp), ncap, nlook, nquant)
        {
          assert LC.Reverse(s4.blocked) == [];
          assert PIV.MatchingBlocked([], nextinp) == [];
        }
        InitialSeenRepLk(rer, qm, code, nextinp, PIV.HdTreeOf(tb1), PIV.HeadPcOf(s4.active),
                         RB.size(code));
        assert IsblockedRepLk(rer, qm, code, nextinp, SS.InitialSeenTrees, s4.isblocked) by {
          forall pc0: nat | AI.pc_mem(s4.isblocked, pc0)
            ensures exists t0: LT.Tree, b0: bool ::
                      SS.Inseen(SS.InitialSeenTrees, t0) && TreeRepLkRE(rer, qm, code, nextinp, t0, pc0, b0)
          {
            assert s4.isblocked[pc0] == false;
            assert false;
          }
        }
        assert SSx.IsStrictSuffix(nextinp, inp1, WP.Forward);
        LL.OracleOkSuffixStep(rer, qm, inp1, nextinp);

        // ---- (E3) the carrier crosses the consume: reactivation keeps registers ----
        // (D3) `*Top` carriers throughout.
        assert LookNestRepBTop(re, S, tb1, filter) by {
          assert LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, s1, ncap, nlook, nquant);
          assert bst1 == PT.PTS(inp1, ta1, best1, tb1, seen1);
          assert LC.AdvanceInput(inp1, WP.Forward).Some?;
          assert filter == PIV.MatchingBlocked(LC.Reverse(s1.blocked), inp1);
        }
        assert LookNestRepCTop(re, S, tb1, s4.active) by {
          assert |tb1| == |filter|;                        // LookNestRepBTop lengths
          assert s4.active == PSM.ResumeAll(filter);
          ResumeAllLen(filter);
          forall i | 0 <= i < |tb1|
            ensures LookNestOkTTop(re, S, tb1[i].1, s4.active[i])
          {
            assert LookNestOkTTop(re, S, tb1[i].1, filter[i].0);
            ResumeAllIndex(filter, i);
            assert s4.active[i] == filter[i].0.(exit_allowed := true, pc := filter[i].0.pc + 1);
            assert s4.active[i].capture_regs == filter[i].0.capture_regs
                   && s4.active[i].look_regs == filter[i].0.look_regs
                   && s4.active[i].quant_regs == filter[i].0.quant_regs;
          }
        }
        assert LC.AdvanceInput(nextinp, WP.Forward).Some? ==>
            LookNestRepBTop(re, S, [], PIV.MatchingBlocked(LC.Reverse(s4.blocked), nextinp)) by {
          assert LC.Reverse(s4.blocked) == [];
          assert PIV.MatchingBlocked([], nextinp) == [];
        }
        assert LookNestBackRepBTop(re, crv, str, ov, S, tb1, filter, ncap, nlook, nquant) by {
          assert LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, s1, ncap, nlook, nquant);
          assert bst1 == PT.PTS(inp1, ta1, best1, tb1, seen1);
          assert LC.AdvanceInput(inp1, WP.Forward).Some?;
        }
        assert LookNestBackRepCTop(re, crv, str, ov, S, tb1, s4.active, ncap, nlook, nquant) by {
          assert s4.active == PSM.ResumeAll(filter);
          ResumeAllLen(filter);
          forall i | 0 <= i < |tb1|
            ensures LookNestBackTTop(re, crv, str, ov, S, tb1[i].1, s4.active[i], ncap, nlook, nquant)
          {
            assert LookNestBackTTop(re, crv, str, ov, S, tb1[i].1, filter[i].0, ncap, nlook, nquant);
            ResumeAllIndex(filter, i);
            assert s4.active[i] == filter[i].0.(exit_allowed := true, pc := filter[i].0.pc + 1);
            assert s4.active[i].look_regs == filter[i].0.look_regs
                   && s4.active[i].quant_regs == filter[i].0.quant_regs;
            LookNestBackTRegSameTop(re, crv, str, ov, S, tb1[i].1, tb1[i].1, filter[i].0, s4.active[i],
                                    ncap, nlook, nquant);
          }
        }
        assert LC.AdvanceInput(nextinp, WP.Forward).Some? ==>
            LookNestBackRepBTop(re, crv, str, ov, S, [],
                                PIV.MatchingBlocked(LC.Reverse(s4.blocked), nextinp), ncap, nlook, nquant) by {
          assert LC.Reverse(s4.blocked) == [];
          assert PIV.MatchingBlocked([], nextinp) == [];
        }
        // (R2 DEEP CARRIER) the deep reps cross the consume PARALLEL to the direct.
        assert LookNestBackRepBTopDeep(rer, re, crv, str, ov, S, tb1, filter, ncap, nlook, nquant) by {
          assert LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst1, s1, ncap, nlook, nquant);
          assert bst1 == PT.PTS(inp1, ta1, best1, tb1, seen1);
          assert LC.AdvanceInput(inp1, WP.Forward).Some?;
        }
        assert LookNestBackRepCTopDeep(rer, re, crv, str, ov, S, tb1, s4.active, ncap, nlook, nquant) by {
          assert s4.active == PSM.ResumeAll(filter);
          ResumeAllLen(filter);
          forall i | 0 <= i < |tb1|
            ensures LookNestBackTTopDeep(rer, re, crv, str, ov, S, tb1[i].1, s4.active[i], ncap, nlook, nquant)
          {
            assert LookNestBackTTopDeep(rer, re, crv, str, ov, S, tb1[i].1, filter[i].0, ncap, nlook, nquant);
            ResumeAllIndex(filter, i);
            assert s4.active[i] == filter[i].0.(exit_allowed := true, pc := filter[i].0.pc + 1);
            assert s4.active[i].look_regs == filter[i].0.look_regs
                   && s4.active[i].quant_regs == filter[i].0.quant_regs;
            LookNestBackTRegSameTopDeep(rer, re, crv, str, ov, S, tb1[i].1, tb1[i].1, filter[i].0, s4.active[i],
                                        ncap, nlook, nquant);
          }
        }
        assert LC.AdvanceInput(nextinp, WP.Forward).Some? ==>
            LookNestBackRepBTopDeep(rer, re, crv, str, ov, S, [],
                                    PIV.MatchingBlocked(LC.Reverse(s4.blocked), nextinp), ncap, nlook, nquant) by {
          assert LC.Reverse(s4.blocked) == [];
          assert PIV.MatchingBlocked([], nextinp) == [];
        }
        assert LiftInvRec(rer, qm, re, code, crv, str, ov, S, bst2, s4, ncap, nlook, nquant);

        // recurse and chain.
        bestT := LiftFindMatchCRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                   ptsA2, bst2, s4, cdn, ncap, nlook, nquant);
        TrcLkCons(bst1, bst2, PT.PTS_final(bestT));
        TrcLkTrans(bst, bst1, PT.PTS_final(bestT));
        assert AI.FFindMatch(code, str, s4, ov1, dir, cdn).0
            == AI.FFindMatch(code, str, vms, ov, dir, cdn).0;
      }
    }
  }

  lemma {:isolate_assertions} LiftInitCRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                     endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                     S: set<LG.GroupId>, tstar: LT.Tree, t: LT.Tree, inp: LC.Input, vms: AI.VmState,
                     ncap: int, nlook: int, nquant: int)
    returns (tcan: LT.Tree)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires code == CP.compile_to_bytecode(re)               // WalkOkEntry's carrier
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str,
                               PT.PikeTreeInitialState(tstar, inp), vms, ncap, nlook, nquant)
    // (L4 NESTED ENTRY) the recursive fragment replaces the depth-1
    // LookBehindFragmentRE: NestedFragmentRE + TransWf + CapUnique come from
    // StaticOkNestedRE, and NegLooksLookFreeRE is the extra hypothesis that
    // lets `TranslateFragmentPikeLkRec` establish PikeLkRegexRec(Translate(re)).
    requires PSM.StaticCoreNestedRE(qm, re, code, endl)
    requires NR.NegLooksLookFreeRE(re)
    requires AR.ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
    requires CW.BoolTreeLkX(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t)   // (§2.5b F-c) the ENGINE-SHAPED root walk
    requires EL.PikeLkRegexRec(T.Translate(re))   // (§2.5b F-c) supplied: the static package is gate-free
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires inp == PIV.InpOfCp(str, vms.cp) && 0 <= vms.cp <= |str|
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.bestmatch.None?
    requires vms.blocked == []                                // genuine start: nothing blocked yet
    requires vms.processed == AI.init_bpcset(RB.size(code))   // genuine start: nothing processed yet
    requires vms.isblocked == AI.init_pcset(RB.size(code))
    requires PIV.ContextOkRE(str, vms.cp, vms.context)
    ensures TreeRepLkRE(rer, qm, code, inp, tcan, 0, false)
    ensures CE.ProgErase(tcan) == CE.ProgErase(t)             // endpoint glue: FirstLeaf(tcan) == FirstLeaf(t)
    ensures LiftInvCRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                        PT.PikeTreeInitialState(tstar, inp), PT.PikeTreeInitialState(tcan, inp), vms,
                        ncap, nlook, nquant)
  {
    // (§2.5b/z3 4.14) recursive nullability predicates + the CIN disjunct's
    // triggered existential storm the solver; all uses here are opaque.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    // The single active pair (t, init_thread) ties via ThreadRepLk (THREAD-
    // anchored — no tstar↔t tree link); the payload is vacuous because a fresh
    // thread denotes Empty. PikeInvFullRE(ptsA, vms) is the hypothesis.
    PIV.GmOfLiveInit(re, ncap, nlook, nquant);        // GmOfLive(re, init...) == Empty
    var it := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
    var acts := [LS.Areg(T.Translate(re))];
    assert it.pc == 0 && it.exit_allowed == false;
    assert it.capture_regs == AReg.init_regs(ncap)
           && it.look_regs == AReg.init_regs(nlook) && it.quant_regs == AReg.init_regs(nquant);
    EL.PikeLkActionsRecConsIff(LS.Areg(T.Translate(re)), []);
    assert EL.PikeLkActionsRec(acts);
    assert GateAheadClear(acts, LG.Empty);              // Empty has no keys
    TranslateDefGroupsNoDup(re);                        // NoDupSeq(DefGroups(Translate(re)))
    WalkDefsOkEntry(T.Translate(re));
    M.AllDefsActsCons(LS.Areg(T.Translate(re)), []);
    assert M.AllDefsActs(acts) == L.DefGroups(T.Translate(re));   // AllDefsActs([]) == []
    assert WalkPairLkRec(rer, qm, code, inp, t, LG.Empty, it.pc as nat, it.exit_allowed) by {
      assert it.pc as nat == 0;
      assert AR.ActionsRepL(rer, qm, acts, code, 0);
      assert ATR.EaOf(BS.CannotExit) == it.exit_allowed;   // both false
      assert CW.BoolTreeLkX(rer, acts, inp, BS.CannotExit, t);
      assert exists actsw: LS.Actions, bw: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, actsw, code, it.pc as nat)
          && EL.PikeLkActionsRec(actsw)
          && ATR.EaOf(bw) == it.exit_allowed
          && CW.BoolTreeLkX(rer, actsw, inp, bw, t)
          && GateAheadClear(actsw, LG.Empty)
          && WalkDefsOk(actsw);
    }
    assert GmtTieOutside(re, it, LG.Empty, S);          // gml == Empty, agrees with Empty
    assert ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, t, LG.Empty, it, ncap, nlook, nquant);
    // Construct machine B's PLANTED CANONICAL entry tree; the raw walk tree
    // `t` is its value-layer erasure witness.
    WkE.WalkOkEntryNested(re);
    assert WO.WalkOk(acts, code, 0, false);
    assert ATR.EaOf(BS.CannotExit) == false;
    tcan := ActionsTreeRepLkRERec(rer, qm, acts, code, 0, inp, BS.CannotExit, t);
    assert ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, tcan, LG.Empty, it,
                           ncap, nlook, nquant) by {
      assert TreeRepLkRE(rer, qm, code, inp, tcan, it.pc as nat, it.exit_allowed);
      assert CE.ProgErase(t) == CE.ProgErase(tcan)
             && ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, t, LG.Empty, it, ncap, nlook, nquant);
    }
    assert ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, [(tcan, LG.Empty)], [it], ncap, nlook, nquant);
    // ptsB = PTS(inp, [(tcan, Empty)], None, [], InitialSeenTrees); best None both sides.
    assert PT.PikeTreeInitialState(tcan, inp) == PT.PTS(inp, [(tcan, LG.Empty)], None, [], SS.InitialSeenTrees);
    assert PT.PikeTreeInitialState(tstar, inp).PTS? && PT.PikeTreeInitialState(tstar, inp).inp == inp;
    assert BestTieLkNestedTop(rer, re, crv, str, ov, S, None, vms.bestmatch, ncap, nlook, nquant);
    // Blocked: genuine start — both sides empty.
    assert PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp) == [];
    forall nextinp | LC.AdvanceInput(inp, WP.Forward) == Some(nextinp)
      ensures BlockedRepLkCRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, [],
                               PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant)
    { }
    // B-side seen ↔ processed: at the genuine start nothing is processed, so
    // `SeenRepLk` holds vacuously (mirror of `PIV.InitialInclusionRE`).
    InitialSeenRepLk(rer, qm, code, inp,
                     PIV.HdTreeOf([(tcan, LG.Empty)]), PIV.HeadPcOf([it]), RB.size(code));
    // (§2.5b/z3 4.14) assemble the Rec invariant's conjuncts explicitly — the
    // packed LiftInvCRec ensures VC grinds past 900 s otherwise.
    assert LookNestRepCTop(re, S, [(tcan, LG.Empty)], [it]);
    assert LookNestBackRepCTop(re, crv, str, ov, S, [(tcan, LG.Empty)], [it], ncap, nlook, nquant);
    assert LookNestBackRepCTopDeep(rer, re, crv, str, ov, S, [(tcan, LG.Empty)], [it], ncap, nlook, nquant);
    forall nextinp | LC.AdvanceInput(inp, WP.Forward) == Some(nextinp)
      ensures LookNestRepBTop(re, S, [], PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp))
           && LookNestBackRepBTop(re, crv, str, ov, S, [],
                                  PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant)
           && LookNestBackRepBTopDeep(rer, re, crv, str, ov, S, [],
                                      PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant)
    {
      assert PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp) == [];
    }
    assert IsblockedRepLk(rer, qm, code, inp, SS.InitialSeenTrees, vms.isblocked);
    assert LiftInvRec(rer, qm, re, code, crv, str, ov, S,
                      PT.PikeTreeInitialState(tcan, inp), vms, ncap, nlook, nquant);
  }

  lemma L3aCompositeCloseRecG(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                             endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                             S: set<LG.GroupId>, tstar: LT.Tree, t: LT.Tree, inp: LC.Input,
                             vms: AI.VmState, cdn: LCdn.cdns, result: Option<AI.Thread>,
                             ncap: int, nlook: int, nquant: int, G: set<LG.GroupId>)
    returns (bleaf: Option<LT.Leaf>)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires |ov| == |str| + 1                                    // L3b: propagate to the backward LB gate
    requires OE.OracleColsOk(rer, qm, str)                    // (L5 F7d) whole-string oracle correctness (backward keystone)
    requires PSM.StaticCoreNestedRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.multiline
    requires !rer.ignoreCase
    requires S == PIV.CapIdsInLooks(re)
    // (BRICK D5) NON-VACUITY: the composite sim's per-lid static package is the
    // depth-AGNOSTIC `GateStaticsOkNested` (nested gate bodies) under the positive-
    // lookahead-nesting scope `M.NoPosLookbehindRE(re)` — this driver is now
    // NON-VACUOUS at nesting depth >= 2.
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires NR.L5ScopeRE(re) && L5ScopeV1RE(re)   // (L5 F7f) the v1 L5 scope
    requires LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires code == CP.compile_to_bytecode(re)
    requires vms.blocked == []
    requires vms.processed == AI.init_bpcset(RB.size(code))
    requires vms.isblocked == AI.init_pcset(RB.size(code))
    requires PIV.ContextOkRE(str, vms.cp, vms.context)
    // Thread-anchored entry facts (feed LiftInitC) — replace the dead
    // LeavesAgreeAtOutside(tstar, t) tree link.
    requires T.TransWf(re) && NR.NegLooksLookFreeRE(re)
    requires AR.ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
    requires EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t)
    // (§2.5b F-c) the CIN bodies' groups lie in G (glue side condition)
    requires EL.PikeLkRegexRec(T.Translate(re))
    requires CW.CinOk(T.Translate(re), G)
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str,
                               PT.PikeTreeInitialState(tstar, inp), vms, ncap, nlook, nquant)
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires inp == PIV.InpOfCp(str, vms.cp) && 0 <= vms.cp <= |str|
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.bestmatch.None?
    requires |vms.processed.true_set| == RB.size(code) && |vms.processed.false_set| == RB.size(code)
    requires vms.context.nextchar == AI.get_char(str, vms.cp)
    requires result == AI.FFindMatch(code, str, vms, ov, LAnc.Forward, cdn).0
    // (§2.5b F-c) machine B's best leaf is the ENGINE-SHAPED tree's first leaf;
    // it agrees with the spec tree's at the position and OUTSIDE G
    ensures BestTieLkNestedTop(rer, re, crv, str, ov, S, bleaf, result, ncap, nlook, nquant)
    ensures (bleaf.None? <==> LT.FirstLeaf(t, inp).None?)
    ensures bleaf.Some? ==> bleaf.value.0 == LT.FirstLeaf(t, inp).value.0
                            && LL.GmAgreeOutside(bleaf.value.1, LT.FirstLeaf(t, inp).value.1, G)
  {
    var acts := [LS.Areg(T.Translate(re))];
    assert EL.PikeLkActionsRec(acts) by {
      assert acts == [LS.Areg(T.Translate(re))] + [];
      EL.PikeLkActionsRecConsIff(LS.Areg(T.Translate(re)), []);
    }
    NB.EncOkNoChecks(acts, inp, BS.CannotExit);
    CW.CinActsInSingle(T.Translate(re), G);
    var tX := CW.CinWalkX(rer, acts, inp, BS.CannotExit, t, G);
    var tcan := LiftInitCRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S, tstar, tX, inp, vms,
                             ncap, nlook, nquant);
    assert LiftInvRec(rer, qm, re, code, crv, str, ov, S,
                      PT.PikeTreeInitialState(tcan, inp), vms, ncap, nlook, nquant);
    // (L4 GENUINELY NESTED) the whole chain is nested-typed and driven by the
    // RECURSIVE walk: the entry (LiftInitCRec) builds WalkPairLkRec directly, so
    // no StaticOkRE bridge is needed -- StaticOkNestedRE feeds the tier as-is.
    var bestT := LiftFindMatchCRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                                   PT.PikeTreeInitialState(tstar, inp),
                                   PT.PikeTreeInitialState(tcan, inp),
                                   vms, cdn, ncap, nlook, nquant);
    // bestT IS the canonical tree's first leaf ...
    BoolTreeLkXPikeSubtree(rer, acts, inp, BS.CannotExit, tX);
    PikeSubtreeLkEraseIff(tX);
    PikeSubtreeLkEraseIff(tcan);
    assert PTL.PikeSubtreeLk(tcan);
    PTL.PikeTreeLkComputesFirstLeaf(tcan, inp, bestT);
    assert bestT == LT.FirstLeaf(tcan, inp);
    // ... which is the ENGINE-SHAPED entry walk's first leaf (Progress is leaf-transparent)
    assert CE.LeavesAgree(tcan, tX) by {
      forall gm: LG.GroupMap, xinp: LC.Input, dr: WP.Direction
        ensures LT.TreeLeaves(tcan, gm, xinp, dr) == LT.TreeLeaves(tX, gm, xinp, dr)
      {
        ProgEraseLeavesEq(tcan, gm, xinp, dr);
        ProgEraseLeavesEq(tX, gm, xinp, dr);
      }
    }
    CE.LAFirstLeaf(tcan, tX, inp);
    assert LT.FirstLeaf(tX, inp) == bestT;
    bleaf := bestT;
    // ... and the glue relates it to the spec tree's
    NB.RAFirstLeafOutside(tX, t, inp, G);
  }
  /** The gated entry (no nulled plus anywhere): the engine-shaped walk IS the
      spec walk at the first leaf — `L3aCompositeCloseRecG` at `G = {}`. */
  lemma L3aCompositeCloseRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                             endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                             S: set<LG.GroupId>, tstar: LT.Tree, t: LT.Tree, inp: LC.Input,
                             vms: AI.VmState, cdn: LCdn.cdns, result: Option<AI.Thread>,
                             ncap: int, nlook: int, nquant: int)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires |ov| == |str| + 1
    requires OE.OracleColsOk(rer, qm, str)
    requires PSM.StaticOkNestedRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.multiline
    requires !rer.ignoreCase
    requires S == PIV.CapIdsInLooks(re)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires NR.L5ScopeRE(re) && L5ScopeV1RE(re)
    requires LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires code == CP.compile_to_bytecode(re)
    requires vms.blocked == []
    requires vms.processed == AI.init_bpcset(RB.size(code))
    requires vms.isblocked == AI.init_pcset(RB.size(code))
    requires PIV.ContextOkRE(str, vms.cp, vms.context)
    requires T.TransWf(re) && NR.NegLooksLookFreeRE(re)
    requires AR.ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
    requires EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t)
    requires PTL.PikeSubtreeLk(t)
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str,
                               PT.PikeTreeInitialState(tstar, inp), vms, ncap, nlook, nquant)
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires inp == PIV.InpOfCp(str, vms.cp) && 0 <= vms.cp <= |str|
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.bestmatch.None?
    requires |vms.processed.true_set| == RB.size(code) && |vms.processed.false_set| == RB.size(code)
    requires vms.context.nextchar == AI.get_char(str, vms.cp)
    requires result == AI.FFindMatch(code, str, vms, ov, LAnc.Forward, cdn).0
    ensures BestTieLkNestedTop(rer, re, crv, str, ov, S, LT.FirstLeaf(t, inp), result, ncap, nlook, nquant)
  {
    EL.TranslateFragmentPikeLkRec(re);
    NUL.TransNoNulledPlus(re);
    CW.NoNulledPlusCinOk(T.Translate(re), {});
    var bleaf := L3aCompositeCloseRecG(rer, qm, re, code, endl, ngroups, crv, str, ov, S, tstar, t, inp,
                                       vms, cdn, result, ncap, nlook, nquant, {});
    var fl := LT.FirstLeaf(t, inp);
    assert bleaf == fl by {
      if bleaf.Some? {
        assert LL.GmAgreeOutside(bleaf.value.1, fl.value.1, {});
        assert bleaf.value.1 == fl.value.1 by {
          forall g ensures (g in bleaf.value.1 <==> g in fl.value.1)
                           && (g in bleaf.value.1 ==> bleaf.value.1[g] == fl.value.1[g]) {
            assert g !in {};
          }
        }
      }
    }
  }


}
