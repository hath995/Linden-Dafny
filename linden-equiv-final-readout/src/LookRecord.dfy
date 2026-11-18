// (G4b-2) The engine-side LOOK RECORD of a nulled-plus replay.
//
// A capturing lookaround on the empty path of a nullable plus body is written by the reconstruction
// (`NRC.NulledWrites` / `FNulledChildren`), not by the VM. This file says what that record is:
//   §1  `PathLooksR`: the positive lids on the first empty path, tied to the Linden Lk-path
//       (`NPL.FirstEmptyPathLkL`): `PathLooksSteps` (sound + complete w.r.t. `NPL.Crossed`), `PathLooksInE`.
//   §2  `EngineLookReadout`: in `NRR.EngineReadout`'s frame, an on-path lid gets the record `(cp, clk > K)`,
//       is present (`NI.LookPathPresent`) and dominates its threshold (`NI.MxAtLidLk`); an off-path lid
//       keeps its record or is not present (a stale stamped child replayed by `FNulledChildren` writes
//       under its own stale quantifier).
//   §3  `LookRecordOk` / `ReconLookRecord`: the same at the `FNulledPlus` level, per machine-A-live stamp.
//   §4  `LookPathPresentThroughQ`, `DeadStampKillsPresence`, `LooksQEUnderStamp`.
module LindenElkLookRecord {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import RA = Anchors
  import LCdn = Cdn
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LW = WarblreRegExpRecord
  import LN = WarblreNumeric
  import LS = Semantics
  import T = LindenElkTranslate
  import NUL = LindenElkNullable
  import AR = LindenElkActionsRep
  import TR = LindenElkTreeRep
  import PIV = LindenElkPikeInv
  import NI = LindenElkNestInv
  import LTB = LindenElkLookTables
  import LL = LindenElkLookLeaves
  import NP = LindenElkNulledPlus
  import NT = LindenElkNulledPlusTie
  import NPL = LindenElkNulledPlusLk
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import NRO = LindenElkNulledReconReadout
  import RF = LindenElkReconFrame
  import CLP = LindenElkCinLookPaths
  import SL = LindenElkStampLive
  import ELk = LindenElkEmptyLooks
  type Regs3 = NRC.Regs3

  // ===========================================================================
  // 1. The positive lids on the first empty path
  // ===========================================================================

  /** The positive lids on the first empty path (the look twin of `NRR.PathGroupsR`). */
  ghost function PathLooksR(qm: AR.QMap, re: R.regex, inp: LC.Input): set<nat>
    requires T.TransWf(re)
    decreases re
  {
    match re
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) =>
      if TR.FirstEmptyPathR(qm, r1, inp).Some? then PathLooksR(qm, r1, inp) else PathLooksR(qm, r2, inp)
    case Re_con(r1, r2) => PathLooksR(qm, r1, inp) + PathLooksR(qm, r2, inp)
    case Re_quant(_, _, q, r1) => if q.min == 0 then {} else PathLooksR(qm, r1, inp)
    case Re_capture(_, r1) => PathLooksR(qm, r1, inp)
    case Re_lookaround(lid, la, _) => if NRC.PositiveLk(la) && lid >= 0 then {lid as nat} else {}
  }

  /** The flavour of the `lid`-labelled lookaround node (the twin of `NI.LookBodyOfRE`). */
  ghost function LookLaOfRE(r: R.regex, lid: nat): R.lookaround
    requires lid in LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if lid in LTB.LookIds(r1) then LookLaOfRE(r1, lid) else LookLaOfRE(r2, lid)
    case Re_con(r1, r2) => if lid in LTB.LookIds(r1) then LookLaOfRE(r1, lid) else LookLaOfRE(r2, lid)
    case Re_quant(_, _, _, r1) => LookLaOfRE(r1, lid)
    case Re_capture(_, r1) => LookLaOfRE(r1, lid)
    case Re_lookaround(lid0, la, r1) => if lid0 >= 0 && (lid0 as nat) == lid then la else LookLaOfRE(r1, lid)
    case _ => R.Lookahead
  }

  lemma LookBodyTransWf(r: R.regex, lid: nat)
    requires T.TransWf(r) && lid in LTB.LookIds(r)
    ensures T.TransWf(NI.LookBodyOfRE(r, lid))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if lid in LTB.LookIds(r1) { LookBodyTransWf(r1, lid); } else { LookBodyTransWf(r2, lid); }
    case Re_con(r1, r2) => if lid in LTB.LookIds(r1) { LookBodyTransWf(r1, lid); } else { LookBodyTransWf(r2, lid); }
    case Re_quant(_, _, _, r1) => LookBodyTransWf(r1, lid);
    case Re_capture(_, r1) => LookBodyTransWf(r1, lid);
    case Re_lookaround(lid0, _, r1) => if !(lid0 >= 0 && (lid0 as nat) == lid) { LookBodyTransWf(r1, lid); }
    case _ =>
  }

  /** The Lk-path step of the `lid` node: its translated flavour and body. */
  ghost function LkStepOf(re: R.regex, lid: nat): NPL.Step
    requires T.TransWf(re) && lid in LTB.LookIds(re)
  {
    LookBodyTransWf(re, lid);
    NPL.LkS(T.TrLookaround(LookLaOfRE(re, lid)), T.Translate(NI.LookBodyOfRE(re, lid)))
  }

  /** `LkStepOf` at the immediate subterm holding `lid`. */
  lemma LkStepOfChild(re: R.regex, lid: nat)
    requires T.TransWf(re) && lid in LTB.LookIds(re)
    ensures (re.Re_alt? || re.Re_con?) && lid in LTB.LookIds(NRR.L1(re)) ==> LkStepOf(re, lid) == LkStepOf(NRR.L1(re), lid)
    ensures (re.Re_alt? || re.Re_con?) && lid !in LTB.LookIds(NRR.L1(re)) ==>
              lid in LTB.LookIds(NRR.L2(re)) && LkStepOf(re, lid) == LkStepOf(NRR.L2(re), lid)
    ensures re.Re_quant? || re.Re_capture? ==> LkStepOf(re, lid) == LkStepOf(NRR.L1(re), lid)
    ensures re.Re_lookaround? && re.lid >= 0 && (re.lid as nat) == lid ==>
              LkStepOf(re, lid) == NPL.LkS(T.TrLookaround(re.look), T.Translate(re.lr))
  {}

  /** The path lids are top-level look ids. */
  lemma PathLooksInTop(qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires T.TransWf(re)
    ensures PathLooksR(qm, re, inp) <= NI.TopLookIds(re) && PathLooksR(qm, re, inp) <= LTB.LookIds(re)
    decreases re
  {
    NI.TopLookIdsIn(re);
    match re
    case Re_alt(r1, r2) => PathLooksInTop(qm, r1, inp); PathLooksInTop(qm, r2, inp);
    case Re_con(r1, r2) => PathLooksInTop(qm, r1, inp); PathLooksInTop(qm, r2, inp);
    case Re_quant(_, _, _, r1) => PathLooksInTop(qm, r1, inp);
    case Re_capture(_, r1) => PathLooksInTop(qm, r1, inp);
    case _ =>
  }

  /** The path lids are positive lookarounds. */
  lemma PathLooksPositive(qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires T.TransWf(re) && LTB.LookUnique(re)
    ensures forall l: nat :: l in PathLooksR(qm, re, inp) ==> l in LTB.LookIds(re) && NRC.PositiveLk(LookLaOfRE(re, l))
    decreases re
  {
    PathLooksInTop(qm, re, inp);
    match re
    case Re_alt(r1, r2) =>
      PathLooksPositive(qm, r1, inp); PathLooksPositive(qm, r2, inp);
      PathLooksInTop(qm, r1, inp); PathLooksInTop(qm, r2, inp);
    case Re_con(r1, r2) =>
      PathLooksPositive(qm, r1, inp); PathLooksPositive(qm, r2, inp);
      PathLooksInTop(qm, r1, inp); PathLooksInTop(qm, r2, inp);
    case Re_quant(_, _, _, r1) => PathLooksPositive(qm, r1, inp);
    case Re_capture(_, r1) => PathLooksPositive(qm, r1, inp);
    case _ =>
  }

  // ---- the shape of the Lk-path, one constructor at a time (cont = []) ----

  lemma LkPathAlt(rer: LW.RegExpRecord, t1: L.Regex, t2: L.Regex, inp: LC.Input)
    ensures NPL.FirstEmptyPathLkL(rer, L.Disjunction(t1, t2), inp)
         == (match NPL.FirstEmptyPathLkL(rer, t1, inp) case Some(p) => Some(p) case None => NPL.FirstEmptyPathLkL(rer, t2, inp))
  {
    var r := L.Disjunction(t1, t2);
    var solo := [LS.Areg(r)];
    assert solo[0] == LS.Areg(r) && solo[1..] == [];
    assert [LS.Areg(t1)] + [] == [LS.Areg(t1)] && [LS.Areg(t2)] + [] == [LS.Areg(t2)];
  }

  lemma LkPathSeq(rer: LW.RegExpRecord, t1: L.Regex, t2: L.Regex, inp: LC.Input)
    ensures NPL.FirstEmptyPathLkL(rer, L.Sequence(t1, t2), inp)
         == NPL.CompPathLk(NPL.FirstEmptyPathLkL(rer, t1, inp), NPL.FirstEmptyPathLkL(rer, t2, inp))
  {
    var r := L.Sequence(t1, t2);
    var solo := [LS.Areg(r)];
    assert solo[0] == LS.Areg(r) && solo[1..] == [];
    assert [LS.Areg(t1), LS.Areg(t2)] + [] == [LS.Areg(t1)] + [LS.Areg(t2)];
    assert [LS.Areg(t2)] + [] == [LS.Areg(t2)];
    NPL.FirstEmptyPathLkAComp(rer, t1, [LS.Areg(t2)], inp);
    assert NPL.FirstEmptyPathLkL(rer, r, inp) == NPL.FirstEmptyPathLkA(rer, [LS.Areg(t1), LS.Areg(t2)] + [], inp);
  }

  lemma LkPathGroup(rer: LW.RegExpRecord, gid: nat, t1: L.Regex, inp: LC.Input)
    ensures NPL.FirstEmptyPathLkL(rer, L.Group(gid, t1), inp)
         == NPL.PrePathLk(NPL.GA(LG.Open(gid)), NPL.CompPathLk(NPL.FirstEmptyPathLkL(rer, t1, inp), Some([NPL.GA(LG.Close(gid))])))
  {
    var r := L.Group(gid, t1);
    var solo := [LS.Areg(r)];
    assert solo[0] == LS.Areg(r) && solo[1..] == [];
    assert NPL.FirstEmptyPathLkA(rer, [], inp) == Some([]);
    assert [LS.Areg(t1), LS.Aclose(gid)] + [] == [LS.Areg(t1)] + [LS.Aclose(gid)];
    assert [LS.Aclose(gid)][0] == LS.Aclose(gid) && [LS.Aclose(gid)][1..] == [];
    assert [NPL.GA(LG.Close(gid))] + [] == [NPL.GA(LG.Close(gid))];
    assert NPL.FirstEmptyPathLkA(rer, [LS.Aclose(gid)], inp) == Some([NPL.GA(LG.Close(gid))]);
    NPL.FirstEmptyPathLkAComp(rer, t1, [LS.Aclose(gid)], inp);
    assert NPL.FirstEmptyPathLkL(rer, r, inp)
        == NPL.PrePathLk(NPL.GA(LG.Open(gid)), NPL.FirstEmptyPathLkA(rer, [LS.Areg(t1), LS.Aclose(gid)] + [], inp));
  }

  lemma LkPathLook(rer: LW.RegExpRecord, lk: L.Lookaround, t1: L.Regex, inp: LC.Input)
    ensures NPL.FirstEmptyPathLkL(rer, L.LookaroundR(lk, t1), inp)
         == (if NP.LkVerdictL(rer, lk, t1, inp) then Some([NPL.LkS(lk, t1)]) else None)
  {
    var r := L.LookaroundR(lk, t1);
    var solo := [LS.Areg(r)];
    assert solo[0] == LS.Areg(r) && solo[1..] == [];
    assert NPL.FirstEmptyPathLkA(rer, [], inp) == Some([]);
    assert [NPL.LkS(lk, t1)] + [] == [NPL.LkS(lk, t1)];
  }

  lemma LkPathLeaf(rer: LW.RegExpRecord, t: L.Regex, inp: LC.Input)
    requires t.Epsilon? || t.Character? || t.AnchorR?
    ensures NPL.FirstEmptyPathLkL(rer, t, inp).Some? ==> NPL.FirstEmptyPathLkL(rer, t, inp).value == []
  {
    var solo := [LS.Areg(t)];
    assert solo[0] == LS.Areg(t) && solo[1..] == [];
    assert NPL.FirstEmptyPathLkA(rer, [], inp) == Some([]);
  }

  /** The Lk twin of `NT.FirstEmptyPathLQuant`, as a statement about the path's STEPS: a forced quantifier's
      path is some repetitions of `Reset` + the body's path, so its steps are the body's plus the reset. */
  lemma LkPathQuant(rer: LW.RegExpRecord, greedy: bool, min: nat, delta: LN.NoI, t1: L.Regex, inp: LC.Input)
    ensures var p := NPL.FirstEmptyPathLkL(rer, L.Quantified(greedy, min, delta, t1), inp);
            var p1 := NPL.FirstEmptyPathLkL(rer, t1, inp);
            (min == 0 ==> p == Some([]))
            && (min > 0 ==> (p.Some? <==> p1.Some?)
                            && (p.Some? ==> forall s :: s in p.value <==> s == NPL.GA(LG.Reset(L.DefGroups(t1))) || s in p1.value))
    decreases min
  {
    var r := L.Quantified(greedy, min, delta, t1);
    var solo := [LS.Areg(r)];
    assert solo[0] == LS.Areg(r) && solo[1..] == [];
    assert NPL.FirstEmptyPathLkA(rer, [], inp) == Some([]);
    if min > 0 {
      var gidl := L.DefGroups(t1);
      var qn := L.Quantified(greedy, min - 1, delta, t1);
      assert [LS.Areg(t1), LS.Areg(qn)] + [] == [LS.Areg(t1)] + [LS.Areg(qn)];
      assert [LS.Areg(qn)] + [] == [LS.Areg(qn)];
      NPL.FirstEmptyPathLkAComp(rer, t1, [LS.Areg(qn)], inp);
      LkPathQuant(rer, greedy, min - 1, delta, t1, inp);
      var p1 := NPL.FirstEmptyPathLkL(rer, t1, inp);
      var pn := NPL.FirstEmptyPathLkL(rer, qn, inp);
      assert NPL.FirstEmptyPathLkA(rer, [LS.Areg(qn)], inp) == pn;
      assert NPL.FirstEmptyPathLkL(rer, r, inp)
          == NPL.PrePathLk(NPL.GA(LG.Reset(gidl)), NPL.FirstEmptyPathLkA(rer, [LS.Areg(t1), LS.Areg(qn)] + [], inp));
      assert NPL.FirstEmptyPathLkL(rer, r, inp) == NPL.PrePathLk(NPL.GA(LG.Reset(gidl)), NPL.CompPathLk(p1, pn));
    }
  }

  /** The Lk-path exists exactly when the oracle-bit path does. */
  lemma LkPathSomeIff(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires !rer.multiline && T.TransWf(re) && AR.LmapOk(re, qm) && LL.OracleOkAt(rer, qm, inp)
    ensures NPL.FirstEmptyPathLkL(rer, T.Translate(re), inp).Some? <==> TR.FirstEmptyPathR(qm, re, inp).Some?
  {
    NPL.ProjPath(rer, [LS.Areg(T.Translate(re))], inp);
    NT.FirstEmptyPathRL(rer, qm, re, inp);
  }

  /** The step-level tie: every path lid's step is on the Lk-path, and every positive look step of the
      Lk-path is a path lid's. */
  ghost predicate StepsTie(qm: AR.QMap, re: R.regex, inp: LC.Input, p: seq<NPL.Step>)
    requires T.TransWf(re)
  {
    (forall l: nat :: l in PathLooksR(qm, re, inp) ==> l in LTB.LookIds(re) && LkStepOf(re, l) in p)
    && (forall s :: s in p && s.LkS? && L.Positivity(s.lk) ==>
          exists l: nat :: l in PathLooksR(qm, re, inp) && l in LTB.LookIds(re) && s == LkStepOf(re, l))
  }

  lemma PathLooksStepsRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires !rer.multiline && T.TransWf(re) && AR.LmapOk(re, qm) && LL.OracleOkAt(rer, qm, inp)
    requires LTB.LookUnique(re)
    ensures var p := NPL.FirstEmptyPathLkL(rer, T.Translate(re), inp);
            (p.Some? <==> TR.FirstEmptyPathR(qm, re, inp).Some?)
            && (p.Some? ==> StepsTie(qm, re, inp, p.value))
    decreases re
  {
    LkPathSomeIff(rer, qm, re, inp);
    PathLooksInTop(qm, re, inp);
    var tr := T.Translate(re);
    var p := NPL.FirstEmptyPathLkL(rer, tr, inp);
    match re
    case Re_empty => LkPathLeaf(rer, tr, inp);
    case Re_character(_) => LkPathLeaf(rer, tr, inp);
    case Re_anchor(_) => LkPathLeaf(rer, tr, inp);
    case Re_alt(r1, r2) =>
      assert {:split_here} true;
      PathLooksStepsRec(rer, qm, r1, inp);
      PathLooksStepsRec(rer, qm, r2, inp);
      PathLooksInTop(qm, r1, inp); PathLooksInTop(qm, r2, inp);
      LkPathAlt(rer, T.Translate(r1), T.Translate(r2), inp);
      if p.Some? {
        forall l: nat | l in LTB.LookIds(re) { LkStepOfChild(re, l); }
        if TR.FirstEmptyPathR(qm, r1, inp).Some? {
          assert StepsTie(qm, r1, inp, p.value);
        } else {
          assert StepsTie(qm, r2, inp, p.value);
          assert forall l: nat :: l in PathLooksR(qm, r2, inp) ==> l !in LTB.LookIds(r1);
        }
      }
    case Re_con(r1, r2) =>
      assert {:split_here} true;
      PathLooksStepsRec(rer, qm, r1, inp);
      PathLooksStepsRec(rer, qm, r2, inp);
      PathLooksInTop(qm, r1, inp); PathLooksInTop(qm, r2, inp);
      LkPathSeq(rer, T.Translate(r1), T.Translate(r2), inp);
      if p.Some? {
        var p1 := NPL.FirstEmptyPathLkL(rer, T.Translate(r1), inp).value;
        var p2 := NPL.FirstEmptyPathLkL(rer, T.Translate(r2), inp).value;
        assert p.value == p1 + p2;
        assert StepsTie(qm, r1, inp, p1) && StepsTie(qm, r2, inp, p2);
        forall l: nat | l in LTB.LookIds(re) { LkStepOfChild(re, l); }
        assert forall l: nat :: l in PathLooksR(qm, r2, inp) ==> l !in LTB.LookIds(r1);
        forall s | s in p.value && s.LkS? && L.Positivity(s.lk)
          ensures exists l: nat :: l in PathLooksR(qm, re, inp) && l in LTB.LookIds(re) && s == LkStepOf(re, l)
        {
          if s in p1 {
            var l: nat :| l in PathLooksR(qm, r1, inp) && l in LTB.LookIds(r1) && s == LkStepOf(r1, l);
            assert l in PathLooksR(qm, re, inp) && s == LkStepOf(re, l);
          } else {
            assert s in p2;
            var l: nat :| l in PathLooksR(qm, r2, inp) && l in LTB.LookIds(r2) && s == LkStepOf(r2, l);
            assert l in PathLooksR(qm, re, inp) && s == LkStepOf(re, l);
          }
        }
      }
    case Re_quant(nul, qid, q, r1) =>
      assert {:split_here} true;
      PathLooksStepsRec(rer, qm, r1, inp);
      PathLooksInTop(qm, r1, inp);
      var t1 := T.Translate(r1);
      assert tr == L.Quantified(q.greedy, q.min as nat, T.TrDelta(q), t1);
      LkPathQuant(rer, q.greedy, q.min as nat, T.TrDelta(q), t1, inp);
      if p.Some? && q.min != 0 {
        var p1 := NPL.FirstEmptyPathLkL(rer, t1, inp).value;
        assert StepsTie(qm, r1, inp, p1);
        forall l: nat | l in LTB.LookIds(re) { LkStepOfChild(re, l); }
        forall s | s in p.value && s.LkS? && L.Positivity(s.lk)
          ensures exists l: nat :: l in PathLooksR(qm, re, inp) && l in LTB.LookIds(re) && s == LkStepOf(re, l)
        {
          assert s in p1;
          var l: nat :| l in PathLooksR(qm, r1, inp) && l in LTB.LookIds(r1) && s == LkStepOf(r1, l);
          assert l in PathLooksR(qm, re, inp) && s == LkStepOf(re, l);
        }
      }
    case Re_capture(cid, r1) =>
      assert {:split_here} true;
      PathLooksStepsRec(rer, qm, r1, inp);
      PathLooksInTop(qm, r1, inp);
      var t1 := T.Translate(r1);
      var gid: nat := cid as nat;
      assert tr == L.Group(gid, t1);
      LkPathGroup(rer, gid, t1, inp);
      if p.Some? {
        var p1 := NPL.FirstEmptyPathLkL(rer, t1, inp).value;
        assert p.value == [NPL.GA(LG.Open(gid))] + (p1 + [NPL.GA(LG.Close(gid))]);
        assert StepsTie(qm, r1, inp, p1);
        forall l: nat | l in LTB.LookIds(re) { LkStepOfChild(re, l); }
        forall s | s in p.value && s.LkS? && L.Positivity(s.lk)
          ensures exists l: nat :: l in PathLooksR(qm, re, inp) && l in LTB.LookIds(re) && s == LkStepOf(re, l)
        {
          assert s in p1;
          var l: nat :| l in PathLooksR(qm, r1, inp) && l in LTB.LookIds(r1) && s == LkStepOf(r1, l);
          assert l in PathLooksR(qm, re, inp) && s == LkStepOf(re, l);
        }
      }
    case Re_lookaround(lid, la, r1) =>
      assert {:split_here} true;
      var lkL := T.TrLookaround(la);
      var t1 := T.Translate(r1);
      assert tr == L.LookaroundR(lkL, t1);
      LkPathLook(rer, lkL, t1, inp);
      assert lid >= 0;
      LkStepOfChild(re, lid as nat);
      assert L.Positivity(lkL) <==> NRC.PositiveLk(la);
      if p.Some? {
        assert p.value == [NPL.LkS(lkL, t1)];
        assert forall s :: s in p.value ==> s == NPL.LkS(lkL, t1);
      }
  }

  /** `g ∈ DefGroups(Translate(r))` names a capture of `r`. */
  lemma DefGroupsInCapIds(r: R.regex, g: nat)
    requires T.TransWf(r) && g in L.DefGroups(T.Translate(r))
    ensures g in PIV.CapIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if g in L.DefGroups(T.Translate(r1)) { DefGroupsInCapIds(r1, g); } else { DefGroupsInCapIds(r2, g); }
    case Re_con(r1, r2) => if g in L.DefGroups(T.Translate(r1)) { DefGroupsInCapIds(r1, g); } else { DefGroupsInCapIds(r2, g); }
    case Re_quant(_, _, _, r1) => DefGroupsInCapIds(r1, g);
    case Re_capture(cid, r1) => if g != cid as nat { DefGroupsInCapIds(r1, g); }
    case Re_lookaround(_, _, r1) => DefGroupsInCapIds(r1, g);
    case _ =>
  }

  /** Under `CapUnique`, a group lies in the body of at most one TOP-LEVEL look. */
  lemma TopLookBodiesCapDisjoint(re: R.regex, l1: nat, l2: nat, g: nat)
    requires PIV.CapUnique(re) && LTB.LookUnique(re)
    requires l1 in NI.TopLookIds(re) && l2 in NI.TopLookIds(re) && l1 in LTB.LookIds(re) && l2 in LTB.LookIds(re)
    requires g in PIV.CapIds(NI.LookBodyOfRE(re, l1)) && g in PIV.CapIds(NI.LookBodyOfRE(re, l2))
    ensures l1 == l2
    decreases re
  {
    match re
    case Re_alt(r1, r2) => TopLookBodiesCapDisjoint2(re, l1, l2, g);
    case Re_con(r1, r2) => TopLookBodiesCapDisjoint2(re, l1, l2, g);
    case Re_quant(_, _, _, r1) => TopLookBodiesCapDisjoint(r1, l1, l2, g);
    case Re_capture(_, r1) => TopLookBodiesCapDisjoint(r1, l1, l2, g);
    case _ =>
  }

  lemma TopLookBodiesCapDisjoint2(re: R.regex, l1: nat, l2: nat, g: nat)
    requires re.Re_alt? || re.Re_con?
    requires PIV.CapUnique(re) && LTB.LookUnique(re)
    requires l1 in NI.TopLookIds(re) && l2 in NI.TopLookIds(re) && l1 in LTB.LookIds(re) && l2 in LTB.LookIds(re)
    requires g in PIV.CapIds(NI.LookBodyOfRE(re, l1)) && g in PIV.CapIds(NI.LookBodyOfRE(re, l2))
    ensures l1 == l2
    decreases re, 0
  {
    var r1 := NRR.L1(re); var r2 := NRR.L2(re);
    NI.TopLookIdsIn(r1); NI.TopLookIdsIn(r2);
    assert LTB.LookIds(r1) * LTB.LookIds(r2) == {};
    assert PIV.CapIds(r1) * PIV.CapIds(r2) == {};
    var in1 := l1 in LTB.LookIds(r1); var in2 := l2 in LTB.LookIds(r1);
    if in1 { NI.LookBodyCapsIn(r1, l1); } else { NI.LookBodyCapsIn(r2, l1); }
    if in2 { NI.LookBodyCapsIn(r1, l2); } else { NI.LookBodyCapsIn(r2, l2); }
    if in1 && in2 {
      assert l1 in NI.TopLookIds(r1) && l2 in NI.TopLookIds(r1);
      TopLookBodiesCapDisjoint(r1, l1, l2, g);
    } else if !in1 && !in2 {
      assert l1 in NI.TopLookIds(r2) && l2 in NI.TopLookIds(r2);
      TopLookBodiesCapDisjoint(r2, l1, l2, g);
    } else {
      assert g in PIV.CapIds(r1) * PIV.CapIds(r2);
    }
  }

  /** L1 as a path tie: the Lk-path's positive look steps are exactly the `PathLooksR` lids' steps
      (sound), and a group the path crosses names its top look as a path lid (complete; `CapUnique`). */
  lemma PathLooksSteps(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires !rer.multiline && T.TransWf(re) && AR.LmapOk(re, qm) && LL.OracleOkAt(rer, qm, inp)
    requires TR.FirstEmptyPathR(qm, re, inp).Some? && PIV.CapUnique(re) && LTB.LookUnique(re)
    ensures var p := NPL.FirstEmptyPathLkL(rer, T.Translate(re), inp);
            p.Some?
            && (forall l: nat :: l in PathLooksR(qm, re, inp) ==>
                  l in LTB.LookIds(re) && NRC.PositiveLk(LookLaOfRE(re, l)) && LkStepOf(re, l) in p.value)
            && (forall l: nat, g: nat :: l in NI.TopLookIds(re) && l in LTB.LookIds(re)
                  && g in PIV.CapIds(NI.LookBodyOfRE(re, l)) && NPL.Crossed(p.value, g)
                  ==> l in PathLooksR(qm, re, inp))
  {
    PathLooksStepsRec(rer, qm, re, inp);
    PathLooksPositive(qm, re, inp);
    PathLooksInTop(qm, re, inp);
    var p := NPL.FirstEmptyPathLkL(rer, T.Translate(re), inp);
    assert StepsTie(qm, re, inp, p.value);
    forall l: nat, g: nat | l in NI.TopLookIds(re) && l in LTB.LookIds(re)
                  && g in PIV.CapIds(NI.LookBodyOfRE(re, l)) && NPL.Crossed(p.value, g)
      ensures l in PathLooksR(qm, re, inp)
    {
      var i :| 0 <= i < |p.value| && p.value[i].LkS? && L.Positivity(p.value[i].lk) && g in L.DefGroups(p.value[i].b);
      var s := p.value[i];
      assert s in p.value;
      var l2: nat :| l2 in PathLooksR(qm, re, inp) && l2 in LTB.LookIds(re) && s == LkStepOf(re, l2);
      LookBodyTransWf(re, l2);
      DefGroupsInCapIds(NI.LookBodyOfRE(re, l2), g);
      TopLookBodiesCapDisjoint(re, l, l2, g);
    }
  }

  /** The path lids lie in the E-sets (`ELk.OwnLooksE` / `ELk.InnerLookRegsE`): what a stamped quantifier's
      `ELk.LooksQE` collects for its body. */
  lemma PathLooksInE(qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires T.TransWf(re) && TR.FirstEmptyPathR(qm, re, inp).Some?
    ensures forall l: nat :: l in PathLooksR(qm, re, inp) ==> (l as int) in ELk.OwnLooksE(re) + ELk.InnerLookRegsE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if TR.FirstEmptyPathR(qm, r1, inp).Some? { PathLooksInE(qm, r1, inp); } else { PathLooksInE(qm, r2, inp); }
    case Re_con(r1, r2) =>
      PathLooksInE(qm, r1, inp); PathLooksInE(qm, r2, inp);
      NRR.NulledWritesIffPath(qm, r1, inp); NRR.NulledWritesIffPath(qm, r2, inp);
      ELk.NulledWritesMayNull(qm, r1, inp); ELk.NulledWritesMayNull(qm, r2, inp);
    case Re_quant(nul, _, q, r1) =>
      if q.min != 0 {
        PathLooksInE(qm, r1, inp);
        NRR.NulledWritesIffPath(qm, r1, inp);
        ELk.NulledWritesMayNull(qm, r1, inp);
        assert nul == R.nullable(r1) && nul != R.NonNullable;
      }
    case Re_capture(_, r1) => PathLooksInE(qm, r1, inp);
    case _ =>
  }

  // ===========================================================================
  // 2. The engine's look record after one replay level (`NRR.EngineReadout`'s frame)
  // ===========================================================================

  lemma LookIdsTie(r: R.regex)
    ensures NRR.LookIds(r) == LTB.LookIds(r)
    ensures forall l: nat :: (l as int) in NRR.LookRegsOf(r) <==> l in LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookIdsTie(r1); LookIdsTie(r2);
    case Re_con(r1, r2) => LookIdsTie(r1); LookIdsTie(r2);
    case Re_quant(_, _, _, r1) => LookIdsTie(r1);
    case Re_capture(_, r1) => LookIdsTie(r1);
    case Re_lookaround(_, _, r1) => LookIdsTie(r1);
    case _ =>
  }

  /** A lid lives on exactly one side of an alt/con. */
  lemma LookSidesDisjoint(r: R.regex, l: nat)
    requires (r.Re_alt? || r.Re_con?) && LTB.LookUnique(r) && l in LTB.LookIds(r)
    ensures LTB.LookUnique(NRR.L1(r)) && LTB.LookUnique(NRR.L2(r))
    ensures l in LTB.LookIds(NRR.L1(r)) ==> (l as int) !in NRR.LookRegsOf(NRR.L2(r)) && l !in LTB.LookIds(NRR.L2(r))
    ensures l !in LTB.LookIds(NRR.L1(r)) ==> l in LTB.LookIds(NRR.L2(r)) && (l as int) !in NRR.LookRegsOf(NRR.L1(r))
    ensures l in NI.TopLookIds(r) ==> (if l in LTB.LookIds(NRR.L1(r)) then l in NI.TopLookIds(NRR.L1(r)) else l in NI.TopLookIds(NRR.L2(r)))
  {
    var r1 := NRR.L1(r); var r2 := NRR.L2(r);
    LookIdsTie(r1); LookIdsTie(r2);
    NI.TopLookIdsIn(r1); NI.TopLookIdsIn(r2);
    assert LTB.LookIds(r1) * LTB.LookIds(r2) == {};
    if l in LTB.LookIds(r1) { assert l !in LTB.LookIds(r2) by { if l in LTB.LookIds(r2) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } } }
  }

  /** What one replay level says about the record of lid `l`: `on` = on the first empty path. */
  ghost predicate LookRec(r: R.regex, rg0: Regs3, rg2: Regs3, cp: int, K: int, l: nat, on: bool)
    requires l in LTB.LookIds(r)
  {
    if on then
      AI.get_idx(rg2.1.a_cp, l) == cp && AI.get_idx(rg2.1.a_clk, l) > K
      && NI.LookPathPresent(r, rg2.0.a_clk, rg2.2.a_clk, K, l)
      && AI.get_idx(rg2.1.a_clk, l) >= NI.MxAtLidLk(r, rg2.2.a_clk, K, l)
    else
      (AI.get_idx(rg2.1.a_cp, l) == AI.get_idx(rg0.1.a_cp, l) && AI.get_idx(rg2.1.a_clk, l) == AI.get_idx(rg0.1.a_clk, l))
      || !NI.LookPathPresent(r, rg2.0.a_clk, rg2.2.a_clk, K, l)
  }

  /** The registers after the path's writes and the children's replay. */
  ghost function RG2(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg0: Regs3, clks: seq<int>,
                     plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView): Regs3
    requires cp <= |str| && NRC.NulledWrites(qm, r, T.InputAt(str, cp)).Some?
    requires |clks| == |NRC.NulledWrites(qm, r, T.InputAt(str, cp)).value|
  {
    NRR.FC(r, cdnt, cp as int, NRC.ApplyWrites(NRC.NulledWrites(qm, r, T.InputAt(str, cp)).value, cp as int, clks, rg0), plus_bcv, str, ov)
  }

  /** A lid whose record `FNulledChildren` may touch sits under a quantifier of `r`; the outermost such
      quantifier is not itself replayed-into, so a stale clock there hides the lid. */
  lemma HiddenLook(r: R.regex, cc: seq<int>, qc: seq<int>, K: int, l: nat)
    requires l in LTB.LookIds(r) && PIV.QuantUnique(r) && LTB.LookUnique(r)
    requires forall q: nat :: q in PIV.QuantIds(r) && (q as int) !in NRR.InnerQuantRegs(r) ==> AI.get_idx(qc, q) < K
    ensures (l as int) !in NRR.InnerLookRegs(r) || !NI.LookPathPresent(r, cc, qc, K, l)
    decreases r, 1
  {
    match r
    case Re_alt(r1, r2) => HiddenLook2(r, cc, qc, K, l);
    case Re_con(r1, r2) => HiddenLook2(r, cc, qc, K, l);
    case Re_quant(_, qid, _, r1) =>
      NRR.QuantRegsOfOwn(r);
      assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
      assert AI.get_idx(qc, qid) < K;
    case Re_capture(_, r1) => HiddenLook(r1, cc, qc, K, l);
    case _ =>
  }

  lemma HiddenLook2(r: R.regex, cc: seq<int>, qc: seq<int>, K: int, l: nat)
    requires r.Re_alt? || r.Re_con?
    requires l in LTB.LookIds(r) && PIV.QuantUnique(r) && LTB.LookUnique(r)
    requires forall q: nat :: q in PIV.QuantIds(r) && (q as int) !in NRR.InnerQuantRegs(r) ==> AI.get_idx(qc, q) < K
    ensures (l as int) !in NRR.InnerLookRegs(r) || !NI.LookPathPresent(r, cc, qc, K, l)
    decreases r, 0
  {
    var r1 := NRR.L1(r); var r2 := NRR.L2(r);
    LookSidesDisjoint(r, l);
    NRR.InnerSub(r1); NRR.InnerSub(r2);
    NRR.QuantRegsOfChar(r1); NRR.QuantRegsOfChar(r2);
    assert PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
    assert NRR.InnerQuantRegs(r) == NRR.InnerQuantRegs(r1) + NRR.InnerQuantRegs(r2);
    assert NRR.InnerLookRegs(r) == NRR.InnerLookRegs(r1) + NRR.InnerLookRegs(r2);
    if l in LTB.LookIds(r1) {
      forall q: nat | q in PIV.QuantIds(r1) && (q as int) !in NRR.InnerQuantRegs(r1) ensures AI.get_idx(qc, q) < K {
        if (q as int) in NRR.InnerQuantRegs(r2) { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
      }
      HiddenLook(r1, cc, qc, K, l);
    } else {
      forall q: nat | q in PIV.QuantIds(r2) && (q as int) !in NRR.InnerQuantRegs(r2) ensures AI.get_idx(qc, q) < K {
        if (q as int) in NRR.InnerQuantRegs(r1) { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
      }
      HiddenLook(r2, cc, qc, K, l);
    }
  }

  /** The look twin of `NRR.FilterHiddenAfterChildren`: over a subtree whose quantifier clocks are all
      below `K`, `FNulledChildren` (which may replay stale stamps here, F2) either leaves a lid's record
      alone or writes it under a quantifier that is still stale — the lid is not present at `K`. */
  lemma FCHiddenLooks(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg: Regs3, K: int,
                      plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, l: nat)
    requires PIV.QuantUnique(r) && LTB.LookUnique(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && cp <= |str|
    requires NRC.CdnBitsOk(qm, r, T.InputAt(str, cp), cdnt)
    requires NRR.RegsStale(r, rg, K) && l in LTB.LookIds(r)
    ensures LookRec(r, rg, NRR.FC(r, cdnt, cp as int, rg, plus_bcv, str, ov), cp as int, K, l, false)
  {
    var rg2 := NRR.FC(r, cdnt, cp as int, rg, plus_bcv, str, ov);
    NRR.FNulledChildrenFrame(qm, r, cdnt, cp, rg, plus_bcv, str, ov);
    HiddenLook(r, rg2.0.a_clk, rg2.2.a_clk, K, l);
  }

  /** The look-path facts of a lid on one side of an alt/con move across a change confined to the other side. */
  lemma LookRecSide(r: R.regex, a: Regs3, b: Regs3, K: int, l: nat, first: bool)
    requires (r.Re_alt? || r.Re_con?) && PIV.CapUnique(r) && PIV.QuantUnique(r) && LTB.LookUnique(r)
    requires l in LTB.LookIds(r) && (first <==> l in LTB.LookIds(NRR.L1(r)))
    requires var o := if first then NRR.L2(r) else NRR.L1(r);
             NRR.AgreeOutside(b, a, NRR.InnerCapRegs(o), NRR.InnerLookRegs(o), NRR.InnerQuantRegs(o))
             || NRR.AgreeOutside(b, a, NRR.CapRegsOf(o), NRR.LookRegsOf(o), NRR.QuantRegsOf(o))
    ensures var s := if first then NRR.L1(r) else NRR.L2(r);
            l in LTB.LookIds(s)
            && NI.LookPathPresent(r, b.0.a_clk, b.2.a_clk, K, l) == NI.LookPathPresent(s, a.0.a_clk, a.2.a_clk, K, l)
            && NI.MxAtLidLk(r, b.2.a_clk, K, l) == NI.MxAtLidLk(s, a.2.a_clk, K, l)
            && AI.get_idx(b.1.a_cp, l) == AI.get_idx(a.1.a_cp, l) && AI.get_idx(b.1.a_clk, l) == AI.get_idx(a.1.a_clk, l)
  {
    var s := if first then NRR.L1(r) else NRR.L2(r);
    var o := if first then NRR.L2(r) else NRR.L1(r);
    LookSidesDisjoint(r, l);
    NRR.DisjointRegs(r);
    NRR.InnerSub(o);
    CLP.AncSub(s, l);
    CLP.LookPathFrame(s, a.0.a_clk, a.2.a_clk, b.0.a_clk, b.2.a_clk, K, l);
  }

  /** L3, one replay level, per lid: in `NRR.EngineReadout`'s frame, an on-path lid gets the record
      `(cp, clk > K)`, is present at `K` and dominates its threshold; an off-path lid keeps its record or
      is not present. */
  lemma EngineLookReadout(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg0: Regs3, K: int, clks: seq<int>,
                          plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, l: nat)
    requires NRR.ReadoutCtx(qm, r, plus_bcv, ov, str, cp) && LTB.LookUnique(r)
    requires NRC.CdnBitsOk(qm, r, T.InputAt(str, cp), cdnt)
    requires NRR.RegsCtx(r, rg0, K)
    requires NRC.NulledWrites(qm, r, T.InputAt(str, cp)).Some?
    requires var ws := NRC.NulledWrites(qm, r, T.InputAt(str, cp)).value;
             |clks| == |ws| && NRC.Incr(clks) && (forall i :: 0 <= i < |clks| ==> clks[i] > K) && K >= -1
    requires l in NI.TopLookIds(r) && l in LTB.LookIds(r)
    ensures LookRec(r, rg0, RG2(qm, r, cdnt, cp, rg0, clks, plus_bcv, str, ov), cp as int, K, l,
                    l in PathLooksR(qm, r, T.InputAt(str, cp)))
    decreases r, 1
  {
    match r {
      case Re_empty =>
      case Re_character(_) =>
      case Re_anchor(_) =>
      case Re_lookaround(_, _, _) =>
        EngineLookReadoutLook(qm, r, cdnt, cp, rg0, K, clks, plus_bcv, str, ov, l);
      case Re_capture(_, _) =>
        EngineLookReadoutCapture(qm, r, cdnt, cp, rg0, K, clks, plus_bcv, str, ov, l);
      case Re_quant(nul, _, q, _) =>
        if q.min == 0 {
          EngineLookReadoutSkip(qm, r, cdnt, cp, rg0, K, clks, plus_bcv, str, ov, l);
        } else if q.max == None && q.greedy {
          EngineLookReadoutStamp(qm, r, cdnt, cp, rg0, K, clks, plus_bcv, str, ov, l);
        } else {
          EngineLookReadoutForced(qm, r, cdnt, cp, rg0, K, clks, plus_bcv, str, ov, l);
        }
      case Re_alt(_, _) =>
        EngineLookReadoutAlt(qm, r, cdnt, cp, rg0, K, clks, plus_bcv, str, ov, l);
      case Re_con(_, _) =>
        EngineLookReadoutCon(qm, r, cdnt, cp, rg0, K, clks, plus_bcv, str, ov, l);
    }
  }

  // ---- the lookaround node itself ----
  lemma EngineLookReadoutLook(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg0: Regs3, K: int, clks: seq<int>,
                              plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, l: nat)
    requires r.Re_lookaround?
    requires NRR.ReadoutCtx(qm, r, plus_bcv, ov, str, cp) && LTB.LookUnique(r)
    requires NRR.RegsCtx(r, rg0, K)
    requires NRC.NulledWrites(qm, r, T.InputAt(str, cp)).Some?
    requires var ws := NRC.NulledWrites(qm, r, T.InputAt(str, cp)).value;
             |clks| == |ws| && NRC.Incr(clks) && (forall i :: 0 <= i < |clks| ==> clks[i] > K) && K >= -1
    requires l in NI.TopLookIds(r) && l in LTB.LookIds(r)
    ensures LookRec(r, rg0, RG2(qm, r, cdnt, cp, rg0, clks, plus_bcv, str, ov), cp as int, K, l,
                    l in PathLooksR(qm, r, T.InputAt(str, cp)))
  {
    var lid := r.lid; var la := r.look;
    var inp := T.InputAt(str, cp);
    var ws := NRC.NulledWrites(qm, r, inp).value;
    var cpi := cp as int;
    var rg1 := NRC.ApplyWrites(ws, cpi, clks, rg0);
    var rg2 := NRR.FC(r, cdnt, cpi, rg1, plus_bcv, str, ov);
    assert rg2 == rg1;
    assert lid >= 0 && l == lid as nat;
    if NRC.PositiveLk(la) {
      assert ws == [NRC.WLook(lid)];
      var k := clks[0];
      assert clks == [k];
      NRR.ApplyWritesSingle(NRC.WLook(lid), cpi, k, rg0);
      LookIdsTie(r);
      assert l in NRR.LookIds(r);
      assert lid < |rg0.1.a_cp| && |rg0.1.a_cp| == |rg0.1.a_clk|;
      assert rg1.1 == AReg.set_reg(rg0.1, lid, Some(cpi), k);
      assert AI.get_idx(rg1.1.a_cp, l) == cpi && AI.get_idx(rg1.1.a_clk, l) == k;
      assert l in PathLooksR(qm, r, inp);
    } else {
      assert ws == [];
      assert rg1 == rg0;
      assert l !in PathLooksR(qm, r, inp);
    }
  }

  // ---- the capture arm ----
  lemma EngineLookReadoutCapture(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg0: Regs3, K: int, clks: seq<int>,
                                 plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, l: nat)
    requires r.Re_capture?
    requires NRR.ReadoutCtx(qm, r, plus_bcv, ov, str, cp) && LTB.LookUnique(r)
    requires NRC.CdnBitsOk(qm, r, T.InputAt(str, cp), cdnt)
    requires NRR.RegsCtx(r, rg0, K)
    requires NRC.NulledWrites(qm, r, T.InputAt(str, cp)).Some?
    requires var ws := NRC.NulledWrites(qm, r, T.InputAt(str, cp)).value;
             |clks| == |ws| && NRC.Incr(clks) && (forall i :: 0 <= i < |clks| ==> clks[i] > K) && K >= -1
    requires l in NI.TopLookIds(r) && l in LTB.LookIds(r)
    ensures LookRec(r, rg0, RG2(qm, r, cdnt, cp, rg0, clks, plus_bcv, str, ov), cp as int, K, l,
                    l in PathLooksR(qm, r, T.InputAt(str, cp)))
    decreases r, 0
  {
    NRR.CdnBitsOkSub(qm, r, T.InputAt(str, cp), cdnt);
    var cid := r.cid; var r1 := NRR.L1(r);
    var inp := T.InputAt(str, cp);
    var ws := NRC.NulledWrites(qm, r, inp).value;
    var w1 := NRC.NulledWrites(qm, r1, inp).value;
    var sr := CP.start_reg(cid); var er := CP.end_reg(cid);
    assert ws == [NRC.WCap(sr)] + w1 + [NRC.WCap(er)];
    var n1 := |w1|;
    assert |clks| == n1 + 2;
    var ks := clks[0]; var ke := clks[n1 + 1]; var clks1 := clks[1..n1 + 1];
    assert clks == [ks] + clks1 + [ke];
    var cpi := cp as int;
    var rgS := NRC.ApplyWrite(NRC.WCap(sr), cpi, ks, rg0);
    var rgSE := NRC.ApplyWrite(NRC.WCap(er), cpi, ke, rgS);
    var rg1 := NRC.ApplyWrites(ws, cpi, clks, rg0);
    NRR.ApplyWritesSplit3(w1, sr, er, cpi, ks, clks1, ke, rg0);
    assert rg1 == NRC.ApplyWrite(NRC.WCap(er), cpi, ke, NRC.ApplyWrites(w1, cpi, clks1, rgS));
    NRR.NulledWritesTargets(qm, r1, inp);
    NRR.CapRegsOfOwn(r);
    assert er !in NRR.CapTargets(w1) && sr !in NRR.CapTargets(w1);
    NRR.ApplyWritesOutsideCommute(w1, cpi, clks1, rgS, er, ke);
    assert rg1 == NRC.ApplyWrites(w1, cpi, clks1, rgSE);
    assert {:split_here} true;
    NRR.PlusTableOkSChildren(r, plus_bcv);
    NRR.CapUniqueChildT(r);
    assert NRR.RegsCtx(r1, rgSE, K) by {
      assert NRR.Sized3(rgSE, rg0) && NRR.WfRegs(rgSE) && NRR.CapValWf(rgSE) by {
        assert ks >= 0 && ke >= 0 && cpi >= 0;
        NRR.ApplyWritesSingle(NRC.WCap(sr), cpi, ks, rg0);
        NRR.ApplyWritesSingle(NRC.WCap(er), cpi, ke, rgS);
        NRR.ApplyWritesFrame([NRC.WCap(sr)], cpi, [ks], rg0);
        NRR.ApplyWritesCapValWf([NRC.WCap(sr)], cpi, [ks], rg0);
        NRR.ApplyWritesFrame([NRC.WCap(er)], cpi, [ke], rgS);
        NRR.ApplyWritesCapValWf([NRC.WCap(er)], cpi, [ke], rgS);
      }
      NRR.RegsCtxCaptureInner(r, rg0, rgS, rgSE, K, ks, ke);
    }
    assert NRC.Incr(clks1) && forall i :: 0 <= i < |clks1| ==> clks1[i] > K by {
      forall i, j | 0 <= i < j < |clks1| ensures clks1[i] < clks1[j] { assert clks1[i] == clks[i + 1] && clks1[j] == clks[j + 1]; }
      forall i | 0 <= i < |clks1| ensures clks1[i] > K { assert clks1[i] == clks[i + 1]; }
    }
    assert {:split_here} true;
    NRR.EngineReadout(qm, r1, cdnt, cp, rgSE, K, clks1, plus_bcv, str, ov);
    EngineLookReadout(qm, r1, cdnt, cp, rgSE, K, clks1, plus_bcv, str, ov, l);
    var rg2 := NRR.FC(r, cdnt, cpi, rg1, plus_bcv, str, ov);
    assert rg2 == NRR.FC(r1, cdnt, cpi, rg1, plus_bcv, str, ov);
    assert rg2 == RG2(qm, r1, cdnt, cp, rgSE, clks1, plus_bcv, str, ov);
    assert AI.get_idx(rg2.0.a_clk, sr) == ks by {
      assert sr !in NRR.CapRegsOf(r1);
      assert sr < |rg0.0.a_cp| && er < |rg0.0.a_cp| by { assert (cid as nat) in PIV.CapIds(r); }
      assert AI.get_idx(rgSE.0.a_clk, sr) == ks;
    }
    assert ks > K && ks >= 0;
    assert rgSE.1 == rg0.1;
    assert (l in PathLooksR(qm, r, inp)) == (l in PathLooksR(qm, r1, inp));
  }

  // ---- the quantifier arms ----
  lemma EngineLookReadoutSkip(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg0: Regs3, K: int, clks: seq<int>,
                              plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, l: nat)
    requires r.Re_quant? && r.quant.min == 0
    requires NRR.ReadoutCtx(qm, r, plus_bcv, ov, str, cp) && LTB.LookUnique(r)
    requires NRC.CdnBitsOk(qm, r, T.InputAt(str, cp), cdnt)
    requires NRR.RegsCtx(r, rg0, K)
    requires NRC.NulledWrites(qm, r, T.InputAt(str, cp)).Some?
    requires var ws := NRC.NulledWrites(qm, r, T.InputAt(str, cp)).value;
             |clks| == |ws| && NRC.Incr(clks) && (forall i :: 0 <= i < |clks| ==> clks[i] > K) && K >= -1
    requires l in NI.TopLookIds(r) && l in LTB.LookIds(r)
    ensures LookRec(r, rg0, RG2(qm, r, cdnt, cp, rg0, clks, plus_bcv, str, ov), cp as int, K, l,
                    l in PathLooksR(qm, r, T.InputAt(str, cp)))
  {
    var qid := r.qid;
    var inp := T.InputAt(str, cp);
    var ws := NRC.NulledWrites(qm, r, inp).value;
    var cpi := cp as int;
    var rg1 := NRC.ApplyWrites(ws, cpi, clks, rg0);
    var rg2 := NRR.FC(r, cdnt, cpi, rg1, plus_bcv, str, ov);
    assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
    NRR.QuantRegsOfOwn(r);
    assert ws == [];
    assert rg1 == rg0;
    NRR.FNulledChildrenFrame(qm, r, cdnt, cp, rg1, plus_bcv, str, ov);
    assert AI.get_idx(rg2.2.a_clk, qid) == AI.get_idx(rg0.2.a_clk, qid) < K;
    assert l !in PathLooksR(qm, r, inp);
    assert !NI.LookPathPresent(r, rg2.0.a_clk, rg2.2.a_clk, K, l);
  }

  /** A nested stamp plus (CIN or CDN) on the path: re-stamped at `k`, its body replayed from `k`. */
  lemma EngineLookReadoutStamp(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg0: Regs3, K: int, clks: seq<int>,
                               plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, l: nat)
    requires r.Re_quant? && r.quant.min != 0 && r.quant.max == None && r.quant.greedy
    requires NRR.ReadoutCtx(qm, r, plus_bcv, ov, str, cp) && LTB.LookUnique(r)
    requires NRC.CdnBitsOk(qm, r, T.InputAt(str, cp), cdnt)
    requires NRR.RegsCtx(r, rg0, K)
    requires NRC.NulledWrites(qm, r, T.InputAt(str, cp)).Some?
    requires var ws := NRC.NulledWrites(qm, r, T.InputAt(str, cp)).value;
             |clks| == |ws| && NRC.Incr(clks) && (forall i :: 0 <= i < |clks| ==> clks[i] > K) && K >= -1
    requires l in NI.TopLookIds(r) && l in LTB.LookIds(r)
    ensures LookRec(r, rg0, RG2(qm, r, cdnt, cp, rg0, clks, plus_bcv, str, ov), cp as int, K, l,
                    l in PathLooksR(qm, r, T.InputAt(str, cp)))
    decreases r, 0
  {
    NRR.CdnBitsOkSub(qm, r, T.InputAt(str, cp), cdnt);
    var nul := r.qnul; var qid := r.qid; var q := r.quant; var r1 := NRR.L1(r);
    var inp := T.InputAt(str, cp);
    var ws := NRC.NulledWrites(qm, r, inp).value;
    var cpi := cp as int;
    var rg1 := NRC.ApplyWrites(ws, cpi, clks, rg0);
    var rg2 := NRR.FC(r, cdnt, cpi, rg1, plus_bcv, str, ov);
    assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
    NRR.PlusTableOkSChildren(r, plus_bcv);
    NRR.CapUniqueChildT(r);
    NRR.QuantRegsOfOwn(r);
    NRR.InnerSub(r1);
    assert nul != R.NonNullable;
    assert NRC.NulledWrites(qm, r1, inp).Some? && ws == [NRC.WQuant(qid, true)] by {
      if nul == R.CINullable {
        NUL.TransCINullable(r1);
        NRR.CINullablePath(qm, r1, inp);
        NRR.NulledWritesIffPath(qm, r1, inp);
      }
    }
    var k := clks[0];
    assert |clks| == 1 && clks == [k];
    NRR.ApplyWritesSingle(NRC.WQuant(qid, true), cpi, k, rg0);
    assert rg1 == NRC.ApplyWrite(NRC.WQuant(qid, true), cpi, k, rg0);
    assert rg1.2 == AReg.set_reg(rg0.2, qid, Some(cpi), k) && rg1.0 == rg0.0 && rg1.1 == rg0.1;
    assert qid < |rg0.2.a_cp| && |rg0.2.a_cp| == |rg0.2.a_clk|;
    assert AReg.get_cp(rg1.2, qid) == Some(cpi) && AI.opt_int(AReg.get_clock(rg1.2, qid)) == k;
    assert {:split_here} true;
    var code := AI.get_code_v(plus_bcv, qid);
    assert NRR.QidStampPlus(r, qid as nat) && PIV.QidBody(r, qid as nat) == r1;
    assert code == CP.compile_reconstruct_nulled(r1);
    var (rgR, ovR) := NRR.ReconAt(code, r1, cdnt, cpi, rg1, k, plus_bcv, str, ov);
    assert rg2 == rgR;
    var ctx := AI.cp_context(cpi, str, RA.Forward);
    var inits := AI.FInitState(code, cpi, rg1.0, rg1.1, rg1.2, k, ctx).(cdn := cdnt);
    var (result, sF, ov1) := AI.FNullInterp(code, inits, ov, RA.Forward);
    NRR.CpOfInputAt(str, cp);
    assert inits == AI.FInitState(code, TR.CpOf(inp) as int, rg1.0, rg1.1, rg1.2, k, TR.CtxOf(inp)).(cdn := inits.cdn);
    NRC.NullInterpNulledT(qm, r1, inp, inits, ov, rg1.0, rg1.1, rg1.2, k);
    NRR.NulledWritesIffPath(qm, r1, inp);
    assert result.Some? && ov1 == ov;
    var w1 := NRC.NulledWrites(qm, r1, inp).value;
    assert NRC.RegsFrom(NRC.RegsOf(result.value), w1, cpi, rg1, k, sF.clock);
    var clks1: seq<int> :| |clks1| == |w1| && NRC.Incr(clks1) && NRC.ClksIn(clks1, k, sF.clock)
                            && NRC.RegsOf(result.value) == NRC.ApplyWrites(w1, cpi, clks1, rg1);
    var rgW := NRC.ApplyWrites(w1, cpi, clks1, rg1);
    assert rg2 == NRR.FC(r1, cdnt, cpi, rgW, plus_bcv, str, ov);
    assert {:split_here} true;
    assert NRR.RegsCtx(r1, rg1, k) by { NRR.RegsCtxQuantInner(r, rg0, rg1, K, k); }
    assert forall i :: 0 <= i < |clks1| ==> clks1[i] > k;
    NRR.EngineReadout(qm, r1, cdnt, cp, rg1, k, clks1, plus_bcv, str, ov);
    EngineLookReadout(qm, r1, cdnt, cp, rg1, k, clks1, plus_bcv, str, ov, l);
    assert rg2 == RG2(qm, r1, cdnt, cp, rg1, clks1, plus_bcv, str, ov);
    assert AI.get_idx(rg2.2.a_clk, qid) == k by {
      assert qid !in NRR.QuantRegsOf(r1);
      assert AI.get_idx(rg1.2.a_clk, qid) == k;
    }
    assert k > K;
    assert (l in PathLooksR(qm, r, inp)) == (l in PathLooksR(qm, r1, inp));
  }

  /** A generic forced quantifier on the path: one clock mark at `k`, then the body's writes above `k`. */
  lemma EngineLookReadoutForced(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg0: Regs3, K: int, clks: seq<int>,
                                plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, l: nat)
    requires r.Re_quant? && r.quant.min != 0 && !(r.quant.max == None && r.quant.greedy)
    requires NRR.ReadoutCtx(qm, r, plus_bcv, ov, str, cp) && LTB.LookUnique(r)
    requires NRC.CdnBitsOk(qm, r, T.InputAt(str, cp), cdnt)
    requires NRR.RegsCtx(r, rg0, K)
    requires NRC.NulledWrites(qm, r, T.InputAt(str, cp)).Some?
    requires var ws := NRC.NulledWrites(qm, r, T.InputAt(str, cp)).value;
             |clks| == |ws| && NRC.Incr(clks) && (forall i :: 0 <= i < |clks| ==> clks[i] > K) && K >= -1
    requires l in NI.TopLookIds(r) && l in LTB.LookIds(r)
    ensures LookRec(r, rg0, RG2(qm, r, cdnt, cp, rg0, clks, plus_bcv, str, ov), cp as int, K, l,
                    l in PathLooksR(qm, r, T.InputAt(str, cp)))
    decreases r, 0
  {
    NRR.CdnBitsOkSub(qm, r, T.InputAt(str, cp), cdnt);
    var nul := r.qnul; var qid := r.qid; var q := r.quant; var r1 := NRR.L1(r);
    var inp := T.InputAt(str, cp);
    var ws := NRC.NulledWrites(qm, r, inp).value;
    var cpi := cp as int;
    var rg1 := NRC.ApplyWrites(ws, cpi, clks, rg0);
    var rg2 := NRR.FC(r, cdnt, cpi, rg1, plus_bcv, str, ov);
    assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
    NRR.PlusTableOkSChildren(r, plus_bcv);
    NRR.CapUniqueChildT(r);
    NRR.QuantRegsOfOwn(r);
    NRR.InnerSub(r1);
    assert nul != R.NonNullable;
    var w1 := NRC.NulledWrites(qm, r1, inp).value;
    assert ws == [NRC.WQuant(qid, false)] + w1;
    var k := clks[0];
    var clks1 := clks[1..];
    assert ws[0] == NRC.WQuant(qid, false) && ws[1..] == w1 && clks[0] == k && clks[1..] == clks1;
    var rgM := NRC.ApplyWrite(NRC.WQuant(qid, false), cpi, k, rg0);
    assert rg1 == NRC.ApplyWrites(w1, cpi, clks1, rgM);
    assert AReg.get_cp(rgM.2, qid) == None;
    NRR.NulledWritesTargets(qm, r1, inp);
    assert qid !in NRR.QuantTargets(w1) by { NRR.QuantRegsOfChar(r1); }
    NRR.ApplyWritesFrame(w1, cpi, clks1, rgM);
    assert AReg.get_cp(rg1.2, qid) == None by {
      assert AI.get_idx(rg1.2.a_cp, qid) == AI.get_idx(rgM.2.a_cp, qid) == -1;
    }
    assert rg2 == NRR.FC(r1, cdnt, cpi, rg1, plus_bcv, str, ov);
    assert {:split_here} true;
    assert NRR.RegsCtx(r1, rgM, k) by { NRR.RegsCtxQuantInner(r, rg0, rgM, K, k); }
    assert NRC.Incr(clks1) && forall i :: 0 <= i < |clks1| ==> clks1[i] > k by {
      forall i, j | 0 <= i < j < |clks1| ensures clks1[i] < clks1[j] { assert clks1[i] == clks[i + 1] && clks1[j] == clks[j + 1]; }
      forall i | 0 <= i < |clks1| ensures clks1[i] > k { assert clks1[i] == clks[i + 1] && clks[0] < clks[i + 1]; }
    }
    NRR.EngineReadout(qm, r1, cdnt, cp, rgM, k, clks1, plus_bcv, str, ov);
    EngineLookReadout(qm, r1, cdnt, cp, rgM, k, clks1, plus_bcv, str, ov, l);
    assert rg2 == RG2(qm, r1, cdnt, cp, rgM, clks1, plus_bcv, str, ov);
    assert AI.get_idx(rg2.2.a_clk, qid) == k by {
      assert qid !in NRR.QuantRegsOf(r1);
      assert AI.get_idx(rgM.2.a_clk, qid) == k;
      assert AI.get_idx(rg1.2.a_clk, qid) == k;
    }
    assert k > K;
    assert rgM.1 == rg0.1;
    assert (l in PathLooksR(qm, r, inp)) == (l in PathLooksR(qm, r1, inp));
  }

  // ---- the alternation arm ----
  lemma EngineLookReadoutAlt(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg0: Regs3, K: int, clks: seq<int>,
                             plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, l: nat)
    requires r.Re_alt?
    requires NRR.ReadoutCtx(qm, r, plus_bcv, ov, str, cp) && LTB.LookUnique(r)
    requires NRC.CdnBitsOk(qm, r, T.InputAt(str, cp), cdnt)
    requires NRR.RegsCtx(r, rg0, K)
    requires NRC.NulledWrites(qm, r, T.InputAt(str, cp)).Some?
    requires var ws := NRC.NulledWrites(qm, r, T.InputAt(str, cp)).value;
             |clks| == |ws| && NRC.Incr(clks) && (forall i :: 0 <= i < |clks| ==> clks[i] > K) && K >= -1
    requires l in NI.TopLookIds(r) && l in LTB.LookIds(r)
    ensures LookRec(r, rg0, RG2(qm, r, cdnt, cp, rg0, clks, plus_bcv, str, ov), cp as int, K, l,
                    l in PathLooksR(qm, r, T.InputAt(str, cp)))
    decreases r, 0
  {
    NRR.CdnBitsOkSub(qm, r, T.InputAt(str, cp), cdnt);
    var r1 := NRR.L1(r); var r2 := NRR.L2(r);
    var inp := T.InputAt(str, cp);
    var ws := NRC.NulledWrites(qm, r, inp).value;
    var cpi := cp as int;
    var rg1 := NRC.ApplyWrites(ws, cpi, clks, rg0);
    NRR.ApplyWritesFrame(ws, cpi, clks, rg0);
    NRR.ApplyWritesCapValWf(ws, cpi, clks, rg0);
    NRR.PlusTableOkSChildren(r, plus_bcv);
    NRR.CapUniqueChildT(r);
    NRR.DisjointRegs(r);
    NRR.RegsStaleSplit(r, rg0, K);
    NRR.CoversChild(r, rg0);
    NRR.InnerSub(r1); NRR.InnerSub(r2);
    NRR.FNulledChildrenFrame(qm, r1, cdnt, cp, rg1, plus_bcv, str, ov);
    var rgA := NRR.FC(r1, cdnt, cpi, rg1, plus_bcv, str, ov);
    var rg2 := NRR.FC(r, cdnt, cpi, rg1, plus_bcv, str, ov);
    assert rg2 == NRR.FC(r2, cdnt, cpi, rgA, plus_bcv, str, ov);
    NRR.NulledWritesIffPath(qm, r1, inp);
    NRR.NulledWritesIffPath(qm, r2, inp);
    LookSidesDisjoint(r, l);
    PathLooksInTop(qm, r1, inp); PathLooksInTop(qm, r2, inp);
    NRR.FNulledChildrenFrame(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
    var inL1 := l in LTB.LookIds(r1);
    if NRC.NulledWrites(qm, r1, inp).Some? {
      assert {:split_here} true;
      assert ws == NRC.NulledWrites(qm, r1, inp).value;
      assert PathLooksR(qm, r, inp) == PathLooksR(qm, r1, inp);
      NRR.EngineReadout(qm, r1, cdnt, cp, rg0, K, clks, plus_bcv, str, ov);
      NRR.NulledWritesTargets(qm, r1, inp);
      if inL1 {
        EngineLookReadout(qm, r1, cdnt, cp, rg0, K, clks, plus_bcv, str, ov, l);
        assert rgA == RG2(qm, r1, cdnt, cp, rg0, clks, plus_bcv, str, ov);
        LookRecSide(r, rgA, rg2, K, l, true);
      } else {
        assert NRR.RegsCtx(r2, rgA, K) by {
          NRR.AgreeOutsideWeaken(rg1, rg0, NRR.CapTargets(ws), NRR.LookTargets(ws), NRR.QuantTargets(ws), NRR.CapRegsOf(r1), NRR.LookRegsOf(r1), NRR.QuantRegsOf(r1));
          NRR.AgreeOutsideWeaken(rgA, rg1, NRR.InnerCapRegs(r1), NRR.InnerLookRegs(r1), NRR.InnerQuantRegs(r1), NRR.CapRegsOf(r1), NRR.LookRegsOf(r1), NRR.QuantRegsOf(r1));
          NRR.AgreeOutsideTrans(rgA, rg1, rg0, NRR.CapRegsOf(r1), NRR.LookRegsOf(r1), NRR.QuantRegsOf(r1));
          NRR.SubAgree2(r, rg0, rgA);
          NRR.StaleFrame(r2, rg0, rgA, K);
          NRR.CoversSized(r2, rg0, rgA);
        }
        FCHiddenLooks(qm, r2, cdnt, cp, rgA, K, plus_bcv, str, ov, l);
        assert NRR.AgreeOutside(rgA, rg0, NRR.CapRegsOf(r1), NRR.LookRegsOf(r1), NRR.QuantRegsOf(r1));
        assert AI.get_idx(rgA.1.a_cp, l) == AI.get_idx(rg0.1.a_cp, l) && AI.get_idx(rgA.1.a_clk, l) == AI.get_idx(rg0.1.a_clk, l);
        assert l !in PathLooksR(qm, r, inp);
      }
    } else {
      assert {:split_here} true;
      assert ws == NRC.NulledWrites(qm, r2, inp).value;
      assert PathLooksR(qm, r, inp) == PathLooksR(qm, r2, inp);
      NRR.NulledWritesTargets(qm, r2, inp);
      assert NRR.RegsCtx(r1, rg1, K) by {
        NRR.AgreeOutsideWeaken(rg1, rg0, NRR.CapTargets(ws), NRR.LookTargets(ws), NRR.QuantTargets(ws), NRR.CapRegsOf(r2), NRR.LookRegsOf(r2), NRR.QuantRegsOf(r2));
        NRR.StaleFrame(r1, rg0, rg1, K);
        NRR.CoversSized(r1, rg0, rg1);
        NRR.ApplyWritesCapValWf(ws, cpi, clks, rg0);
      }
      if inL1 {
        FCHiddenLooks(qm, r1, cdnt, cp, rg1, K, plus_bcv, str, ov, l);
        LookRecSide(r, rgA, rg2, K, l, true);
        assert (l as int) !in NRR.LookTargets(ws);
        assert AI.get_idx(rg1.1.a_cp, l) == AI.get_idx(rg0.1.a_cp, l) && AI.get_idx(rg1.1.a_clk, l) == AI.get_idx(rg0.1.a_clk, l);
        assert l !in PathLooksR(qm, r, inp);
      } else {
        assert {:split_here} true;
        var rgB := NRR.MergeOn(rgA, rg0, NRR.CapTargets(ws), NRR.LookTargets(ws), NRR.QuantTargets(ws));
        assert forall k: int :: k in NRR.QuantTargets(ws) ==>
                 AI.get_idx(rgA.2.a_cp, k) == AI.get_idx(rg1.2.a_cp, k) && AI.get_idx(rgA.2.a_clk, k) == AI.get_idx(rg1.2.a_clk, k) by {
          forall k: int | k in NRR.QuantTargets(ws)
            ensures AI.get_idx(rgA.2.a_cp, k) == AI.get_idx(rg1.2.a_cp, k) && AI.get_idx(rgA.2.a_clk, k) == AI.get_idx(rg1.2.a_clk, k)
          {
            assert k in NRR.QuantRegsOf(r2);
            assert k !in NRR.QuantRegsOf(r1) by { assert NRR.QuantRegsOf(r1) * NRR.QuantRegsOf(r2) == {}; }
            assert k !in NRR.InnerQuantRegs(r1);
          }
        }
        assert NRC.ApplyWrites(ws, cpi, clks, rgB) == rgA by {
          NRR.TargetsInRangeFromCovers(qm, r2, inp, rg0);
          NRR.MergeOnApply(ws, cpi, clks, rg0, rgA, rgB, r1, r2);
        }
        assert NRR.RegsCtx(r2, rgB, K) by {
          NRR.SubAgree2(r, rg1, rgA);
          NRR.RegsCtxMerge(r, rg0, rg1, rgA, rgB, K, ws);
        }
        assert {:split_here} true;
        EngineLookReadout(qm, r2, cdnt, cp, rgB, K, clks, plus_bcv, str, ov, l);
        assert rg2 == RG2(qm, r2, cdnt, cp, rgB, clks, plus_bcv, str, ov);
        NRR.MergeOnFacts(rgA, rg0, NRR.CapTargets(ws), NRR.LookTargets(ws), NRR.QuantTargets(ws));
        assert (l as int) !in NRR.InnerLookRegs(r1);
        assert AI.get_idx(rgB.1.a_cp, l) == AI.get_idx(rg0.1.a_cp, l) && AI.get_idx(rgB.1.a_clk, l) == AI.get_idx(rg0.1.a_clk, l);
      }
    }
  }

  // ---- the concatenation arm ----
  lemma {:induction false} EngineLookReadoutCon(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg0: Regs3, K: int, clks: seq<int>,
                             plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, l: nat)
    requires r.Re_con?
    requires NRR.ReadoutCtx(qm, r, plus_bcv, ov, str, cp) && LTB.LookUnique(r)
    requires NRC.CdnBitsOk(qm, r, T.InputAt(str, cp), cdnt)
    requires NRR.RegsCtx(r, rg0, K)
    requires NRC.NulledWrites(qm, r, T.InputAt(str, cp)).Some?
    requires var ws := NRC.NulledWrites(qm, r, T.InputAt(str, cp)).value;
             |clks| == |ws| && NRC.Incr(clks) && (forall i :: 0 <= i < |clks| ==> clks[i] > K) && K >= -1
    requires l in NI.TopLookIds(r) && l in LTB.LookIds(r)
    ensures LookRec(r, rg0, RG2(qm, r, cdnt, cp, rg0, clks, plus_bcv, str, ov), cp as int, K, l,
                    l in PathLooksR(qm, r, T.InputAt(str, cp)))
    decreases r, 0
  {
    NRR.CdnBitsOkSub(qm, r, T.InputAt(str, cp), cdnt);
    var r1 := NRR.L1(r); var r2 := NRR.L2(r);
    var inp := T.InputAt(str, cp);
    NRR.NulledWritesConSplit(qm, r, inp);
    var ws := NRC.NulledWrites(qm, r, inp).value;
    var w1 := NRC.NulledWrites(qm, r1, inp).value;
    var w2 := NRC.NulledWrites(qm, r2, inp).value;
    assert ws == w1 + w2;
    assert {:split_here} true;
    var n1 := |w1|;
    var cl1 := clks[..n1]; var cl2 := clks[n1..];
    assert clks == cl1 + cl2;
    var cpi := cp as int;
    var rg1 := NRC.ApplyWrites(ws, cpi, clks, rg0);
    NRR.ApplyWritesApp(w1, w2, cpi, cl1, cl2, rg0);
    var rgX := NRC.ApplyWrites(w1, cpi, cl1, rg0);
    assert rg1 == NRC.ApplyWrites(w2, cpi, cl2, rgX);
    NRR.ApplyWritesFrame(ws, cpi, clks, rg0);
    NRR.ApplyWritesCapValWf(ws, cpi, clks, rg0);
    assert {:split_here} true;
    NRR.PlusTableOkSChildren(r, plus_bcv);
    NRR.CapUniqueChildT(r);
    NRR.DisjointRegs(r);
    NRR.RegsStaleSplit(r, rg0, K);
    NRR.CoversChild(r, rg0);
    NRR.InnerSub(r1); NRR.InnerSub(r2);
    NRR.NulledWritesTargets(qm, r1, inp);
    NRR.NulledWritesTargets(qm, r2, inp);
    NRR.TargetsApp(w1, w2);
    assert NRR.CapTargets(w1) * NRR.CapTargets(w2) == {} && NRR.LookTargets(w1) * NRR.LookTargets(w2) == {} && NRR.QuantTargets(w1) * NRR.QuantTargets(w2) == {} by {
      assert NRR.LookRegsOf(r1) * NRR.LookRegsOf(r2) == {};
    }
    assert {:split_here} true;
    NRR.FNulledChildrenFrame(qm, r1, cdnt, cp, rg1, plus_bcv, str, ov);
    var rgA := NRR.FC(r1, cdnt, cpi, rg1, plus_bcv, str, ov);
    var rg2 := NRR.FC(r, cdnt, cpi, rg1, plus_bcv, str, ov);
    assert {:split_here} true;
    NRR.FCConStep(r, cdnt, cpi, rg1, plus_bcv, str, ov);
    assert rg2 == NRR.FC(r2, cdnt, cpi, rgA, plus_bcv, str, ov);
    assert {:split_here} true;
    NRR.IncrSplit(clks, n1, K);
    assert {:split_here} true;
    var rg0a := NRC.ApplyWrites(w2, cpi, cl2, rg0);
    NRR.ApplyWritesFrame(w2, cpi, cl2, rg0);
    NRR.ApplyWritesFrame(w1, cpi, cl1, rg0);
    assert rg1 == NRC.ApplyWrites(w1, cpi, cl1, rg0a) by { NRR.ApplyWritesDisjointCommute(w1, w2, cpi, cl1, cl2, rg0); }
    assert NRR.RegsCtx(r1, rg0a, K) by {
      NRR.AgreeOutsideWeaken(rg0a, rg0, NRR.CapTargets(w2), NRR.LookTargets(w2), NRR.QuantTargets(w2), NRR.CapRegsOf(r2), NRR.LookRegsOf(r2), NRR.QuantRegsOf(r2));
      NRR.SubAgree(r, rg0, rg0a);
      NRR.StaleFrame(r1, rg0, rg0a, K);
      NRR.CoversSized(r1, rg0, rg0a);
      NRR.ApplyWritesCapValWf(w2, cpi, cl2, rg0);
    }
    assert {:split_here} true;
    LookSidesDisjoint(r, l);
    PathLooksInTop(qm, r1, inp); PathLooksInTop(qm, r2, inp);
    NRR.FNulledChildrenFrame(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
    if l in LTB.LookIds(r1) {
      EngineLookReadout(qm, r1, cdnt, cp, rg0a, K, cl1, plus_bcv, str, ov, l);
      assert rgA == RG2(qm, r1, cdnt, cp, rg0a, cl1, plus_bcv, str, ov);
      LookRecSide(r, rgA, rg2, K, l, true);
      assert (l in PathLooksR(qm, r, inp)) == (l in PathLooksR(qm, r1, inp));
      assert (l as int) !in NRR.LookTargets(w2);
      assert AI.get_idx(rg0a.1.a_cp, l) == AI.get_idx(rg0.1.a_cp, l) && AI.get_idx(rg0a.1.a_clk, l) == AI.get_idx(rg0.1.a_clk, l);
    } else {
      assert {:split_here} true;
      NRR.SubAgree2(r, rg1, rgA);
      var rgB := NRR.MergeOn(rgA, rg0, NRR.CapTargets(w2), NRR.LookTargets(w2), NRR.QuantTargets(w2));
      assert NRC.ApplyWrites(w2, cpi, cl2, rgB) == rgA by {
        NRR.TargetsInRangeFromCovers(qm, r2, inp, rg0);
        NRR.MergeOnApplyCon(w1, w2, cpi, cl1, cl2, rg0, rg1, rgA, rgB, r1, r2);
      }
      assert NRR.RegsCtx(r2, rgB, K) by {
        forall k: int | k in NRR.CapRegsOf(r2) && k !in NRR.CapTargets(w2) ensures AI.get_idx(rgA.0.a_cp, k) == AI.get_idx(rg0.0.a_cp, k) && AI.get_idx(rgA.0.a_clk, k) == AI.get_idx(rg0.0.a_clk, k) {
          assert k !in NRR.CapTargets(w1) by { if k in NRR.CapTargets(w1) { assert k in NRR.CapRegsOf(r1) * NRR.CapRegsOf(r2); } }
        }
        forall k: int | k in NRR.QuantRegsOf(r2) && k !in NRR.QuantTargets(w2) ensures AI.get_idx(rgA.2.a_clk, k) == AI.get_idx(rg0.2.a_clk, k) {
          assert k !in NRR.QuantTargets(w1) by { if k in NRR.QuantTargets(w1) { assert k in NRR.QuantRegsOf(r1) * NRR.QuantRegsOf(r2); } }
        }
        NRR.RegsCtxMergeCon(r, rg0, rg1, rgA, rgB, K, w1, w2);
      }
      assert {:split_here} true;
      EngineLookReadout(qm, r2, cdnt, cp, rgB, K, cl2, plus_bcv, str, ov, l);
      assert rg2 == RG2(qm, r2, cdnt, cp, rgB, cl2, plus_bcv, str, ov);
      assert (l in PathLooksR(qm, r, inp)) == (l in PathLooksR(qm, r2, inp));
      NRR.MergeOnFacts(rgA, rg0, NRR.CapTargets(w2), NRR.LookTargets(w2), NRR.QuantTargets(w2));
      assert (l as int) !in NRR.InnerLookRegs(r1) && (l as int) !in NRR.LookTargets(w1);
      assert AI.get_idx(rgB.1.a_cp, l) == AI.get_idx(rg0.1.a_cp, l) && AI.get_idx(rgB.1.a_clk, l) == AI.get_idx(rg0.1.a_clk, l);
    }
  }

  // ===========================================================================
  // 3. The look record at the `FNulledPlus` level, per machine-A-live stamp
  // ===========================================================================

  /** For every live stamp `q` of `best` (`PIV.QLive`) and every top lid `l` of its body: `rp`'s record of
      `l` is `EngineLookReadout`'s — written at the stamp's position above the stamp's clock, present and
      dominating inside the body if the body's first empty path crosses it; kept from `best` or not present
      otherwise. Opaque: passed as a term, read with `LookRecordAt`. */
  opaque ghost predicate LookRecordOk(qm: AR.QMap, re: R.regex, str: string, best: Regs3, rp: Regs3)
  {
    forall q: nat, l: nat ::
      PIV.QLive(re, best.2.a_clk, best.2.a_cp, q)
      && AI.get_idx(best.2.a_cp, q) <= |str| && T.TransWf(PIV.QidBody(re, q))
      && l in NI.TopLookIds(PIV.QidBody(re, q)) && l in LTB.LookIds(PIV.QidBody(re, q)) ==>
        LookRec(PIV.QidBody(re, q), best, rp, AI.get_idx(best.2.a_cp, q), AI.get_idx(best.2.a_clk, q), l,
                l in PathLooksR(qm, PIV.QidBody(re, q), T.InputAt(str, AI.get_idx(best.2.a_cp, q) as nat)))
  }

  lemma LookRecordAt(qm: AR.QMap, re: R.regex, str: string, best: Regs3, rp: Regs3, q: nat, l: nat)
    requires LookRecordOk(qm, re, str, best, rp)
    requires PIV.QLive(re, best.2.a_clk, best.2.a_cp, q)
    requires AI.get_idx(best.2.a_cp, q) <= |str| && T.TransWf(PIV.QidBody(re, q))
    requires l in NI.TopLookIds(PIV.QidBody(re, q)) && l in LTB.LookIds(PIV.QidBody(re, q))
    ensures LookRec(PIV.QidBody(re, q), best, rp, AI.get_idx(best.2.a_cp, q), AI.get_idx(best.2.a_clk, q), l,
                    l in PathLooksR(qm, PIV.QidBody(re, q), T.InputAt(str, AI.get_idx(best.2.a_cp, q) as nat)))
  {
    reveal LookRecordOk();
  }

  /** `LookRec` reads the lid's record, and the body's ancestor registers only. */
  lemma LookRecFrame(body: R.regex, rg0: Regs3, rg0': Regs3, a: Regs3, b: Regs3, cp: int, K: int, l: nat, on: bool)
    requires l in LTB.LookIds(body) && LookRec(body, rg0, a, cp, K, l, on)
    requires AI.get_idx(rg0'.1.a_cp, l) == AI.get_idx(rg0.1.a_cp, l) && AI.get_idx(rg0'.1.a_clk, l) == AI.get_idx(rg0.1.a_clk, l)
    requires AI.get_idx(b.1.a_cp, l) == AI.get_idx(a.1.a_cp, l) && AI.get_idx(b.1.a_clk, l) == AI.get_idx(a.1.a_clk, l)
    requires forall k: int :: k in NRR.CapRegsOf(body) ==> AI.get_idx(b.0.a_clk, k) == AI.get_idx(a.0.a_clk, k)
    requires forall k: int :: k in NRR.QuantRegsOf(body) ==> AI.get_idx(b.2.a_clk, k) == AI.get_idx(a.2.a_clk, k)
    ensures LookRec(body, rg0', b, cp, K, l, on)
  {
    CLP.AncSub(body, l);
    CLP.LookPathFrame(body, a.0.a_clk, a.2.a_clk, b.0.a_clk, b.2.a_clk, K, l);
  }

  /** A chain-fresh quantifier outside looks sits at or above the threshold. */
  lemma ChainFreshGe(r: R.regex, qc: seq<int>, mx: int, q: nat)
    requires PIV.QuantUnique(r) && q in PIV.QuantIds(r) && q in PIV.QuantIdsOutsideLooks(r)
    requires PIV.QChainFresh(r, qc, mx, q)
    ensures AI.get_idx(qc, q) >= mx
    decreases r
  {
    match r
    case Re_alt(r1, r2) => OLSide(r, q); if q in PIV.QuantIds(r1) { ChainFreshGe(r1, qc, mx, q); } else { ChainFreshGe(r2, qc, mx, q); }
    case Re_con(r1, r2) => OLSide(r, q); if q in PIV.QuantIds(r1) { ChainFreshGe(r1, qc, mx, q); } else { ChainFreshGe(r2, qc, mx, q); }
    case Re_quant(_, qid0, _, r1) =>
      if !(qid0 >= 0 && (qid0 as nat) == q) { ChainFreshGe(r1, qc, AI.get_idx(qc, qid0), q); }
    case Re_capture(_, r1) => ChainFreshGe(r1, qc, mx, q);
    case _ =>
  }

  /** A quantifier outside looks is outside looks on its own side of an alt/con. */
  lemma OLSide(r: R.regex, q: nat)
    requires (r.Re_alt? || r.Re_con?) && PIV.QuantUnique(r) && q in PIV.QuantIdsOutsideLooks(r)
    ensures q in PIV.QuantIds(NRR.L1(r)) ==> q in PIV.QuantIdsOutsideLooks(NRR.L1(r)) && q !in PIV.QuantIds(NRR.L2(r))
    ensures q !in PIV.QuantIds(NRR.L1(r)) ==> q in PIV.QuantIdsOutsideLooks(NRR.L2(r)) && q in PIV.QuantIds(NRR.L2(r))
  {
    var r1 := NRR.L1(r); var r2 := NRR.L2(r);
    PIV.QuantIdsOutsideLooksSub(r1); PIV.QuantIdsOutsideLooksSub(r2);
    assert PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
    if q in PIV.QuantIds(r1) && q in PIV.QuantIds(r2) { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
  }

  /** The record of a top lid of a live stamp's body after `FNulledPlus` over `r` (threshold `mx`). */
  lemma FPLook(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, mx: int, q: nat, l: nat)
    requires mx >= -1
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRR.LookUnique(r) && LTB.LookUnique(r)
    requires NRC.CdnTopRE(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires ov == qm.ov
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(r, rg) && NRR.LookCapsAbsent(r, rg)
    requires NRO.StampsLocalS(qm, r, str, rg, mx)
    requires q in PIV.QuantIdsOutsideLooks(r) && q in PIV.QuantIds(r)
    requires AI.get_idx(rg.2.a_cp, q) >= 0 && PIV.QChainFresh(r, rg.2.a_clk, mx, q)
    requires l in NI.TopLookIds(PIV.QidBody(r, q)) && l in LTB.LookIds(PIV.QidBody(r, q))
    ensures AI.get_idx(rg.2.a_cp, q) <= |str| && T.TransWf(PIV.QidBody(r, q))
    ensures LookRec(PIV.QidBody(r, q), rg, NRO.FP(r, rg, plus_bcv, str, ov), AI.get_idx(rg.2.a_cp, q), AI.get_idx(rg.2.a_clk, q), l,
                    l in PathLooksR(qm, PIV.QidBody(r, q), T.InputAt(str, AI.get_idx(rg.2.a_cp, q) as nat)))
    decreases r, 1
  {
    match r {
      case Re_empty =>
      case Re_character(_) =>
      case Re_anchor(_) =>
      case Re_lookaround(_, _, _) =>
      case Re_capture(_, r1) =>
        NRC.CdnTopChild(r);
        NRR.PlusTableOkSChildren(r, plus_bcv);
        NRO.CapUniqueChildS(r);
        NRO.StampsLocalSChild(qm, r, str, rg, mx);
        NRR.CoversChild(r, rg);
        assert NRR.L1(r) == r1;
        assert NRO.FP(r, rg, plus_bcv, str, ov) == NRO.FP(r1, rg, plus_bcv, str, ov);
        assert PIV.CapIdsInLooks(r1) == PIV.CapIdsInLooks(r);
        FPLook(qm, r1, rg, plus_bcv, str, ov, mx, q, l);
      case Re_quant(_, qid, _, _) =>
        if qid as nat == q {
          FPLookStamp(qm, r, rg, plus_bcv, str, ov, mx, q, l);
        } else {
          FPLookQuant(qm, r, rg, plus_bcv, str, ov, mx, q, l);
        }
      case Re_alt(_, _) =>
        FPLookBin(qm, r, rg, plus_bcv, str, ov, mx, q, l);
      case Re_con(_, _) =>
        FPLookBin(qm, r, rg, plus_bcv, str, ov, mx, q, l);
    }
  }

  /** The live stamp's own node: `FNulledPlus` replays the body from the stamp (`NRO.StampReadoutS`'s
      unfolding), and `EngineLookReadout` reads the record. */
  lemma FPLookStamp(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, mx: int, q: nat, l: nat)
    requires mx >= -1
    requires r.Re_quant? && r.qid >= 0 && r.qid as nat == q
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRR.LookUnique(r) && LTB.LookUnique(r)
    requires NRC.CdnTopRE(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires ov == qm.ov
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(r, rg) && NRR.LookCapsAbsent(r, rg)
    requires NRO.StampsLocalS(qm, r, str, rg, mx)
    requires q in PIV.QuantIds(r)
    requires AI.get_idx(rg.2.a_cp, q) >= 0 && PIV.QChainFresh(r, rg.2.a_clk, mx, q)
    requires l in NI.TopLookIds(PIV.QidBody(r, q)) && l in LTB.LookIds(PIV.QidBody(r, q))
    ensures AI.get_idx(rg.2.a_cp, q) <= |str| && T.TransWf(PIV.QidBody(r, q))
    ensures LookRec(PIV.QidBody(r, q), rg, NRO.FP(r, rg, plus_bcv, str, ov), AI.get_idx(rg.2.a_cp, q), AI.get_idx(rg.2.a_clk, q), l,
                    l in PathLooksR(qm, PIV.QidBody(r, q), T.InputAt(str, AI.get_idx(rg.2.a_cp, q) as nat)))
  {
    var qid := r.qid; var r1 := NRR.L1(r);
    var K := AI.get_idx(rg.2.a_clk, qid);
    assert PIV.QidBody(r, q) == r1;
    assert NRR.QidStampPlus(r, q) && 0 <= AI.get_idx(rg.2.a_cp, qid) <= |str|
        && (q as int) in qm.bodies && qm.bodies[q as int] == r1 && T.TransWf(r1);
    var cp: nat := AI.get_idx(rg.2.a_cp, qid) as nat;
    var cpi := cp as int;
    var inp := T.InputAt(str, cp);
    assert TR.FirstEmptyPathR(qm, r1, inp).Some?;
    assert NRR.RegsStale(r1, rg, K);
    assert K >= mx;
    assert NRR.LookCapsAbsent(r1, rg) by { assert PIV.CapIdsInLooks(r1) == PIV.CapIdsInLooks(r); }
    assert {:split_here} true;
    // unfold FNulledPlus's Some branch (as `NRO.StampReadoutS`)
    assert AReg.get_cp(rg.2, qid) == Some(cpi);
    assert AI.opt_int(AReg.get_clock(rg.2, qid)) == K;
    var code := AI.get_code_v(plus_bcv, qid);
    assert code == CP.compile_reconstruct_nulled(r1);
    var ctx := AI.cp_context(cpi, str, RA.Forward);
    var subcdn := LCdn.compile_cdns(r1);
    var subtable := LCdn.build_cdn_v(subcdn, cpi, ov, ctx, RA.Forward);
    var inits := AI.FInitState(code, cpi, rg.0, rg.1, rg.2, K, ctx).(cdn := subtable);
    var (result, sF, ov1) := AI.FNullInterp(code, inits, ov, RA.Forward);
    NRR.CpOfInputAt(str, cp);
    assert inits == AI.FInitState(code, TR.CpOf(inp) as int, rg.0, rg.1, rg.2, K, TR.CtxOf(inp)).(cdn := inits.cdn);
    NRO.CapUniqueChildS(r);
    NRR.SubtableBitsOk(qm, r1, str, cp, ov);
    NRC.NullInterpNulledT(qm, r1, inp, inits, ov, rg.0, rg.1, rg.2, K);
    NRR.NulledWritesIffPath(qm, r1, inp);
    assert result.Some? && ov1 == ov;
    var w1 := NRC.NulledWrites(qm, r1, inp).value;
    var clks: seq<int> :| |clks| == |w1| && NRC.Incr(clks) && NRC.ClksIn(clks, K, sF.clock)
                          && NRC.RegsOf(result.value) == NRC.ApplyWrites(w1, cpi, clks, rg);
    var rgW := NRC.ApplyWrites(w1, cpi, clks, rg);
    var rg2 := NRO.FP(r, rg, plus_bcv, str, ov);
    assert rg2 == NRR.FC(r1, subtable, cpi, rgW, plus_bcv, str, ov);
    assert {:split_here} true;
    NRR.PlusTableOkSChildren(r, plus_bcv);
    assert NRR.ReadoutCtx(qm, r1, plus_bcv, ov, str, cp);
    assert PIV.CapIds(r1) <= PIV.CapIds(r) && PIV.QuantIds(r1) <= PIV.QuantIds(r) && NRR.LookIds(r1) <= NRR.LookIds(r);
    assert NRR.Covers(r1, rg);
    assert NRR.RegsCtx(r1, rg, K);
    EngineLookReadout(qm, r1, subtable, cp, rg, K, clks, plus_bcv, str, ov, l);
    assert rg2 == RG2(qm, r1, subtable, cp, rg, clks, plus_bcv, str, ov);
  }

  /** A quantifier above the live stamp: it is unstamped (a stamped one would be chain-fresh, and its
      stale body would put the stamp's clock below its own, F4), so `FNulledPlus` descends. */
  lemma FPLookQuant(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, mx: int, q: nat, l: nat)
    requires mx >= -1
    requires r.Re_quant? && r.qid >= 0 && r.qid as nat != q
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRR.LookUnique(r) && LTB.LookUnique(r)
    requires NRC.CdnTopRE(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires ov == qm.ov
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(r, rg) && NRR.LookCapsAbsent(r, rg)
    requires NRO.StampsLocalS(qm, r, str, rg, mx)
    requires q in PIV.QuantIdsOutsideLooks(r) && q in PIV.QuantIds(r)
    requires AI.get_idx(rg.2.a_cp, q) >= 0 && PIV.QChainFresh(r, rg.2.a_clk, mx, q)
    requires l in NI.TopLookIds(PIV.QidBody(r, q)) && l in LTB.LookIds(PIV.QidBody(r, q))
    ensures AI.get_idx(rg.2.a_cp, q) <= |str| && T.TransWf(PIV.QidBody(r, q))
    ensures LookRec(PIV.QidBody(r, q), rg, NRO.FP(r, rg, plus_bcv, str, ov), AI.get_idx(rg.2.a_cp, q), AI.get_idx(rg.2.a_clk, q), l,
                    l in PathLooksR(qm, PIV.QidBody(r, q), T.InputAt(str, AI.get_idx(rg.2.a_cp, q) as nat)))
    decreases r, 0
  {
    NRC.CdnTopChild(r);
    var qid := r.qid; var r1 := NRR.L1(r);
    var qc := rg.2.a_clk;
    assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
    var qv := AI.get_idx(qc, qid);
    assert qv >= mx && q in PIV.QuantIds(r1) && q in PIV.QuantIdsOutsideLooks(r1) && PIV.QChainFresh(r1, qc, qv, q);
    assert PIV.QidBody(r, q) == PIV.QidBody(r1, q);
    NRR.PlusTableOkSChildren(r, plus_bcv);
    NRO.CapUniqueChildS(r);
    NRO.StampsLocalSChild(qm, r, str, rg, mx);
    ChainFreshGe(r1, qc, qv, q);
    if AI.get_idx(rg.2.a_cp, qid) >= 0 {
      assert PIV.QChainFresh(r, qc, mx, qid as nat);
      assert PIV.QidBody(r, qid as nat) == r1;
      assert NRR.RegsStale(r1, rg, qv);
      assert false;
    }
    var rg' := NRO.FP(r, rg, plus_bcv, str, ov);
    assert rg' == NRO.FP(r1, rg, plus_bcv, str, ov) by { assert AReg.get_cp(rg.2, qid) == None; }
    NRR.CoversChild(r, rg);
    assert PIV.CapIdsInLooks(r1) == PIV.CapIdsInLooks(r);
    FPLook(qm, r1, rg, plus_bcv, str, ov, qv, q, l);
  }

  /** Alt / con: the stamp's side runs on registers that agree with `rg` on its own; the other side's run
      leaves the body's registers alone. */
  lemma {:induction false} FPLookBin(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, mx: int, q: nat, l: nat)
    requires mx >= -1
    requires r.Re_alt? || r.Re_con?
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRR.LookUnique(r) && LTB.LookUnique(r)
    requires NRC.CdnTopRE(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires ov == qm.ov
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(r, rg) && NRR.LookCapsAbsent(r, rg)
    requires NRO.StampsLocalS(qm, r, str, rg, mx)
    requires q in PIV.QuantIdsOutsideLooks(r) && q in PIV.QuantIds(r)
    requires AI.get_idx(rg.2.a_cp, q) >= 0 && PIV.QChainFresh(r, rg.2.a_clk, mx, q)
    requires l in NI.TopLookIds(PIV.QidBody(r, q)) && l in LTB.LookIds(PIV.QidBody(r, q))
    ensures AI.get_idx(rg.2.a_cp, q) <= |str| && T.TransWf(PIV.QidBody(r, q))
    ensures LookRec(PIV.QidBody(r, q), rg, NRO.FP(r, rg, plus_bcv, str, ov), AI.get_idx(rg.2.a_cp, q), AI.get_idx(rg.2.a_clk, q), l,
                    l in PathLooksR(qm, PIV.QidBody(r, q), T.InputAt(str, AI.get_idx(rg.2.a_cp, q) as nat)))
    decreases r, 0
  {
    NRC.CdnTopChild(r);
    var r1 := NRR.L1(r); var r2 := NRR.L2(r);
    NRR.PlusTableOkSChildren(r, plus_bcv);
    NRO.CapUniqueChildS(r);
    NRR.DisjointRegs(r);
    NRO.StampsLocalSChild(qm, r, str, rg, mx);
    NRR.InnerSub(r1); NRR.InnerSub(r2);
    NRR.CoversChild(r, rg);
    var rgA := NRO.FP(r1, rg, plus_bcv, str, ov);
    var rg' := NRO.FP(r, rg, plus_bcv, str, ov);
    NRO.ReconReadoutSubS(qm, r1, rg, plus_bcv, str, ov, mx);
    NRO.FNulledPlusFrameS(qm, r1, rg, plus_bcv, str, ov);
    assert rg' == NRO.FP(r2, rgA, plus_bcv, str, ov);
    assert NRR.Covers(r2, rgA) && NRR.LookCapsAbsent(r2, rgA) && NRO.StampsLocalS(qm, r2, str, rgA, mx) by {
      NRR.CoversSized(r2, rg, rgA);
      NRR.SubAgree2(r, rg, rgA);
      NRR.CapIdsInLooksSub(r2); NRR.CapRegsOfChar(r2);
      assert NRR.LookCapsAbsent(r2, rgA) by {
        forall c: nat | c in PIV.CapIdsInLooks(r2) ensures AI.get_idx(rgA.0.a_cp, CP.start_reg(c)) < 0 { assert CP.start_reg(c) in NRR.CapRegsOf(r2); }
      }
      NRO.StampsLocalSTransfer(qm, r2, str, rg, rgA, mx);
    }
    NRO.ReconReadoutSubS(qm, r2, rgA, plus_bcv, str, ov, mx);
    NRO.FNulledPlusFrameS(qm, r2, rgA, plus_bcv, str, ov);
    assert {:split_here} true;
    OLSide(r, q);
    var body := PIV.QidBody(r, q);
    if q in PIV.QuantIds(r1) {
      assert body == PIV.QidBody(r1, q);
      FPLook(qm, r1, rg, plus_bcv, str, ov, mx, q, l);
      NRO.QidBodyRegs(r1, q);
      NI.QidBodyLookIdsSub(r1, q);
      assert l in LTB.LookIds(r1) && l in LTB.LookIds(r);
      LookSidesDisjoint(r, l);
      LookRecFrame(body, rg, rg, rgA, rg', AI.get_idx(rg.2.a_cp, q), AI.get_idx(rg.2.a_clk, q), l,
                   l in PathLooksR(qm, body, T.InputAt(str, AI.get_idx(rg.2.a_cp, q) as nat)));
    } else {
      assert body == PIV.QidBody(r2, q);
      NRR.SubAgree2(r, rg, rgA);
      NRR.QuantRegsOfChar(r2);
      assert AI.get_idx(rgA.2.a_cp, q) == AI.get_idx(rg.2.a_cp, q) && AI.get_idx(rgA.2.a_clk, q) == AI.get_idx(rg.2.a_clk, q);
      NRO.QChainFreshDep(r2, rg.2.a_clk, rgA.2.a_clk, mx, q);
      FPLook(qm, r2, rgA, plus_bcv, str, ov, mx, q, l);
      NI.QidBodyLookIdsSub(r2, q);
      assert l in LTB.LookIds(r2) && l in LTB.LookIds(r);
      LookSidesDisjoint(r, l);
      assert l !in LTB.LookIds(r1) by { if l in LTB.LookIds(r1) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } }
      assert AI.get_idx(rgA.1.a_cp, l) == AI.get_idx(rg.1.a_cp, l) && AI.get_idx(rgA.1.a_clk, l) == AI.get_idx(rg.1.a_clk, l);
      LookRecFrame(body, rgA, rg, rg', rg', AI.get_idx(rg.2.a_cp, q), AI.get_idx(rg.2.a_clk, q), l,
                   l in PathLooksR(qm, body, T.InputAt(str, AI.get_idx(rg.2.a_cp, q) as nat)));
    }
  }

  /** L3 at the `FNulledPlus` level (the premises of `NRO.ReconReadoutS`, plus `LTB.LookUnique`). */
  lemma ReconLookRecord(qm: AR.QMap, re: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires T.TransWf(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && NRR.LookUnique(re) && LTB.LookUnique(re)
    requires NRC.CdnTopRE(re) && NRR.PlusTableOkS(re, plus_bcv)
    requires ov == qm.ov
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(re, rg) && NRR.LookCapsAbsent(re, rg)
    requires NRO.StampsLocalS(qm, re, str, rg, -1)
    ensures LookRecordOk(qm, re, str, rg, NRO.FP(re, rg, plus_bcv, str, ov))
  {
    var rp := NRO.FP(re, rg, plus_bcv, str, ov);
    forall q: nat, l: nat |
      PIV.QLive(re, rg.2.a_clk, rg.2.a_cp, q)
      && AI.get_idx(rg.2.a_cp, q) <= |str| && T.TransWf(PIV.QidBody(re, q))
      && l in NI.TopLookIds(PIV.QidBody(re, q)) && l in LTB.LookIds(PIV.QidBody(re, q))
      ensures LookRec(PIV.QidBody(re, q), rg, rp, AI.get_idx(rg.2.a_cp, q), AI.get_idx(rg.2.a_clk, q), l,
                      l in PathLooksR(qm, PIV.QidBody(re, q), T.InputAt(str, AI.get_idx(rg.2.a_cp, q) as nat)))
    {
      FPLook(qm, re, rg, plus_bcv, str, ov, -1, q, l);
    }
    reveal LookRecordOk();
  }

  // ===========================================================================
  // 4. Presence through a live stamp; dead stamps; `LooksQE` hosts
  // ===========================================================================

  /** Above a live stamp `q` the lid's look path is `q`'s own path (`PIV.PathPresentQ` + `PIV.QChainFresh`):
      presence at the top is presence inside the body from the stamp's clock, with the same threshold. */
  lemma LookPathPresentThroughQ(re: R.regex, cc: seq<int>, qc: seq<int>, mx: int, q: nat, l: nat)
    requires PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires q in PIV.QuantIds(re) && q in PIV.QuantIdsOutsideLooks(re)
    requires l in LTB.LookIds(PIV.QidBody(re, q))
    requires PIV.PathPresentQ(re, cc, qc, mx, q) && PIV.QChainFresh(re, qc, mx, q)
    ensures l in LTB.LookIds(re)
    ensures NI.LookPathPresent(re, cc, qc, mx, l) == NI.LookPathPresent(PIV.QidBody(re, q), cc, qc, AI.get_idx(qc, q), l)
    ensures NI.MxAtLidLk(re, qc, mx, l) == NI.MxAtLidLk(PIV.QidBody(re, q), qc, AI.get_idx(qc, q), l)
    decreases re, 1
  {
    NI.QidBodyLookIdsSub(re, q);
    match re
    case Re_alt(r1, r2) => LookPathPresentThroughQ2(re, cc, qc, mx, q, l);
    case Re_con(r1, r2) => LookPathPresentThroughQ2(re, cc, qc, mx, q, l);
    case Re_quant(_, qid0, _, r1) =>
      if !(qid0 >= 0 && (qid0 as nat) == q) {
        LookPathPresentThroughQ(r1, cc, qc, AI.get_idx(qc, qid0), q, l);
      }
    case Re_capture(_, r1) => LookPathPresentThroughQ(r1, cc, qc, mx, q, l);
    case _ =>
  }

  lemma LookPathPresentThroughQ2(re: R.regex, cc: seq<int>, qc: seq<int>, mx: int, q: nat, l: nat)
    requires re.Re_alt? || re.Re_con?
    requires PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires q in PIV.QuantIds(re) && q in PIV.QuantIdsOutsideLooks(re)
    requires l in LTB.LookIds(PIV.QidBody(re, q))
    requires PIV.PathPresentQ(re, cc, qc, mx, q) && PIV.QChainFresh(re, qc, mx, q)
    ensures l in LTB.LookIds(re)
    ensures NI.LookPathPresent(re, cc, qc, mx, l) == NI.LookPathPresent(PIV.QidBody(re, q), cc, qc, AI.get_idx(qc, q), l)
    ensures NI.MxAtLidLk(re, qc, mx, l) == NI.MxAtLidLk(PIV.QidBody(re, q), qc, AI.get_idx(qc, q), l)
    decreases re, 0
  {
    var r1 := NRR.L1(re); var r2 := NRR.L2(re);
    NI.QidBodyLookIdsSub(re, q);
    OLSide(re, q);
    assert LTB.LookIds(r1) * LTB.LookIds(r2) == {};
    if q in PIV.QuantIds(r1) {
      NI.QidBodyLookIdsSub(r1, q);
      LookPathPresentThroughQ(r1, cc, qc, mx, q, l);
    } else {
      NI.QidBodyLookIdsSub(r2, q);
      assert l !in LTB.LookIds(r1) by { if l in LTB.LookIds(r1) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } }
      LookPathPresentThroughQ(r2, cc, qc, mx, q, l);
    }
  }

  /** A quantifier whose clock is below the threshold in force hides every top lid of its body. */
  lemma BelowThresholdKills(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, q: nat, lid: nat)
    requires PIV.QuantUnique(r) && LTB.LookUnique(r)
    requires q in PIV.QuantIds(r) && lid in LTB.LookIds(PIV.QidBody(r, q)) && lid in NI.TopLookIds(r)
    requires AI.get_idx(qc, q) < mx
    ensures lid in LTB.LookIds(r) && !NI.LookPathPresent(r, cc, qc, mx, lid)
    decreases r, 1
  {
    NI.QidBodyLookIdsSub(r, q);
    match r
    case Re_alt(r1, r2) => BelowThresholdKills2(r, cc, qc, mx, q, lid);
    case Re_con(r1, r2) => BelowThresholdKills2(r, cc, qc, mx, q, lid);
    case Re_quant(_, qid0, _, r1) =>
      if !(qid0 >= 0 && (qid0 as nat) == q) {
        var qv := AI.get_idx(qc, qid0);
        if qv >= mx { BelowThresholdKills(r1, cc, qc, qv, q, lid); }
      }
    case Re_capture(_, r1) => BelowThresholdKills(r1, cc, qc, mx, q, lid);
    case Re_lookaround(lid0, _, r1) =>
      NI.QidBodyLookIdsSub(r1, q);
      assert false;
    case _ =>
  }

  lemma BelowThresholdKills2(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, q: nat, lid: nat)
    requires r.Re_alt? || r.Re_con?
    requires PIV.QuantUnique(r) && LTB.LookUnique(r)
    requires q in PIV.QuantIds(r) && lid in LTB.LookIds(PIV.QidBody(r, q)) && lid in NI.TopLookIds(r)
    requires AI.get_idx(qc, q) < mx
    ensures lid in LTB.LookIds(r) && !NI.LookPathPresent(r, cc, qc, mx, lid)
    decreases r, 0
  {
    var r1 := NRR.L1(r); var r2 := NRR.L2(r);
    NI.QidBodyLookIdsSub(r, q);
    LookSidesDisjoint(r, lid);
    assert PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
    if q in PIV.QuantIds(r1) {
      NI.QidBodyLookIdsSub(r1, q);
      BelowThresholdKills(r1, cc, qc, mx, q, lid);
    } else {
      NI.QidBodyLookIdsSub(r2, q);
      BelowThresholdKills(r2, cc, qc, mx, q, lid);
    }
  }

  /** (c) A quantifier `q` under a quantifier `qo` of LARGER clock (so `q` is not chain-fresh; for a stamped
      `q`: a dead stamp) kills the presence of every top lid in `q`'s body: below `qo` the threshold is at
      least `qo`'s clock, and `q`'s own clause fails. */
  lemma DeadStampKillsPresenceAt(re: R.regex, cc: seq<int>, qc: seq<int>, mx: int, qo: nat, q: nat, lid: nat)
    requires PIV.QuantUnique(re) && LTB.LookUnique(re) && lid in NI.TopLookIds(re)
    requires q in PIV.QuantIds(re) && lid in LTB.LookIds(PIV.QidBody(re, q))
    requires qo in PIV.QuantIds(re) && q in PIV.QuantIds(PIV.QidBody(re, qo)) && AI.get_idx(qc, qo) > AI.get_idx(qc, q)
    ensures lid in LTB.LookIds(re) && !NI.LookPathPresent(re, cc, qc, mx, lid)
    decreases re, 1
  {
    NI.QidBodyLookIdsSub(re, q);
    match re
    case Re_alt(r1, r2) => DeadStampKillsPresenceAt2(re, cc, qc, mx, qo, q, lid);
    case Re_con(r1, r2) => DeadStampKillsPresenceAt2(re, cc, qc, mx, qo, q, lid);
    case Re_quant(_, qid0, _, r1) =>
      var qv := AI.get_idx(qc, qid0);
      if qid0 >= 0 && (qid0 as nat) == qo {
        assert q in PIV.QuantIds(r1) && PIV.QidBody(re, q) == PIV.QidBody(r1, q);
        if qv >= mx { BelowThresholdKills(r1, cc, qc, qv, q, lid); }
      } else {
        SL.QuantIdsQidBodySub(r1, qo);
        assert q in PIV.QuantIds(r1) && PIV.QidBody(re, q) == PIV.QidBody(r1, q);
        if qv >= mx { DeadStampKillsPresenceAt(r1, cc, qc, qv, qo, q, lid); }
      }
    case Re_capture(_, r1) => DeadStampKillsPresenceAt(r1, cc, qc, mx, qo, q, lid);
    case Re_lookaround(lid0, _, r1) =>
      SL.QuantIdsQidBodySub(r1, qo);
      NI.QidBodyLookIdsSub(r1, q);
      assert false;
    case _ =>
  }

  lemma DeadStampKillsPresenceAt2(re: R.regex, cc: seq<int>, qc: seq<int>, mx: int, qo: nat, q: nat, lid: nat)
    requires re.Re_alt? || re.Re_con?
    requires PIV.QuantUnique(re) && LTB.LookUnique(re) && lid in NI.TopLookIds(re)
    requires q in PIV.QuantIds(re) && lid in LTB.LookIds(PIV.QidBody(re, q))
    requires qo in PIV.QuantIds(re) && q in PIV.QuantIds(PIV.QidBody(re, qo)) && AI.get_idx(qc, qo) > AI.get_idx(qc, q)
    ensures lid in LTB.LookIds(re) && !NI.LookPathPresent(re, cc, qc, mx, lid)
    decreases re, 0
  {
    var r1 := NRR.L1(re); var r2 := NRR.L2(re);
    NI.QidBodyLookIdsSub(re, q);
    LookSidesDisjoint(re, lid);
    assert PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
    if qo in PIV.QuantIds(r1) {
      SL.QuantIdsQidBodySub(r1, qo);
      NI.QidBodyLookIdsSub(r1, q);
      DeadStampKillsPresenceAt(r1, cc, qc, mx, qo, q, lid);
    } else {
      SL.QuantIdsQidBodySub(r2, qo);
      assert q !in PIV.QuantIds(r1) by { if q in PIV.QuantIds(r1) { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); } }
      NI.QidBodyLookIdsSub(r2, q);
      DeadStampKillsPresenceAt(r2, cc, qc, mx, qo, q, lid);
    }
  }

  lemma DeadStampKillsPresence(re: R.regex, cc: seq<int>, qc: seq<int>, q: nat, lid: nat)
    requires PIV.QuantUnique(re) && LTB.LookUnique(re) && lid in NI.TopLookIds(re) && lid in LTB.LookIds(re)
    requires q in PIV.QuantIds(re) && lid in LTB.LookIds(PIV.QidBody(re, q))
    requires exists qo: nat :: qo in PIV.QuantIds(re) && q in PIV.QuantIds(PIV.QidBody(re, qo)) && AI.get_idx(qc, qo) > AI.get_idx(qc, q)
    ensures !NI.LookPathPresent(re, cc, qc, -1, lid)
  {
    var qo: nat :| qo in PIV.QuantIds(re) && q in PIV.QuantIds(PIV.QidBody(re, qo)) && AI.get_idx(qc, qo) > AI.get_idx(qc, q);
    DeadStampKillsPresenceAt(re, cc, qc, -1, qo, q, lid);
  }

  /** The E-sets hold look ids of the regex. */
  lemma ELooksInLookIds(r: R.regex, l: nat)
    requires (l as int) in ELk.OwnLooksE(r) + ELk.InnerLookRegsE(r)
    ensures l in LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if (l as int) in ELk.OwnLooksE(r1) + ELk.InnerLookRegsE(r1) { ELooksInLookIds(r1, l); } else { ELooksInLookIds(r2, l); }
    case Re_con(r1, r2) =>
      if (l as int) in ELk.OwnLooksE(r1) + ELk.InnerLookRegsE(r1) { ELooksInLookIds(r1, l); } else { ELooksInLookIds(r2, l); }
    case Re_quant(_, _, _, r1) => ELooksInLookIds(r1, l);
    case Re_capture(_, r1) => ELooksInLookIds(r1, l);
    case _ =>
  }

  /** A lid of `ELk.LooksQE(re, Q)` sits in the body of a quantifier of `Q` (outside looks). */
  lemma LooksQEUnderStamp(re: R.regex, Q: set<int>, l: nat) returns (q: nat)
    requires PIV.QuantUnique(re) && (l as int) in ELk.LooksQE(re, Q)
    ensures (q as int) in Q && q in PIV.QuantIds(re) && q in PIV.QuantIdsOutsideLooks(re)
    ensures l in LTB.LookIds(PIV.QidBody(re, q))
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      assert PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
      if (l as int) in ELk.LooksQE(r1, Q) { q := LooksQEUnderStamp(r1, Q, l); }
      else {
        q := LooksQEUnderStamp(r2, Q, l);
        assert q !in PIV.QuantIds(r1) by { if q in PIV.QuantIds(r1) { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); } }
      }
    case Re_con(r1, r2) =>
      assert PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
      if (l as int) in ELk.LooksQE(r1, Q) { q := LooksQEUnderStamp(r1, Q, l); }
      else {
        q := LooksQEUnderStamp(r2, Q, l);
        assert q !in PIV.QuantIds(r1) by { if q in PIV.QuantIds(r1) { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); } }
      }
    case Re_quant(_, qid, _, body) =>
      if (l as int) in ELk.LooksQE(body, Q) {
        q := LooksQEUnderStamp(body, Q, l);
      } else {
        assert qid in Q && (l as int) in ELk.InnerLookRegsE(re);
        ELooksInLookIds(body, l);
        q := qid as nat;
      }
    case Re_capture(_, r1) => q := LooksQEUnderStamp(r1, Q, l);
    case _ => q := 0; assert false;
  }

  /** The path lids of a stamp-plus body lie in `ELk.LooksQE` of any stamp set holding the stamp:
      "crossed ⇒ in `LooksQE`" for the transports. */
  lemma PathLooksInQE(qm: AR.QMap, re: R.regex, Q: set<int>, q: nat, inp: LC.Input)
    requires PIV.QuantUnique(re) && q in PIV.QuantIds(re) && q in PIV.QuantIdsOutsideLooks(re) && (q as int) in Q
    requires NRR.QidStampPlus(re, q)
    requires T.TransWf(PIV.QidBody(re, q)) && TR.FirstEmptyPathR(qm, PIV.QidBody(re, q), inp).Some?
    ensures forall l: nat :: l in PathLooksR(qm, PIV.QidBody(re, q), inp) ==> (l as int) in ELk.LooksQE(re, Q)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => OLSide(re, q); if q in PIV.QuantIds(r1) { PathLooksInQE(qm, r1, Q, q, inp); } else { PathLooksInQE(qm, r2, Q, q, inp); }
    case Re_con(r1, r2) => OLSide(re, q); if q in PIV.QuantIds(r1) { PathLooksInQE(qm, r1, Q, q, inp); } else { PathLooksInQE(qm, r2, Q, q, inp); }
    case Re_quant(nul, qid0, qt, body) =>
      if qid0 >= 0 && (qid0 as nat) == q {
        PathLooksInE(qm, body, inp);
        assert RF.StampNode(nul, qt);
      } else {
        PathLooksInQE(qm, body, Q, q, inp);
      }
    case Re_capture(_, r1) => PathLooksInQE(qm, r1, Q, q, inp);
    case _ =>
  }

  // ===========================================================================
  // 5. The composed statement at the top of `re`: a live stamp's path survives the replay
  //    (`FPLiveFrame`), so §3's body-level record lifts through `LookPathPresentThroughQ`.
  // ===========================================================================

  /** `FNulledPlus` keeps a live stamp's own register and the registers its chain / path read. */
  lemma FPLiveFrame(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, mx: int, q: nat)
    requires mx >= -1
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRR.LookUnique(r)
    requires NRC.CdnTopRE(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires ov == qm.ov
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(r, rg) && NRR.LookCapsAbsent(r, rg)
    requires NRO.StampsLocalS(qm, r, str, rg, mx)
    requires q in PIV.QuantIdsOutsideLooks(r) && q in PIV.QuantIds(r)
    requires AI.get_idx(rg.2.a_cp, q) >= 0 && PIV.QChainFresh(r, rg.2.a_clk, mx, q)
    ensures var rg' := NRO.FP(r, rg, plus_bcv, str, ov);
            AI.get_idx(rg'.2.a_clk, q) == AI.get_idx(rg.2.a_clk, q) && AI.get_idx(rg'.2.a_cp, q) == AI.get_idx(rg.2.a_cp, q)
            && PIV.QChainFresh(r, rg'.2.a_clk, mx, q)
            && PIV.PathPresentQ(r, rg'.0.a_clk, rg'.2.a_clk, mx, q) == PIV.PathPresentQ(r, rg.0.a_clk, rg.2.a_clk, mx, q)
    decreases r, 1
  {
    match r {
      case Re_empty =>
      case Re_character(_) =>
      case Re_anchor(_) =>
      case Re_lookaround(_, _, _) =>
      case Re_capture(_, r1) =>
        NRC.CdnTopChild(r);
        NRR.PlusTableOkSChildren(r, plus_bcv);
        NRO.CapUniqueChildS(r);
        NRO.StampsLocalSChild(qm, r, str, rg, mx);
        NRR.CoversChild(r, rg);
        assert NRR.L1(r) == r1;
        assert NRO.FP(r, rg, plus_bcv, str, ov) == NRO.FP(r1, rg, plus_bcv, str, ov);
        assert PIV.CapIdsInLooks(r1) == PIV.CapIdsInLooks(r);
        FPLiveFrame(qm, r1, rg, plus_bcv, str, ov, mx, q);
        NRO.ReconReadoutSubS(qm, r1, rg, plus_bcv, str, ov, mx);
        NRO.FNulledPlusFrameS(qm, r1, rg, plus_bcv, str, ov);
        NRR.InnerSub(r1);
        NRR.CapRegsOfOwn(r);
      case Re_quant(_, qid, _, _) =>
        if qid as nat == q {
          FPLiveFrameStamp(qm, r, rg, plus_bcv, str, ov, mx, q);
        } else {
          FPLiveFrameQuant(qm, r, rg, plus_bcv, str, ov, mx, q);
        }
      case Re_alt(_, _) =>
        FPLiveFrameBin(qm, r, rg, plus_bcv, str, ov, mx, q);
      case Re_con(_, _) =>
        FPLiveFrameBin(qm, r, rg, plus_bcv, str, ov, mx, q);
    }
  }

  lemma FPLiveFrameStamp(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, mx: int, q: nat)
    requires mx >= -1
    requires r.Re_quant? && r.qid >= 0 && r.qid as nat == q
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRR.LookUnique(r)
    requires NRC.CdnTopRE(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires ov == qm.ov
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(r, rg) && NRR.LookCapsAbsent(r, rg)
    requires NRO.StampsLocalS(qm, r, str, rg, mx)
    requires q in PIV.QuantIds(r)
    requires AI.get_idx(rg.2.a_cp, q) >= 0 && PIV.QChainFresh(r, rg.2.a_clk, mx, q)
    ensures var rg' := NRO.FP(r, rg, plus_bcv, str, ov);
            AI.get_idx(rg'.2.a_clk, q) == AI.get_idx(rg.2.a_clk, q) && AI.get_idx(rg'.2.a_cp, q) == AI.get_idx(rg.2.a_cp, q)
            && PIV.QChainFresh(r, rg'.2.a_clk, mx, q)
            && PIV.PathPresentQ(r, rg'.0.a_clk, rg'.2.a_clk, mx, q) == PIV.PathPresentQ(r, rg.0.a_clk, rg.2.a_clk, mx, q)
  {
    var qid := r.qid; var r1 := NRR.L1(r);
    var K := AI.get_idx(rg.2.a_clk, qid);
    assert PIV.QidBody(r, q) == r1;
    assert NRR.QidStampPlus(r, q) && 0 <= AI.get_idx(rg.2.a_cp, qid) <= |str|
        && (q as int) in qm.bodies && qm.bodies[q as int] == r1 && T.TransWf(r1);
    var cp: nat := AI.get_idx(rg.2.a_cp, qid) as nat;
    assert TR.FirstEmptyPathR(qm, r1, T.InputAt(str, cp)).Some?;
    assert NRR.RegsStale(r1, rg, K);
    assert K >= mx;
    assert NRR.LookCapsAbsent(r1, rg) by { assert PIV.CapIdsInLooks(r1) == PIV.CapIdsInLooks(r); }
    NRO.StampReadoutS(qm, r, rg, plus_bcv, str, ov);
    assert NRO.PlusAt(qm, r, rg, plus_bcv, str, ov).0 == NRO.FP(r, rg, plus_bcv, str, ov);
    NRR.QuantRegsOfOwn(r);
  }

  lemma FPLiveFrameQuant(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, mx: int, q: nat)
    requires mx >= -1
    requires r.Re_quant? && r.qid >= 0 && r.qid as nat != q
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRR.LookUnique(r)
    requires NRC.CdnTopRE(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires ov == qm.ov
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(r, rg) && NRR.LookCapsAbsent(r, rg)
    requires NRO.StampsLocalS(qm, r, str, rg, mx)
    requires q in PIV.QuantIdsOutsideLooks(r) && q in PIV.QuantIds(r)
    requires AI.get_idx(rg.2.a_cp, q) >= 0 && PIV.QChainFresh(r, rg.2.a_clk, mx, q)
    ensures var rg' := NRO.FP(r, rg, plus_bcv, str, ov);
            AI.get_idx(rg'.2.a_clk, q) == AI.get_idx(rg.2.a_clk, q) && AI.get_idx(rg'.2.a_cp, q) == AI.get_idx(rg.2.a_cp, q)
            && PIV.QChainFresh(r, rg'.2.a_clk, mx, q)
            && PIV.PathPresentQ(r, rg'.0.a_clk, rg'.2.a_clk, mx, q) == PIV.PathPresentQ(r, rg.0.a_clk, rg.2.a_clk, mx, q)
    decreases r, 0
  {
    NRC.CdnTopChild(r);
    var qid := r.qid; var r1 := NRR.L1(r);
    var qc := rg.2.a_clk;
    assert (qid as nat) in PIV.QuantIds(r);
    var qv := AI.get_idx(qc, qid);
    assert qv >= mx && q in PIV.QuantIds(r1) && q in PIV.QuantIdsOutsideLooks(r1) && PIV.QChainFresh(r1, qc, qv, q);
    NRR.PlusTableOkSChildren(r, plus_bcv);
    NRO.CapUniqueChildS(r);
    NRO.StampsLocalSChild(qm, r, str, rg, mx);
    ChainFreshGe(r1, qc, qv, q);
    if AI.get_idx(rg.2.a_cp, qid) >= 0 {
      assert PIV.QChainFresh(r, qc, mx, qid as nat);
      assert PIV.QidBody(r, qid as nat) == r1;
      assert NRR.RegsStale(r1, rg, qv);
      assert false;
    }
    var rg' := NRO.FP(r, rg, plus_bcv, str, ov);
    assert rg' == NRO.FP(r1, rg, plus_bcv, str, ov) by { assert AReg.get_cp(rg.2, qid) == None; }
    NRR.CoversChild(r, rg);
    assert PIV.CapIdsInLooks(r1) == PIV.CapIdsInLooks(r);
    FPLiveFrame(qm, r1, rg, plus_bcv, str, ov, qv, q);
    NRO.ReconReadoutSubS(qm, r1, rg, plus_bcv, str, ov, qv);
    NRO.FNulledPlusFrameS(qm, r1, rg, plus_bcv, str, ov);
    NRR.InnerSub(r1);
    NRR.QuantRegsOfOwn(r);
    assert AI.get_idx(rg'.2.a_clk, qid) == qv;
  }

  lemma {:induction false} FPLiveFrameBin(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, mx: int, q: nat)
    requires mx >= -1
    requires r.Re_alt? || r.Re_con?
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRR.LookUnique(r)
    requires NRC.CdnTopRE(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires ov == qm.ov
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(r, rg) && NRR.LookCapsAbsent(r, rg)
    requires NRO.StampsLocalS(qm, r, str, rg, mx)
    requires q in PIV.QuantIdsOutsideLooks(r) && q in PIV.QuantIds(r)
    requires AI.get_idx(rg.2.a_cp, q) >= 0 && PIV.QChainFresh(r, rg.2.a_clk, mx, q)
    ensures var rg' := NRO.FP(r, rg, plus_bcv, str, ov);
            AI.get_idx(rg'.2.a_clk, q) == AI.get_idx(rg.2.a_clk, q) && AI.get_idx(rg'.2.a_cp, q) == AI.get_idx(rg.2.a_cp, q)
            && PIV.QChainFresh(r, rg'.2.a_clk, mx, q)
            && PIV.PathPresentQ(r, rg'.0.a_clk, rg'.2.a_clk, mx, q) == PIV.PathPresentQ(r, rg.0.a_clk, rg.2.a_clk, mx, q)
    decreases r, 0
  {
    NRC.CdnTopChild(r);
    var r1 := NRR.L1(r); var r2 := NRR.L2(r);
    NRR.PlusTableOkSChildren(r, plus_bcv);
    NRO.CapUniqueChildS(r);
    NRR.DisjointRegs(r);
    NRO.StampsLocalSChild(qm, r, str, rg, mx);
    NRR.InnerSub(r1); NRR.InnerSub(r2);
    NRR.CoversChild(r, rg);
    var rgA := NRO.FP(r1, rg, plus_bcv, str, ov);
    var rg' := NRO.FP(r, rg, plus_bcv, str, ov);
    NRO.ReconReadoutSubS(qm, r1, rg, plus_bcv, str, ov, mx);
    NRO.FNulledPlusFrameS(qm, r1, rg, plus_bcv, str, ov);
    assert rg' == NRO.FP(r2, rgA, plus_bcv, str, ov);
    assert NRR.Covers(r2, rgA) && NRR.LookCapsAbsent(r2, rgA) && NRO.StampsLocalS(qm, r2, str, rgA, mx) by {
      NRR.CoversSized(r2, rg, rgA);
      NRR.SubAgree2(r, rg, rgA);
      NRR.CapIdsInLooksSub(r2); NRR.CapRegsOfChar(r2);
      assert NRR.LookCapsAbsent(r2, rgA) by {
        forall c: nat | c in PIV.CapIdsInLooks(r2) ensures AI.get_idx(rgA.0.a_cp, CP.start_reg(c)) < 0 { assert CP.start_reg(c) in NRR.CapRegsOf(r2); }
      }
      NRO.StampsLocalSTransfer(qm, r2, str, rg, rgA, mx);
    }
    NRO.ReconReadoutSubS(qm, r2, rgA, plus_bcv, str, ov, mx);
    NRO.FNulledPlusFrameS(qm, r2, rgA, plus_bcv, str, ov);
    assert {:split_here} true;
    OLSide(r, q);
    NRR.QuantRegsOfChar(r1); NRR.QuantRegsOfChar(r2);
    NRR.CapRegsOfChar(r1); NRR.CapRegsOfChar(r2);
    if q in PIV.QuantIds(r1) {
      FPLiveFrame(qm, r1, rg, plus_bcv, str, ov, mx, q);
      NRR.SubAgree(r, rgA, rg');
      NRO.QChainFreshDep(r1, rgA.2.a_clk, rg'.2.a_clk, mx, q);
      NRO.PathPresentQDep(r1, rgA.0.a_clk, rg'.0.a_clk, rgA.2.a_clk, rg'.2.a_clk, mx, q);
    } else {
      NRR.SubAgree2(r, rg, rgA);
      NRO.QChainFreshDep(r2, rg.2.a_clk, rgA.2.a_clk, mx, q);
      NRO.PathPresentQDep(r2, rg.0.a_clk, rgA.0.a_clk, rg.2.a_clk, rgA.2.a_clk, mx, q);
      FPLiveFrame(qm, r2, rgA, plus_bcv, str, ov, mx, q);
    }
  }

  /** `LookRec` read at the top of the regex (threshold `-1`), for a lid under a stamp of clock `K` at `cp`. */
  ghost predicate LookRecTop(re: R.regex, rg0: Regs3, rg2: Regs3, cp: int, K: int, l: nat, on: bool)
    requires l in LTB.LookIds(re)
  {
    if on then
      AI.get_idx(rg2.1.a_cp, l) == cp && AI.get_idx(rg2.1.a_clk, l) > K
      && NI.LookPathPresent(re, rg2.0.a_clk, rg2.2.a_clk, -1, l)
      && AI.get_idx(rg2.1.a_clk, l) >= NI.MxAtLidLk(re, rg2.2.a_clk, -1, l)
    else
      (AI.get_idx(rg2.1.a_cp, l) == AI.get_idx(rg0.1.a_cp, l) && AI.get_idx(rg2.1.a_clk, l) == AI.get_idx(rg0.1.a_clk, l))
      || !NI.LookPathPresent(re, rg2.0.a_clk, rg2.2.a_clk, -1, l)
  }

  /** L3 at the top of `re`, per live stamp `q` and top lid `l` of its body: the composition of
      `FPLook`, `FPLiveFrame` and `LookPathPresentThroughQ` (what the transports' cases (a)/(b) read). */
  lemma ReconLookRecordTop(qm: AR.QMap, re: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, q: nat, l: nat)
    requires T.TransWf(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && NRR.LookUnique(re) && LTB.LookUnique(re)
    requires NRC.CdnTopRE(re) && NRR.PlusTableOkS(re, plus_bcv)
    requires ov == qm.ov
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(re, rg) && NRR.LookCapsAbsent(re, rg)
    requires NRO.StampsLocalS(qm, re, str, rg, -1)
    requires PIV.QLive(re, rg.2.a_clk, rg.2.a_cp, q)
    requires l in NI.TopLookIds(PIV.QidBody(re, q)) && l in LTB.LookIds(PIV.QidBody(re, q))
    ensures AI.get_idx(rg.2.a_cp, q) <= |str| && T.TransWf(PIV.QidBody(re, q)) && l in LTB.LookIds(re)
    ensures var rp := NRO.FP(re, rg, plus_bcv, str, ov);
            var cp := AI.get_idx(rg.2.a_cp, q); var K := AI.get_idx(rg.2.a_clk, q);
            AI.get_idx(rp.2.a_clk, q) == K && AI.get_idx(rp.2.a_cp, q) == cp
            && PIV.QChainFresh(re, rp.2.a_clk, -1, q) && PIV.PathPresentQ(re, rp.0.a_clk, rp.2.a_clk, -1, q)
            && LookRecTop(re, rg, rp, cp, K, l, l in PathLooksR(qm, PIV.QidBody(re, q), T.InputAt(str, cp as nat)))
  {
    var rp := NRO.FP(re, rg, plus_bcv, str, ov);
    FPLook(qm, re, rg, plus_bcv, str, ov, -1, q, l);
    FPLiveFrame(qm, re, rg, plus_bcv, str, ov, -1, q);
    assert PIV.PathPresentQ(re, rg.0.a_clk, rg.2.a_clk, -1, q);
    LookPathPresentThroughQ(re, rp.0.a_clk, rp.2.a_clk, -1, q, l);
  }
}
