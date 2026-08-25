// FlipClosed.dfy — L5 F7e (part 1): CLOSEDNESS of a positive LOOKBEHIND's body
// sub-leaf under the forward depth-stratification hypothesis `M.ClosedBelow`.
//
// The L4 closedness ladder (`M.FirstLeafClosedRecAux`) discharges a positive
// look's body sub-leaf through `M.ClosedBelow(rer, D)`, a FORWARD-only
// hypothesis (`TreeRes(.., WP.Forward)`), so its `LookaroundR` arm pins
// `LkDir(lk) == Forward` (`FwdPosLooksL`). For a positive LOOKBEHIND with a
// lookbehind-only body (`SD.GroupOkLB`) the same hypothesis suffices: the FLIP
// mirror (F1 builder `FM.ComputeTrReverseF` + the general-gm fold
// `FM.TreeResMirrorF` under `FD.ComputeTrCloseDiscF`) sends the backward walk
// from a CLOSED `gmR` to the flipped body's FORWARD walk from `MirrorGm(gmR)`,
// which is a `ClosedBelow` instance (all its looks are lookaheads after the
// flip); closedness is `MirrorGm`-invariant, so it transports back.
//
//   `BackBodyLeafClosedFromBelow` = the Backward twin of `M.BodyLeafClosedFromBelow`.
// Part 2 (next): the L5 ladder copy `FirstLeafClosedRecAuxL5` with the LB arm.
include "MainTheorem.dfy"
include "FlipDisc.dfy"

module LindenElkFlipClosed {
  import opened Std.Wrappers
  import M = LindenElkMain
  import FM = LindenElkFlipMirror
  import FD = LindenElkFlipDisc
  import FR = LindenElkFlipRev
  import TML = LindenElkTreeMirrorLk
  import TRM = LindenTreeResMirror
  import SD = LindenSpanDuality
  import EL = LindenElkEntryLk
  import LFS = FunctionalSemantics
  import BS = BooleanSemantics
  import CD = LindenCloseDisc
  import LW = WarblreRegExpRecord
  import LT = Tree
  import LG = Groups
  import LS = Semantics
  import LC = Chars
  import FU = FunctionalUtils
  import WP = WarblrePrimitives
  import L = Regex

  // ===========================================================================
  // Side lemmas: structural facts about the flip-reversed body
  // ===========================================================================

  /** `NoDupSeq` of a concatenation, both ways. */
  lemma NoDupSeqAppendIff(a: seq<LG.GroupId>, b: seq<LG.GroupId>)
    ensures M.NoDupSeq(a + b) <==> (M.NoDupSeq(a) && M.NoDupSeq(b) && forall x :: x in a ==> x !in b)
  {
    if M.NoDupSeq(a + b) {
      forall i, j | 0 <= i < j < |a| ensures a[i] != a[j] { assert (a + b)[i] == a[i] && (a + b)[j] == a[j]; }
      forall i, j | 0 <= i < j < |b| ensures b[i] != b[j] {
        assert (a + b)[|a| + i] == b[i] && (a + b)[|a| + j] == b[j];
      }
      forall x | x in a ensures x !in b {
        if x in b {
          var i :| 0 <= i < |a| && a[i] == x;
          var j :| 0 <= j < |b| && b[j] == x;
          assert (a + b)[i] == x && (a + b)[|a| + j] == x;
          assert false;
        }
      }
    }
    if M.NoDupSeq(a) && M.NoDupSeq(b) && (forall x :: x in a ==> x !in b) {
      forall i, j | 0 <= i < j < |a + b| ensures (a + b)[i] != (a + b)[j] {
        if j < |a| { assert (a + b)[i] == a[i] && (a + b)[j] == a[j]; }
        else if i >= |a| { assert (a + b)[i] == b[i - |a|] && (a + b)[j] == b[j - |a|]; }
        else { assert (a + b)[i] == a[i] && a[i] in a && (a + b)[j] == b[j - |a|] && b[j - |a|] in b; }
      }
    }
  }

  /** `RevL` permutes the defined-group sequence (concatenations swap), so
      `NoDupSeq` is preserved. */
  lemma NoDupSeqRevL(r: L.Regex)
    requires M.NoDupSeq(L.DefGroups(r))
    ensures M.NoDupSeq(L.DefGroups(SD.RevL(r)))
    decreases r
  {
    match r
    case Disjunction(r1, r2) =>
      NoDupSeqAppendIff(L.DefGroups(r1), L.DefGroups(r2));
      NoDupSeqRevL(r1); NoDupSeqRevL(r2);
      SD.RevLDefGroupsSet(r1); SD.RevLDefGroupsSet(r2);
      NoDupSeqAppendIff(L.DefGroups(SD.RevL(r1)), L.DefGroups(SD.RevL(r2)));
    case Sequence(r1, r2) =>
      NoDupSeqAppendIff(L.DefGroups(r1), L.DefGroups(r2));
      NoDupSeqRevL(r1); NoDupSeqRevL(r2);
      SD.RevLDefGroupsSet(r1); SD.RevLDefGroupsSet(r2);
      assert forall x :: x in L.DefGroups(SD.RevL(r2)) ==> x !in L.DefGroups(SD.RevL(r1));
      NoDupSeqAppendIff(L.DefGroups(SD.RevL(r2)), L.DefGroups(SD.RevL(r1)));
    case Quantified(_, _, _, r1) => NoDupSeqRevL(r1);
    case LookaroundR(_, r1) => NoDupSeqRevL(r1);
    case Group(id, r1) =>
      NoDupSeqAppendIff([id], L.DefGroups(r1));
      NoDupSeqRevL(r1);
      SD.RevLDefGroupsSet(r1);
      NoDupSeqAppendIff([id], L.DefGroups(SD.RevL(r1)));
    case _ =>
  }

  lemma NoDupSeqFlipRevL(r: L.Regex)
    requires M.NoDupSeq(L.DefGroups(r))
    ensures M.NoDupSeq(L.DefGroups(FM.FlipRevL(r)))
  {
    NoDupSeqRevL(r);
    FM.FlipLDefGroups(SD.RevL(r));
  }

  /** Look nesting depth is invariant under `RevL` and `FlipL`. */
  lemma NestDepthRevL(r: L.Regex)
    ensures M.NestDepthL(SD.RevL(r)) == M.NestDepthL(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => NestDepthRevL(r1); NestDepthRevL(r2);
    case Sequence(r1, r2) => NestDepthRevL(r1); NestDepthRevL(r2);
    case Quantified(_, _, _, r1) => NestDepthRevL(r1);
    case Group(_, r1) => NestDepthRevL(r1);
    case LookaroundR(_, r1) => NestDepthRevL(r1);
    case _ =>
  }
  lemma NestDepthFlipL(r: L.Regex)
    ensures M.NestDepthL(FR.FlipL(r)) == M.NestDepthL(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => NestDepthFlipL(r1); NestDepthFlipL(r2);
    case Sequence(r1, r2) => NestDepthFlipL(r1); NestDepthFlipL(r2);
    case Quantified(_, _, _, r1) => NestDepthFlipL(r1);
    case Group(_, r1) => NestDepthFlipL(r1);
    case LookaroundR(_, r1) => NestDepthFlipL(r1);
    case _ =>
  }
  lemma NestDepthFlipRevL(r: L.Regex)
    ensures M.NestDepthL(FM.FlipRevL(r)) == M.NestDepthL(r)
  { NestDepthRevL(r); NestDepthFlipL(SD.RevL(r)); }

  /** A lookbehind-only regex flips to a lookAHEAD-only one: every positive look
      of `FlipRevL(r)` is Forward (`RevL` keeps kinds; `FlipLk` flips them). */
  lemma GroupOkLBRevL(r: L.Regex)
    requires SD.GroupOkLB(r)
    ensures SD.GroupOkLB(SD.RevL(r))
    decreases r
  {
    match r
    case Disjunction(r1, r2) => GroupOkLBRevL(r1); GroupOkLBRevL(r2);
    case Sequence(r1, r2) => GroupOkLBRevL(r1); GroupOkLBRevL(r2);
    case Quantified(_, _, _, r1) => GroupOkLBRevL(r1);
    case Group(_, r1) => GroupOkLBRevL(r1);
    case LookaroundR(_, r1) => GroupOkLBRevL(r1);
    case _ =>
  }
  lemma FlipLFwdPos(r: L.Regex)
    requires SD.GroupOkLB(r)
    ensures M.FwdPosLooksL(FR.FlipL(r))
    decreases r
  {
    match r
    case Disjunction(r1, r2) => FlipLFwdPos(r1); FlipLFwdPos(r2);
    case Sequence(r1, r2) => FlipLFwdPos(r1); FlipLFwdPos(r2);
    case Quantified(_, _, _, r1) => FlipLFwdPos(r1);
    case Group(_, r1) => FlipLFwdPos(r1);
    case LookaroundR(lk, r1) =>
      FlipLFwdPos(r1);
      assert lk.LookBehind? || lk.NegLookBehind?;
      assert FR.FlipLk(lk).LookAhead? || FR.FlipLk(lk).NegLookAhead?;
    case _ =>
  }
  lemma FlipRevLFwdPos(r: L.Regex)
    requires SD.GroupOkLB(r)
    ensures M.FwdPosLooksL(FM.FlipRevL(r))
  { GroupOkLBRevL(r); FlipLFwdPos(SD.RevL(r)); }

  /** `FlipL` keeps the pike-lk shape (positivity and groups are untouched). */
  lemma FlipLGroupFree(r: L.Regex)
    ensures SD.GroupFreeL(FR.FlipL(r)) <==> SD.GroupFreeL(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => FlipLGroupFree(r1); FlipLGroupFree(r2);
    case Sequence(r1, r2) => FlipLGroupFree(r1); FlipLGroupFree(r2);
    case Quantified(_, _, _, r1) => FlipLGroupFree(r1);
    case Group(_, r1) => FlipLGroupFree(r1);
    case LookaroundR(_, r1) => FlipLGroupFree(r1);
    case _ =>
  }
  lemma FlipLPikeLkRec(r: L.Regex)
    requires EL.PikeLkRegexRec(r)
    ensures EL.PikeLkRegexRec(FR.FlipL(r))
    decreases r
  {
    match r
    case Disjunction(r1, r2) => FlipLPikeLkRec(r1); FlipLPikeLkRec(r2);
    case Sequence(r1, r2) => FlipLPikeLkRec(r1); FlipLPikeLkRec(r2);
    case Quantified(_, _, _, r1) => FlipLPikeLkRec(r1);
    case Group(_, r1) => FlipLPikeLkRec(r1);
    case LookaroundR(lk, r1) =>
      FR.FlipLkLaws(lk);
      if L.Positivity(lk) { FlipLPikeLkRec(r1); } else { FlipLGroupFree(r1); }
    case _ =>
  }
  lemma FlipRevLPikeLkRec(r: L.Regex)
    requires EL.PikeLkRegexRec(r)
    ensures EL.PikeLkRegexRec(FM.FlipRevL(r))
  { TML.RevLPreservesPikeLkRec(r); FlipLPikeLkRec(SD.RevL(r)); }

  /** `MirrorGm` keeps closedness (both ways) and in-boundedness. */
  lemma MirrorGmClosedIff(gm: LG.GroupMap, n: nat)
    requires TRM.GmInBounds(gm, n)
    ensures M.ClosedGm(TRM.MirrorGm(gm, n)) <==> M.ClosedGm(gm)
    ensures TRM.GmInBounds(TRM.MirrorGm(gm, n), n)
  {
    forall g | g in gm ensures TRM.MirrorGm(gm, n)[g].endIdx.Some? <==> gm[g].endIdx.Some? {}
  }

  // ===========================================================================
  // THE LEMMA: backward body sub-leaf closedness from the forward `ClosedBelow`
  // ===========================================================================

  /** The Backward twin of `M.BodyLeafClosedFromBelow`: the from-`gmR` body leaf
      of a positive LOOKBEHIND gate (lookbehind-only body) is CLOSED, by the
      FORWARD depth-stratification hypothesis `M.ClosedBelow` at the FLIPPED body
      instance, transported through the flip mirror. */
  lemma {:isolate_assertions} BackBodyLeafClosedFromBelow(
      rer: LW.RegExpRecord, lk: L.Lookaround, r1: L.Regex,
      tlk: LT.Tree, inp: LC.Input, gmR: LG.GroupMap, subR0: LT.Leaf, D: nat)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Backward
    requires EL.PikeLkRegexRec(r1) && SD.GroupOkLB(r1)
    requires tlk == FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, WP.Backward)
    requires LT.TreeRes(tlk, gmR, inp, WP.Backward) == Some(subR0)
    requires forall g :: g in gmR ==> gmR[g].endIdx.Some?
    requires M.NoDupSeq(L.DefGroups(r1))
    requires TRM.GmInBounds(gmR, |inp.pref| + |inp.next|)
    requires D > 0 && M.NestDepthL(r1) <= D - 1
    requires M.ClosedBelow(rer, D)
    ensures M.ClosedGm(subR0.1)
  {
    var n: nat := |inp.pref| + |inp.next|;
    var inpF := SD.SwapInput(inp);
    assert |inpF.pref| + |inpF.next| == n;
    var rF := FM.FlipRevL(r1);
    var actsB := [LS.Areg(r1)];
    var actsF := [LS.Areg(rF)];
    assert FM.FlipRevActs(actsB) == actsF;
    var tF := FU.ComputeTr(rer, actsF, inpF, LG.Empty, WP.Forward);

    // ---- F1: the flipped forward tree is related; the backward tree is close-disciplined ----
    assert FM.GroupOkLBActs(actsB);
    FM.ComputeTrReverseF(rer, actsB, inp, LG.Empty, LG.Empty);
    assert FM.TreeMirrorRelF(tlk, tF);
    assert CD.NoDupG(L.DefGroups(r1));
    FD.ComputeTrCloseDiscF(rer, r1, inp, LG.Empty, WP.Backward);
    assert FM.CloseDiscF(tlk, {});
    assert TRM.OpenSubset(gmR, {});

    // ---- the general-gm fold: rb (from gmR, Backward) mirrors rf (from MirrorGm(gmR), Forward) ----
    var gmF := TRM.MirrorGm(gmR, n);
    MirrorGmClosedIff(gmR, n);
    FM.TreeResMirrorF(tlk, tF, gmR, inp, n, {});
    var rb := LT.TreeRes(tlk, gmR, inp, WP.Backward);
    var rf := LT.TreeRes(tF, gmF, inpF, WP.Forward);
    assert rb == Some(subR0);
    assert rf.Some? && TRM.GmInBounds(subR0.1, n) && rf.value.1 == TRM.MirrorGm(subR0.1, n);

    // ---- the flipped instance is a `ClosedBelow` instance ----
    FlipRevLPikeLkRec(r1);
    assert EL.PikeLkActionsRec(actsF) by {
      assert actsF == actsF + [];
      assert EL.PikeLkActionsRec([]);
      EL.PikeLkActionsRecConsIff(LS.Areg(rF), []);
    }
    var fuel := LFS.ActionsFuel(actsF, inpF, WP.Forward) + 1;
    LFS.FunctionalTerminates(rer, actsF, inpF, LG.Empty, WP.Forward, fuel);
    assert LFS.ComputeTree(rer, actsF, inpF, LG.Empty, WP.Forward, fuel) == Some(tF);
    var b0 := BS.CannotExit;
    assert BS.BoolEncoding(b0, inpF, actsF);
    EL.ComputeBoolTreeLkRec(rer, actsF, inpF, LG.Empty, b0, fuel, tF);
    assert EL.BoolTreeLk(rer, actsF, inpF, b0, tF);
    NestDepthFlipRevL(r1);
    assert M.NestDepthActsLe(actsF, D - 1);
    FlipRevLFwdPos(r1);
    assert M.FwdPosActsL(actsF);
    assert M.ClosedGm(gmF);
    assert M.OpenOf(gmF) == {} by {
      forall g | g in M.OpenOf(gmF) ensures false { assert gmF[g].endIdx.Some?; }
    }
    assert M.OpenOf(gmF) <= M.PendingCloses(actsF);
    assert M.LkClosedInGm(gmF, actsF) by {
      forall g | g in gmF && g in M.LkBodyGroupsActs(actsF) ensures gmF[g].endIdx.Some? { }
    }
    NoDupSeqFlipRevL(r1);
    assert M.OuterLkDisjoint(actsF) by {
      M.OuterDefsActsCons(LS.Areg(rF), []); M.LkBodyGroupsActsCons(LS.Areg(rF), []);
      M.OuterLkFromNoDup(rF);
    }
    assert M.NoDupRegsActs(actsF);
    assert TRM.GmInBounds(gmF, n);
    assert LT.TreeRes(tF, gmF, inpF, WP.Forward) == Some(rf.value);

    // ---- ClosedBelow at the flipped instance, transported back through MirrorGm ----
    assert M.ClosedGm(rf.value.1);
    MirrorGmClosedIff(subR0.1, n);
    assert M.ClosedGm(subR0.1);
  }
}
