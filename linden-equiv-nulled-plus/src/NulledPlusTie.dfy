// §2.5b stage 2, rung B (spec half): the oracle-bit empty path over the annotated
// RegElk regex (`TR.FirstEmptyPathR`, read by `TreeRepRE`'s nulled-exit stamp rule)
// computes the spec path `NP.FirstEmptyPathL` over its translation. Kept in its own
// module so `NulledPlus.dfy`'s verification context stays free of the engine-side
// modules (`AR`/`TR` and their imports) it does not need.
/** Rung B's spec tie: `FirstEmptyPathA` is compositional in the continuation, and
    the oracle-bit path over an annotated RegElk regex equals the spec path over its
    translation under `OracleOkAt` (bits tell the truth) and `LmapOk` (lids resolve). */
module LindenElkNulledPlusTie {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LN = WarblreNumeric
  import LS = Semantics
  import LT = Tree
  import FS = FunctionalSemantics
  import FU = FunctionalUtils
  import R = RegElkRegex
  import T = LindenElkTranslate
  import AR = LindenElkActionsRep
  import TR = LindenElkTreeRep
  import LL = LindenElkLookLeaves
  import NP = LindenElkNulledPlus

  // ===========================================================================
  // Rung B (spec half): `FirstEmptyPathA` is COMPOSITIONAL in the continuation,
  // and the oracle-bit twin `TR.FirstEmptyPathR` over the annotated RegElk
  // regex computes the same path as `FirstEmptyPathL` over its translation
  // (under `OracleOkAt` for the lookaround bits and `LmapOk` for the lids).
  // ===========================================================================

  /** Sequential composition of two optional paths (`None` absorbs). */
  ghost function CompPath(a: Option<seq<LG.GroupAction>>, b: Option<seq<LG.GroupAction>>): Option<seq<LG.GroupAction>> {
    match a
    case None => None
    case Some(p) => (match b case None => None case Some(q) => Some(p + q))
  }

  lemma CompPathAssoc(a: Option<seq<LG.GroupAction>>, b: Option<seq<LG.GroupAction>>, c: Option<seq<LG.GroupAction>>)
    ensures CompPath(CompPath(a, b), c) == CompPath(a, CompPath(b, c))
  {
    if a.Some? && b.Some? && c.Some? {
      assert (a.value + b.value) + c.value == a.value + (b.value + c.value);
    }
  }

  /** Prefixing one action onto an optional path (`None` absorbs). */
  ghost function PrePath(g: LG.GroupAction, a: Option<seq<LG.GroupAction>>): Option<seq<LG.GroupAction>> {
    match a case None => None case Some(p) => Some([g] + p)
  }

  lemma PrePathComp(g: LG.GroupAction, a: Option<seq<LG.GroupAction>>, b: Option<seq<LG.GroupAction>>)
    ensures CompPath(PrePath(g, a), b) == PrePath(g, CompPath(a, b))
  {
    if a.Some? && b.Some? {
      assert ([g] + a.value) + b.value == [g] + (a.value + b.value);
    }
  }

  /** A structural size on Linden regexes (the induction measure below needs a
      quantifier's forced unrolling `Q(min-1)` to be "smaller": same size,
      smaller `min`). */
  ghost function RSizeL(r: L.Regex): nat
    decreases r
  {
    match r
    case Epsilon => 1
    case Character(_) => 1
    case Disjunction(r1, r2) => 1 + RSizeL(r1) + RSizeL(r2)
    case Sequence(r1, r2) => 1 + RSizeL(r1) + RSizeL(r2)
    case Quantified(_, _, _, r1) => 1 + RSizeL(r1)
    case Group(_, r1) => 1 + RSizeL(r1)
    case AnchorR(_) => 1
    case LookaroundR(_, r1) => 1 + RSizeL(r1)
    case Backreference(_) => 1
  }

  ghost function MinOfL(r: L.Regex): nat {
    match r case Quantified(_, min, _, _) => min case _ => 0
  }

  /** The first empty path of `[Areg(r)] + cont` is the first empty path of
      `r` alone followed by the continuation's (both must exist). Holds
      because, without backreferences, whether the continuation has an empty
      path at `inp` does not depend on which empty path `r` took. */
  lemma FirstEmptyPathAComp(rer: LW.RegExpRecord, r: L.Regex, cont: LS.Actions, inp: LC.Input)
    ensures NP.FirstEmptyPathA(rer, [LS.Areg(r)] + cont, inp) == CompPath(NP.FirstEmptyPathL(rer, r, inp), NP.FirstEmptyPathA(rer, cont, inp))
    decreases RSizeL(r), MinOfL(r)
  {
    var acts := [LS.Areg(r)] + cont;
    assert acts[0] == LS.Areg(r) && acts[1..] == cont;
    var solo := [LS.Areg(r)];
    assert solo[0] == LS.Areg(r) && solo[1..] == [];
    assert NP.FirstEmptyPathA(rer, [], inp) == Some([]);
    var q := NP.FirstEmptyPathA(rer, cont, inp);
    match r
    case Epsilon =>
      assert NP.FirstEmptyPathL(rer, r, inp) == Some([]);
      assert NP.FirstEmptyPathA(rer, acts, inp) == q;
      if q.Some? { assert [] + q.value == q.value; }
    case Character(_) =>
    case Disjunction(r1, r2) =>
      assert [LS.Areg(r1)] + [] == [LS.Areg(r1)] && [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      FirstEmptyPathAComp(rer, r1, cont, inp);
      FirstEmptyPathAComp(rer, r2, cont, inp);
      var p1 := NP.FirstEmptyPathL(rer, r1, inp);
      var p2 := NP.FirstEmptyPathL(rer, r2, inp);
      assert NP.FirstEmptyPathL(rer, r, inp) == (match p1 case Some(p) => Some(p) case None => p2);
      assert NP.FirstEmptyPathA(rer, acts, inp)
          == (match NP.FirstEmptyPathA(rer, [LS.Areg(r1)] + cont, inp)
              case Some(p) => Some(p)
              case None => NP.FirstEmptyPathA(rer, [LS.Areg(r2)] + cont, inp));
    case Sequence(r1, r2) =>
      assert [LS.Areg(r1), LS.Areg(r2)] + cont == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
      assert [LS.Areg(r1), LS.Areg(r2)] + [] == [LS.Areg(r1)] + [LS.Areg(r2)];
      assert [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      FirstEmptyPathAComp(rer, r1, [LS.Areg(r2)] + cont, inp);
      FirstEmptyPathAComp(rer, r2, cont, inp);
      FirstEmptyPathAComp(rer, r1, [LS.Areg(r2)], inp);
      var p1 := NP.FirstEmptyPathL(rer, r1, inp);
      var p2 := NP.FirstEmptyPathL(rer, r2, inp);
      assert NP.FirstEmptyPathA(rer, acts, inp) == NP.FirstEmptyPathA(rer, [LS.Areg(r1)] + ([LS.Areg(r2)] + cont), inp);
      assert NP.FirstEmptyPathA(rer, acts, inp) == CompPath(p1, CompPath(p2, q));
      assert NP.FirstEmptyPathL(rer, r, inp) == NP.FirstEmptyPathA(rer, solo, inp);
      assert NP.FirstEmptyPathA(rer, solo, inp) == NP.FirstEmptyPathA(rer, [LS.Areg(r1), LS.Areg(r2)] + [], inp);
      assert NP.FirstEmptyPathL(rer, r, inp) == NP.FirstEmptyPathA(rer, [LS.Areg(r1)] + [LS.Areg(r2)], inp);
      assert NP.FirstEmptyPathA(rer, [LS.Areg(r2)], inp) == p2;
      assert NP.FirstEmptyPathL(rer, r, inp) == CompPath(p1, p2);
      CompPathAssoc(p1, p2, q);
    case Quantified(greedy, min, delta, r1) =>
      var gidl := L.DefGroups(r1);
      if min > 0 {
        var qn := L.Quantified(greedy, min - 1, delta, r1);
        assert RSizeL(qn) == RSizeL(r) && MinOfL(qn) < MinOfL(r);
        assert [LS.Areg(r1), LS.Areg(qn)] + cont == [LS.Areg(r1)] + ([LS.Areg(qn)] + cont);
        assert [LS.Areg(r1), LS.Areg(qn)] + [] == [LS.Areg(r1)] + [LS.Areg(qn)];
        assert [LS.Areg(qn)] + [] == [LS.Areg(qn)];
        FirstEmptyPathAComp(rer, r1, [LS.Areg(qn)] + cont, inp);
        FirstEmptyPathAComp(rer, qn, cont, inp);
        FirstEmptyPathAComp(rer, r1, [LS.Areg(qn)], inp);
        var p1 := NP.FirstEmptyPathL(rer, r1, inp);
        var pn := NP.FirstEmptyPathL(rer, qn, inp);
        assert NP.FirstEmptyPathA(rer, acts, inp) == PrePath(LG.Reset(gidl), CompPath(p1, CompPath(pn, q)));
        assert NP.FirstEmptyPathL(rer, r, inp) == PrePath(LG.Reset(gidl), CompPath(p1, pn));
        CompPathAssoc(p1, pn, q);
        PrePathComp(LG.Reset(gidl), CompPath(p1, pn), q);
      } else {
        assert NP.FirstEmptyPathL(rer, r, inp) == Some([]);
        assert NP.FirstEmptyPathA(rer, acts, inp) == q;
        if q.Some? { assert [] + q.value == q.value; }
      }
    case Group(gid, r1) =>
      assert [LS.Areg(r1), LS.Aclose(gid)] + cont == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
      assert [LS.Areg(r1), LS.Aclose(gid)] + [] == [LS.Areg(r1)] + [LS.Aclose(gid)];
      assert ([LS.Aclose(gid)] + cont)[0] == LS.Aclose(gid) && ([LS.Aclose(gid)] + cont)[1..] == cont;
      assert [LS.Aclose(gid)][0] == LS.Aclose(gid) && [LS.Aclose(gid)][1..] == [];
      assert NP.FirstEmptyPathA(rer, [LS.Aclose(gid)] + cont, inp) == PrePath(LG.Close(gid), q);
      assert [LG.Close(gid)] + [] == [LG.Close(gid)];
      assert NP.FirstEmptyPathA(rer, [LS.Aclose(gid)], inp) == Some([LG.Close(gid)]);
      FirstEmptyPathAComp(rer, r1, [LS.Aclose(gid)] + cont, inp);
      FirstEmptyPathAComp(rer, r1, [LS.Aclose(gid)], inp);
      var p1 := NP.FirstEmptyPathL(rer, r1, inp);
      assert NP.FirstEmptyPathA(rer, acts, inp) == PrePath(LG.Open(gid), CompPath(p1, PrePath(LG.Close(gid), q)));
      assert NP.FirstEmptyPathL(rer, r, inp) == PrePath(LG.Open(gid), CompPath(p1, Some([LG.Close(gid)])));
      assert CompPath(Some([LG.Close(gid)]), q) == PrePath(LG.Close(gid), q);
      CompPathAssoc(p1, Some([LG.Close(gid)]), q);
      PrePathComp(LG.Open(gid), CompPath(p1, Some([LG.Close(gid)])), q);
    case AnchorR(a) =>
      if LS.AnchorSatisfied(rer, a, inp) {
        assert NP.FirstEmptyPathL(rer, r, inp) == Some([]);
        assert NP.FirstEmptyPathA(rer, acts, inp) == q;
        if q.Some? { assert [] + q.value == q.value; }
      }
    case LookaroundR(lk, r1) =>
      if NP.LkVerdictL(rer, lk, r1, inp) {
        assert NP.FirstEmptyPathL(rer, r, inp) == Some([]);
        assert NP.FirstEmptyPathA(rer, acts, inp) == q;
        if q.Some? { assert [] + q.value == q.value; }
      }
    case Backreference(_) =>
  }

  /** The first empty path of a forced quantifier: `min` copies of
      `Reset(gidl)` + the body's path (the spec unrolls `[Areg(r1), Areg(Q(min-1))]`
      at the same position each time); a free quantifier's is the skip. */
  lemma FirstEmptyPathLQuant(rer: LW.RegExpRecord, greedy: bool, min: nat, delta: LN.NoI, r1: L.Regex, inp: LC.Input)
    ensures NP.FirstEmptyPathL(rer, L.Quantified(greedy, min, delta, r1), inp)
         == (if min == 0 then Some([])
             else match NP.FirstEmptyPathL(rer, r1, inp)
                  case None => None
                  case Some(p1) => Some(TR.RepeatPath(min, [LG.Reset(L.DefGroups(r1))] + p1)))
    decreases min
  {
    var r := L.Quantified(greedy, min, delta, r1);
    var solo := [LS.Areg(r)];
    assert solo[0] == LS.Areg(r) && solo[1..] == [];
    assert NP.FirstEmptyPathA(rer, [], inp) == Some([]);
    if min == 0 {
      assert NP.FirstEmptyPathL(rer, r, inp) == NP.FirstEmptyPathA(rer, [], inp);
    }
    if min > 0 {
      var gidl := L.DefGroups(r1);
      var qn := L.Quantified(greedy, min - 1, delta, r1);
      assert [LS.Areg(r1), LS.Areg(qn)] + [] == [LS.Areg(r1)] + [LS.Areg(qn)];
      assert [LS.Areg(qn)] + [] == [LS.Areg(qn)];
      assert NP.FirstEmptyPathL(rer, r, inp) == NP.FirstEmptyPathA(rer, solo, inp);
      assert NP.FirstEmptyPathA(rer, solo, inp)
          == PrePath(LG.Reset(gidl), NP.FirstEmptyPathA(rer, [LS.Areg(r1), LS.Areg(qn)] + [], inp));
      assert NP.FirstEmptyPathL(rer, r, inp)
          == PrePath(LG.Reset(gidl), NP.FirstEmptyPathA(rer, [LS.Areg(r1)] + [LS.Areg(qn)], inp));
      FirstEmptyPathAComp(rer, r1, [LS.Areg(qn)], inp);
      FirstEmptyPathLQuant(rer, greedy, min - 1, delta, r1, inp);
      var p1 := NP.FirstEmptyPathL(rer, r1, inp);
      var pn := NP.FirstEmptyPathL(rer, qn, inp);
      assert NP.FirstEmptyPathA(rer, [LS.Areg(qn)], inp) == pn;
      assert NP.FirstEmptyPathL(rer, r, inp) == PrePath(LG.Reset(gidl), CompPath(p1, pn));
      if p1.Some? {
        var unit := [LG.Reset(gidl)] + p1.value;
        assert TR.RepeatPath(min, unit) == unit + TR.RepeatPath(min - 1, unit);
        if min - 1 == 0 {
          assert pn == Some([]);
          assert TR.RepeatPath(0, unit) == [];
          assert [LG.Reset(gidl)] + (p1.value + []) == unit + [];
        } else {
          assert pn == Some(TR.RepeatPath(min - 1, unit));
          assert [LG.Reset(gidl)] + (p1.value + TR.RepeatPath(min - 1, unit)) == unit + TR.RepeatPath(min - 1, unit);
        }
        assert NP.FirstEmptyPathL(rer, r, inp) == Some(TR.RepeatPath(min, unit));
      }
    }
  }

  /** `LkVerdictL` is the oracle bit's meaning: for a positive lookaround the
      body's walk succeeds, for a negative one it fails. */
  lemma LkVerdictLBit(rer: LW.RegExpRecord, lk: L.Lookaround, r1: L.Regex, inp: LC.Input)
    ensures var ok := LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk)), LG.Empty, inp, L.LkDir(lk)).Some?;
            NP.LkVerdictL(rer, lk, r1, inp) <==> (if L.Positivity(lk) then ok else !ok)
  {}

  /** THE rung-B tie: the oracle-bit path over the annotated RegElk regex is
      the spec path over its translation, whenever the bits tell the truth
      (`OracleOkAt`) about the lookarounds `LmapOk` registers. */
  lemma FirstEmptyPathRL(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires !rer.multiline
    requires T.TransWf(re) && AR.LmapOk(re, qm)
    requires LL.OracleOkAt(rer, qm, inp)
    ensures TR.FirstEmptyPathR(qm, re, inp) == NP.FirstEmptyPathL(rer, T.Translate(re), inp)
    decreases re
  {
    var tr := T.Translate(re);
    var solo := [LS.Areg(tr)];
    assert solo[0] == LS.Areg(tr) && solo[1..] == [];
    assert NP.FirstEmptyPathA(rer, [], inp) == Some([]);
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(a) =>
      TR.AnchorAgreeInput(rer, a, inp);
    case Re_alt(r1, r2) =>
      FirstEmptyPathRL(rer, qm, r1, inp);
      FirstEmptyPathRL(rer, qm, r2, inp);
      var t1 := T.Translate(r1);
      var t2 := T.Translate(r2);
      assert [LS.Areg(t1)] + [] == [LS.Areg(t1)] && [LS.Areg(t2)] + [] == [LS.Areg(t2)];
      assert NP.FirstEmptyPathL(rer, tr, inp)
          == (match NP.FirstEmptyPathL(rer, t1, inp) case Some(p) => Some(p) case None => NP.FirstEmptyPathL(rer, t2, inp));
    case Re_con(r1, r2) =>
      FirstEmptyPathRL(rer, qm, r1, inp);
      FirstEmptyPathRL(rer, qm, r2, inp);
      var t1 := T.Translate(r1);
      var t2 := T.Translate(r2);
      assert [LS.Areg(t1), LS.Areg(t2)] + [] == [LS.Areg(t1)] + [LS.Areg(t2)];
      assert [LS.Areg(t2)] + [] == [LS.Areg(t2)];
      FirstEmptyPathAComp(rer, t1, [LS.Areg(t2)], inp);
      assert NP.FirstEmptyPathL(rer, tr, inp) == CompPath(NP.FirstEmptyPathL(rer, t1, inp), NP.FirstEmptyPathL(rer, t2, inp));
    case Re_quant(nul, qid, q, r1) =>
      FirstEmptyPathRL(rer, qm, r1, inp);
      var t1 := T.Translate(r1);
      assert tr == L.Quantified(q.greedy, q.min as nat, T.TrDelta(q), t1);
      FirstEmptyPathLQuant(rer, q.greedy, q.min as nat, T.TrDelta(q), t1, inp);
    case Re_capture(cid, r1) =>
      FirstEmptyPathRL(rer, qm, r1, inp);
      var t1 := T.Translate(r1);
      var gid: nat := cid as nat;
      assert tr == L.Group(gid, t1);
      assert [LS.Areg(t1), LS.Aclose(gid)] + [] == [LS.Areg(t1)] + [LS.Aclose(gid)];
      assert [LS.Aclose(gid)][0] == LS.Aclose(gid) && [LS.Aclose(gid)][1..] == [];
      assert [LG.Close(gid)] + [] == [LG.Close(gid)];
      assert NP.FirstEmptyPathA(rer, [LS.Aclose(gid)], inp) == Some([LG.Close(gid)]);
      FirstEmptyPathAComp(rer, t1, [LS.Aclose(gid)], inp);
      var p1 := NP.FirstEmptyPathL(rer, t1, inp);
      assert NP.FirstEmptyPathL(rer, tr, inp) == PrePath(LG.Open(gid), CompPath(p1, Some([LG.Close(gid)])));
      if p1.Some? {
        assert [LG.Open(gid)] + (p1.value + [LG.Close(gid)]) == [LG.Open(gid)] + p1.value + [LG.Close(gid)];
      }
    case Re_lookaround(lid, lk, r1) =>
      var lkL := T.TrLookaround(lk);
      var t1 := T.Translate(r1);
      assert tr == L.LookaroundR(lkL, t1);
      assert lid in qm.looks && qm.looks[lid] == (lkL, t1);
      LL.OracleOkAtGet(rer, qm, inp, lid, lkL, t1);
      LkVerdictLBit(rer, lkL, t1, inp);
      assert AR.PositiveL(lkL) == L.Positivity(lkL);
  }
}
