// Phase 4b (layer 4) / Phase +C4: the central construction â€” from the spec
// BoolTree of a represented action list to the CHECKED TreeRepRE tree.
//
// PIVOT (plus campaign): the lemma is value-returning. Given the spec walk
// (BoolTree, which never inserts a check after the do-while's last forced
// iteration) it CONSTRUCTS the checked tree tstar that the engine represents
// (TreeRepRE at the same pc/flag) and proves the two agree on leaves. The
// checking happens at exactly two seams:
//  - the do-while entry (min == 1, Inf): BoolCheckInsert plants the missing
//    Acheck after the guaranteed last forced body â€” legal because the body is
//    NonNullable (ConsumesBeforeAreg);
//  - the backward fork (the do-while's decision point): the zero-width Acheck
//    dissolves into the fork and is consumed together with the Choice by
//    tr_plus (companion lemma AtBackForkTreeRep), with BoolFlagLift raising
//    the iteration walk to CanExit â€” the engine never clears exit_allowed
//    through the back edge, so the represented iteration runs at true.
// The WalkOk carrier excludes the one adversarial config where the ensures
// would be false (a bare loop-view star at CannotExit); its guard bit g runs
// in lockstep with EaOf(b) through every case.
//
// Measure: PSize (Progress-blind â€” check insertion is PSize-preserving),
// then MsizeA = 2*ActionsRegexSize + |acts| (expansions net-decrease it,
// Acheck/Progress-consuming steps tie PSize and drop it), then fuel, then a
// tag ordering the mutual pair (the bare loop-view delegation is a tie on
// everything else).

/** Phase 4b layer 4 â€” the checked-tree construction: a `BoolTree` of a
    `PikeActions`/`PikeRegex`-restricted action list yields a leaves-agreeing
    CHECKED tree that is `TreeRepRE`-represented at the corresponding pc. */
module LindenElkActionsTreeRep {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LN = WarblreNumeric
  import LT = Tree
  import LS = Semantics
  import BS = BooleanSemantics
  import PS = PikeSubset
  import FS = FunctionalSemantics
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import T = LindenElkTranslate
  import NR = LindenElkNfaRep
  import AR = LindenElkActionsRep
  import TR = LindenElkTreeRep
  import CE = LindenElkCheckErase
  import WO = LindenElkWalkOk
  import FU = FunctionalUtils
  import LOr = Oracle
  import EL = LindenElkEntryLk
  import LL = LindenElkLookLeaves
  import NUL = LindenElkNullable
  import NP = LindenElkNulledPlus
  import NT = LindenElkNulledPlusTie
  import NB = LindenElkNulledPlusBool

  // RegElk's exit_allowed bool for a Linden LoopBool.
  /** RegElk's `exit_allowed` bit for a Linden `LoopBool`: `true` iff the
      thread `CanExit` its current loop iteration. */
  function EaOf(b: BS.LoopBool): bool { b.CanExit? }

  // Translated fragment regexes are exactly Linden's pike subset.
  /** Every RegElk regex in the star fragment (`StarFragmentRE`, well-formed
      under `TransWf`) translates to a regex satisfying Linden's `PikeRegex`
      restriction â€” so the tree-simulation argument can assume the pike subset. */
  lemma TranslateFragmentPike(re: R.regex)
    requires NR.PlusFragmentRE(re) && T.TransWf(re)
    ensures PS.PikeRegex(T.Translate(re))
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_alt(r1, r2) =>
      TranslateFragmentPike(r1);
      TranslateFragmentPike(r2);
    case Re_con(r1, r2) =>
      TranslateFragmentPike(r1);
      TranslateFragmentPike(r2);
    case Re_quant(nul, qid, q, r1) =>
      // PikeRegex admits any min/delta since the model generalization
      TranslateFragmentPike(r1);
    case Re_capture(cid, r1) =>
      TranslateFragmentPike(r1);
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
  }

  // ===========================================================================
  // Fuel plumbing for ActionsRepL (ports of ActionsRepFuel / ToFuel / FromFuel)
  // ===========================================================================

  /** Fuelled version of `ActionsRepL` (Linden's action-stack representation
      predicate): same three cases (empty stack at `Accept`, one action stepped
      then the rest, or a `Jmp` stutter) but structured so a lemma can recurse
      on decreasing fuel `n` instead of on the representation predicate itself. */
  ghost predicate ActionsRepFuelL(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, c: RB.code, pc: nat, n: nat)
    decreases n
  {
    n > 0 &&
    ((|acts| == 0 && NR.GetPcRE(c, pc) == Some(RB.Accept))
     || (|acts| > 0 && exists pcmid: nat ::
           AR.ActionRepL(rer, qm, acts[0], c, pc, pcmid) && ActionsRepFuelL(rer, qm, acts[1..], c, pcmid, n - 1))
     || (exists pcstart: nat ::
           NR.GetPcRE(c, pc) == Some(RB.Jmp(pcstart)) && ActionsRepFuelL(rer, qm, acts, c, pcstart, n - 1)))
  }

  /** Every `ActionsRepL` derivation has some finite fuel bound witnessing it
      via `ActionsRepFuelL` â€” turns the representation predicate into
      something a fuel-indexed induction can consume. */
  least lemma ActionsRepLToFuel(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, c: RB.code, pc: nat)
    requires AR.ActionsRepL(rer, qm, acts, c, pc)
    ensures exists n: nat :: ActionsRepFuelL(rer, qm, acts, c, pc, n)
  {
    if |acts| == 0 && NR.GetPcRE(c, pc) == Some(RB.Accept) {
      assert ActionsRepFuelL(rer, qm, acts, c, pc, 1);
    } else if |acts| > 0 && exists pcmid: nat :: AR.ActionRepL(rer, qm, acts[0], c, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], c, pcmid) {
      var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], c, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], c, pcmid);
      ActionsRepLToFuel(rer, qm, acts[1..], c, pcmid);
      var np: nat :| ActionsRepFuelL(rer, qm, acts[1..], c, pcmid, np);
      assert ActionsRepFuelL(rer, qm, acts, c, pc, np + 1);
    } else {
      var pcstart: nat :| NR.GetPcRE(c, pc) == Some(RB.Jmp(pcstart)) && AR.ActionsRepL(rer, qm, acts, c, pcstart);
      ActionsRepLToFuel(rer, qm, acts, c, pcstart);
      var np: nat :| ActionsRepFuelL(rer, qm, acts, c, pcstart, np);
      assert ActionsRepFuelL(rer, qm, acts, c, pc, np + 1);
    }
  }

  /** The fuelled predicate implies the real one â€” `ActionsRepFuelL` is sound
      for `ActionsRepL`, the inverse direction of `ActionsRepLToFuel`. */
  lemma FuelToActionsRepL(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, c: RB.code, pc: nat, n: nat)
    requires ActionsRepFuelL(rer, qm, acts, c, pc, n)
    ensures AR.ActionsRepL(rer, qm, acts, c, pc)
    decreases n
  {
    if |acts| == 0 && NR.GetPcRE(c, pc) == Some(RB.Accept) {
    } else if |acts| > 0 && exists pcmid: nat :: AR.ActionRepL(rer, qm, acts[0], c, pc, pcmid) && ActionsRepFuelL(rer, qm, acts[1..], c, pcmid, n - 1) {
      var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], c, pc, pcmid) && ActionsRepFuelL(rer, qm, acts[1..], c, pcmid, n - 1);
      FuelToActionsRepL(rer, qm, acts[1..], c, pcmid, n - 1);
    } else {
      var pcstart: nat :| NR.GetPcRE(c, pc) == Some(RB.Jmp(pcstart)) && ActionsRepFuelL(rer, qm, acts, c, pcstart, n - 1);
      FuelToActionsRepL(rer, qm, acts, c, pcstart, n - 1);
    }
  }

  // ===========================================================================
  // The construction (returns the checked tree)
  // ===========================================================================

  /** The list component of the construction's measure: expansions replace a
      regex node by its parts (`ActionsRegexSize` drops by at least one, the
      length grows by at most one), and `Acheck`/`Aclose` peels drop the
      length with the size unchanged â€” both strictly decrease this. */
  function MsizeA(acts: LS.Actions): nat {
    2 * LS.ActionsRegexSize(acts) + |acts|
  }

  /** Fuel-indexed core of the construction: from the action-stack fuel bound,
      the walk guard, and `acts`'s spec `BoolTree` `t`, CONSTRUCTS the checked
      tree `tstar` â€” `TreeRepRE`-represented at `pc` with the walk's flag, and
      leaves-agreeing with `t`. One case per `Action`/`Regex` shape; the
      do-while cases plant/dissolve the progress check as described in the
      file header. */
  // {:isolate_assertions} is LOAD-BEARING here: as one VC this lemma times out
  // past 600s (measured). It is also the package's dominant cost â€” ~4300 tiny
  // batches, ~3800 cpu-seconds â€” and the way to fix that is to decompose the
  // LEMMA (its per-shape cases into standalone lemmas with small contexts),
  // not to split the file: this single lemma owns ~98% of the file's time and
  // is mutually recursive with AtBackForkTreeRep, so no file split can
  // separate them.
  /** (2026-08-29 E3) the `Quantified` arm of `ActionsTreeRepFRE`, min > 0 — extracted from a 350-line
      case so each branch is its own VC (the parent no longer needs `{:isolate_assertions}`). */
  /** (§2.5b stage 2) the CIN-GREEDY arm of `ATR_QuantMin`: `min - 1` forced copies,
      then the stamped end-fork loop. Extracted so the parent stays within its
      batch budget; sectioned per E3. */
  lemma ATR_QuantCin(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, greedy: bool, min: nat, delta: LN.NoI, r1: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTree(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActions(cont)
    requires EL.PikeLkRegex(L.Quantified(greedy, min, delta, r1))
    requires min > 0 && delta == LN.Inf && !NUL.NonNullableL(r1) && greedy
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0   // below `ATR_QuantMin`'s `1`
  {
    // (§2.5b) the recursive nullability predicates' definitional axioms send z3 4.14 into
    // a matching loop (as in the LiftSimCore giants): every use here is opaque, so hide them.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL, AR.NfaRepStarCinL, EL.PikeLkRegexRec, MsizeA;   // every recursive call below decreases on PSize alone
    assert acts == [acts[0]] + cont;
    EL.PikeLkActionsConsIff(acts[0], cont);
    var gidl := L.DefGroups(r1);
          // §2.5b CIN-GREEDY: `min - 1` forced copies, then the stamped end-fork
          // loop at the head fork `em`. A forced copy peels like the do-while's;
          // at `min == 1` the head IS the fork: its loop arm is the star's
          // iteration (BeginLoop/EndLoop are the spec's `Acheck`), its skip arm
          // is the nulled-exit stamp = the VIRTUAL CHAIN of the body's first
          // empty path over the continuation (`tr_stamp`), and rung A's
          // priority theorem (`NB.CinPlusPriorityBool`) relates the two shapes.
          var em, e1x := AR.NfaRepLCinInv(rer, qm, greedy, min, r1, code, pc, pcmid);
          var qidC: int :| NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qidC, false))
            && NR.GetPcRE(code, e1x + 2) == Some(RB.SetQuantToClock(qidC, true))
            && qidC in qm.quants && qm.quants[qidC] == gidl
            && AR.StampBodyOk(qm, qidC, r1);
          AR.NfaRepIncrL(rer, qm, r1, code, em + 3, e1x);
          assert {:split_here} true;   // (E3) section: the forced copy
          if min > 1 {
            var quant1 := L.Quantified(greedy, min - 1, LN.Inf, r1);
            var eb: nat :| (exists qid2: int ::
                  NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid2, false))
                  && qid2 in qm.quants && qm.quants[qid2] == gidl)
              && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
              && AR.NfaRepMinL(rer, qm, min - 2, r1, code, eb, em);
            AR.NfaRepLCinIntro(rer, qm, greedy, min - 1, r1, code, eb, em, e1x, pcmid, qidC);
            assert AR.NfaRepL(rer, qm, quant1, code, eb, pcmid);
            match t {
              case GroupActionT(g, tc) =>
                assert g == LG.Reset(gidl);
                EL.PikeLkActionsConsIff(LS.Areg(quant1), cont);
                EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
                FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                assert AR.ActionRepL(rer, qm, LS.Areg(quant1), code, eb, pcmid);
                var lq1 := [LS.Areg(quant1)] + cont;
                assert lq1[0] == LS.Areg(quant1) && lq1[1..] == cont;
                assert AR.ActionsRepL(rer, qm, lq1, code, eb);
                var ia := [LS.Areg(r1)] + lq1;
                assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, eb);
                assert ia[0] == LS.Areg(r1) && ia[1..] == lq1;
                assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
                assert ia == [LS.Areg(r1), LS.Areg(quant1)] + cont;
                ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
                var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
                WO.WalkOkQuantForced(acts, code, pc, EaOf(b), greedy, min, delta, r1);
                assert CE.PSize(tc) < CE.PSize(t);
                assert LL.LkActsInS(ia, S) by {
                  LL.LkActsInSTail(acts, S);
                  assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(quant1, S);
                  LL.LkActsInSCons(LS.Areg(quant1), cont, S);
                  LL.LkActsInSCons(LS.Areg(r1), [LS.Areg(quant1)] + cont, S);
                }
                assert NB.EncOk(ia, inp, b) by {
                  var parts := [LS.Areg(r1), LS.Areg(quant1)];
                  assert parts + cont == ia;
                  if NUL.NonNullableL(acts[0].r) { reveal NUL.NonNullableL; assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
                  NB.EncOkExpand(acts, parts, inp, b);
                }
                var sub := ActionsTreeRepFRE(rer, qm, ia, code, pc + 1, inp, b, tc, ni, S);
                tstar := LT.GroupActionT(g, sub);
                NP.RACongGroupOutside(g, sub, tc, inp, S);
              case _ =>
            }
          } else {
            // min == 1: THE CIN HEAD FORK at pc == em
            assert {:split_here} true;   // (E3) section: the head fork
            assert em == pc;
            assert greedy && delta == LN.Inf;
            var q0 := L.Quantified(greedy, 0, LN.Inf, r1);
            assert acts == [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont;
            match t {
              case GroupActionT(g, tc) =>
                assert g == LG.Reset(gidl);
                assert EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Areg(q0)] + cont, inp, b, tc);
                EL.PikeLkActionsConsIff(LS.Areg(q0), cont);
                EL.PikeLkActionsConsIff(LS.Acheck(inp), [LS.Areg(q0)] + cont);
                EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
                var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
                assert ia == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
                assert EL.PikeLkActions(ia) && EL.PikeLkActions(cont);
                EL.PikeLkActionsEmbedsRec(ia); EL.PikeLkActionsEmbedsRec(cont); EL.PikeLkActionsEmbedsRec(acts);
                // the sub-stacks' confinement and encoding
                assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
                assert LL.LkBodiesInS(r1, S);
                assert LL.LkActsInS(ia, S) by {
                  assert LL.LkBodiesInS(q0, S);
                  LL.LkActsInSCons(LS.Areg(q0), cont, S);
                  LL.LkActsInSCons(LS.Acheck(inp), [LS.Areg(q0)] + cont, S);
                  LL.LkActsInSCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont), S);
                }
                assert NB.EncOk(cont, inp, b) by {
                  assert !NUL.NonNullableL(acts[0].r) by { reveal NUL.NonNullableL; }
                  NB.EncOkTailReg(acts, inp, b);
                }
                assert NB.EncOk(ia, inp, BS.CannotExit) by {
                  NB.EncodableTail(acts, inp, b);
                  NB.EncOkIter(r1, q0, cont, inp);
                }
                // the spec trees of the iteration and of the continuation live
                // INSIDE `tc` (at the body's first empty leaf), so both are
                // PSize-smaller than `t`
                assert NP.FirstEmptyPathL(rer, r1, inp).Some? by {
                  assert NP.FirstEmptyPathA(rer, [], inp) == Some([]);
                  NP.CINullableEmptyPathA(rer, r1, [], inp);
                  assert [LS.Areg(r1)] + [] == [LS.Areg(r1)];
                }
                assert [LS.Areg(r1), LS.Areg(q0)] + cont == [LS.Areg(r1)] + ([LS.Areg(q0)] + cont);
                var tcont0 := NB.BoolTreeLkEmptyPathSub(rer, r1, [LS.Areg(q0)] + cont, inp, b, tc);
                assert FS.NoiPred(LN.Inf) == LN.Inf;
                match tcont0 {
                  case Choice(ta, tb) =>
                    var ti: LT.Tree := *;
                    match ta {
                      case GroupActionT(g2, ti2) =>
                        assert g2 == LG.Reset(gidl);
                        ti := ti2;
                      case _ => assert false;
                    }
                    var tcont := tb;
                    assert EL.BoolTreeLk(rer, ia, inp, BS.CannotExit, ti);
                    assert EL.BoolTreeLk(rer, cont, inp, b, tcont);
                    assert CE.PSize(ti) < CE.PSize(t) && CE.PSize(tcont) < CE.PSize(t);
                    assert CE.LkConfinedTree(tc, S);
                    assert CE.LkConfinedTree(tcont0, S);
                    assert tcont0 == LT.Choice(ta, tb);
                    assert CE.LkConfinedTree(ta, S) && CE.LkConfinedTree(tb, S);
                    assert ta.GroupActionT? && ti == ta.t;
                    assert CE.LkConfinedTree(ti, S) && CE.LkConfinedTree(tcont, S);
                    assert {:split_here} true;   // (E3) section: representation
                    // representation of the two lists: the loop body at em + 3
                    // (EndLoop at e1x, the CIN loop view of the star at e1x + 1),
                    // the continuation at pcmid == e1x + 3
                    FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                    AR.NfaRepLStarCinIntro(rer, qm, r1, code, em, e1x, qidC);
                    assert AR.ActionRepL(rer, qm, LS.Areg(q0), code, e1x + 1, pcmid);
                    var lq := [LS.Areg(q0)] + cont;
                    assert lq[0] == LS.Areg(q0) && lq[1..] == cont;
                    assert AR.ActionsRepL(rer, qm, lq, code, e1x + 1);
                    var lc := [LS.Acheck(inp)] + lq;
                    assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1x, e1x + 1);
                    assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
                    assert AR.ActionsRepL(rer, qm, lc, code, e1x);
                    assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, em + 3, e1x);
                    assert ia[0] == LS.Areg(r1) && ia[1..] == lc;
                    assert AR.ActionsRepL(rer, qm, ia, code, em + 3);
                    ActionsRepLToFuel(rer, qm, ia, code, em + 3);
                    var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, em + 3, ni);
                    // the walk guard's CIN head arm
                    WO.WalkOkQuantCinHead(acts, code, pc, EaOf(b), greedy, min, delta, r1, em + 1, e1x + 2, inp);
                    var subi := ActionsTreeRepFRE(rer, qm, ia, code, em + 3, inp, BS.CannotExit, ti, ni, S);
                    var subc := ActionsTreeRepFRE(rer, qm, cont, code, pcmid, inp, b, tcont, n - 1, S);
                    assert {:split_here} true;   // (E3) section: assembly
                    // loop arm: tr_begin at em + 2, tr_reset at em + 1
                    assert TR.TreeRepRE(qm, subi, code, em + 2, inp, EaOf(b));
                    var tloop := LT.GroupActionT(LG.Reset(gidl), subi);
                    assert TR.TreeRepRE(qm, tloop, code, em + 1, inp, EaOf(b));
                    // skip arm: tr_stamp at e1x + 2 — the virtual chain of the
                    // body's first empty path, read off the oracle bits and tied
                    // to the spec path by rung B's `FirstEmptyPathRL`
                    assert LL.OracleOkAt(rer, qm, inp);
                    NT.FirstEmptyPathRL(rer, qm, qm.bodies[qidC], inp);
                    var p := NP.FirstEmptyPathL(rer, r1, inp).value;
                    assert TR.FirstEmptyPathR(qm, qm.bodies[qidC], inp) == Some(p);
                    var tskip := LT.GroupActionT(LG.Reset(gidl), TR.ChainT(p, subc));
                    assert TR.TreeRepRE(qm, tskip, code, e1x + 2, inp, EaOf(b)) by {
                      TR.PeelChainT(p, subc);
                      assert TR.StampShape(qm, qidC, tskip);
                      assert TR.PeelT(p, tskip.t) == Some(subc);
                      assert TR.TreeRepRE(qm, subc, code, e1x + 3, inp, EaOf(b));
                    }
                    tstar := LT.Choice(tloop, tskip);
                    assert TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b));   // tr_choice at the head fork
                    assert {:split_here} true;   // (E3) section: the relation
                    // the relation: rung A's theorem on the spec side, congruences on ours
                    NB.CinPlusPriorityBool(rer, r1, cont, inp, b, S, t, ti, tcont);
                    var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), ti),
                                          LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont)));
                    NB.ChainTEqChain(p, subc);
                    NB.RACongChainOutside(p, subc, tcont, inp, S);
                    NP.RACongGroupOutside(LG.Reset(gidl), subi, ti, inp, S);
                    NP.RACongGroupOutside(LG.Reset(gidl), NP.Chain(p, subc), NP.Chain(p, tcont), inp, S);
                    NP.RACongChoiceOutside(tloop, LT.GroupActionT(LG.Reset(gidl), ti),
                                           tskip, LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont)), inp, S);
                    NP.RATransOutside(tstar, tcin, t, inp, S);
                  case _ => assert false;
                }
              case _ =>
            }
          }
  }

  lemma ATR_QuantMin(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, greedy: bool, min: nat, delta: LN.NoI, r1: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTree(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActions(cont)
    requires EL.PikeLkRegex(L.Quantified(greedy, min, delta, r1))
    requires min > 0
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 1
  {
    // (§2.5b) hide the recursive nullability predicates (z3 4.14 matching loop; every use is opaque)
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL, AR.NfaRepStarCinL, EL.PikeLkRegexRec;
    assert acts == [acts[0]] + cont;
    EL.PikeLkActionsConsIff(acts[0], cont);
    var gidl := L.DefGroups(r1);
    match delta {
      case Inf =>
        // the do-while: min-1 forced copies, the stamp, the body, the
        // backward fork
        if !NUL.NonNullableL(r1) {
          if !greedy {
          // §2.5a GENERIC (lazy): `min` forced copies, then the ordinary star loop at
          // `em`. Unlike the do-while there is NO seam -- the code's
          // BeginLoop/EndLoop sits exactly where the spec's `Acheck` is -- so
          // nothing has to be inserted with `CE.BoolCheckInsert` and this arm
          // needs no nullability hypothesis at all.
          var em, e1x := AR.NfaRepLGenInv(rer, qm, greedy, min, r1, code, pc, pcmid);
          var qidL: int :| NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qidL, false))
            && qidL in qm.quants && qm.quants[qidL] == gidl;
          AR.NfaRepIncrL(rer, qm, r1, code, em + 3, e1x);
          var quant1 := L.Quantified(greedy, min - 1, LN.Inf, r1);
          var eb: nat :| (exists qid2: int ::
                NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid2, false))
                && qid2 in qm.quants && qm.quants[qid2] == gidl)
            && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
            && AR.NfaRepMinL(rer, qm, min - 1, r1, code, eb, em);
          if min > 1 {
            // the residual is the same GENERIC shape with one copy fewer
            AR.NfaRepLGenIntro(rer, qm, greedy, min - 1, r1, code, eb, em, e1x, pcmid, qidL);
          } else {
            // min == 1: `NfaRepMinL(0, …)` forces `eb == em`, and the loop at
            // `em` IS `NfaRepL`'s `min == 0 && Inf` (star) arm, verbatim
            assert eb == em;
          }
          assert AR.NfaRepL(rer, qm, quant1, code, eb, pcmid);
          match t {
            case GroupActionT(g, tc) =>
              assert g == LG.Reset(gidl);
              EL.PikeLkActionsConsIff(LS.Areg(quant1), cont);
              EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
              FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              assert AR.ActionRepL(rer, qm, LS.Areg(quant1), code, eb, pcmid);
              var lq1 := [LS.Areg(quant1)] + cont;
              assert lq1[0] == LS.Areg(quant1) && lq1[1..] == cont;
              assert AR.ActionsRepL(rer, qm, lq1, code, eb);
              var ia := [LS.Areg(r1)] + lq1;
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, eb);
              assert ia[0] == LS.Areg(r1) && ia[1..] == lq1;
              assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
              assert ia == [LS.Areg(r1), LS.Areg(quant1)] + cont;
              ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
              var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
              WO.WalkOkQuantForced(acts, code, pc, EaOf(b), greedy, min, delta, r1);
              assert CE.PSize(tc) < CE.PSize(t);
              assert LL.LkActsInS(ia, S) by {
                LL.LkActsInSTail(acts, S);
                assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(quant1, S);
                LL.LkActsInSCons(LS.Areg(quant1), cont, S);
                LL.LkActsInSCons(LS.Areg(r1), [LS.Areg(quant1)] + cont, S);
              }
              assert NB.EncOk(ia, inp, b) by {
                var parts := [LS.Areg(r1), LS.Areg(quant1)];
                assert parts + cont == ia;
                if NUL.NonNullableL(acts[0].r) { reveal NUL.NonNullableL; assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
                NB.EncOkExpand(acts, parts, inp, b);
              }
              var sub := ActionsTreeRepFRE(rer, qm, ia, code, pc + 1, inp, b, tc, ni, S);
              tstar := LT.GroupActionT(g, sub);
              NP.RACongGroupOutside(g, sub, tc, inp, S);
            case _ =>
          }
          } else {
            tstar := ATR_QuantCin(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, greedy, min, delta, r1, S);
          }
        } else {
          assert {:split_here} true;   // (E3) section: the do-while arm
          var em, e1x := AR.NfaRepLPlusInv(rer, qm, greedy, min, r1, code, pc, pcmid);
          assert NUL.NonNullableL(r1);
          var qid: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
            && qid in qm.quants && qm.quants[qid] == gidl;
          AR.NfaRepIncrL(rer, qm, r1, code, em + 1, e1x);
          if min > 1 {
          // a forced copy: stamp at pc, body at pc+1, the smaller
          // do-while continues at eb
          var quant1 := L.Quantified(greedy, min - 1, LN.Inf, r1);
          var eb: nat :| (exists qid2: int ::
                NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid2, false))
                && qid2 in qm.quants && qm.quants[qid2] == gidl)
            && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
            && AR.NfaRepMinL(rer, qm, min - 2, r1, code, eb, em);
          AR.NfaRepLPlusIntro(rer, qm, greedy, min - 1, r1, code, eb, em, e1x, pcmid, qid);
          assert AR.NfaRepL(rer, qm, quant1, code, eb, pcmid);
          match t {
            case GroupActionT(g, tc) =>
              assert g == LG.Reset(gidl);
              EL.PikeLkActionsConsIff(LS.Areg(quant1), cont);
              EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
              FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              assert AR.ActionRepL(rer, qm, LS.Areg(quant1), code, eb, pcmid);
              var lq1 := [LS.Areg(quant1)] + cont;
              assert lq1[0] == LS.Areg(quant1) && lq1[1..] == cont;
              assert AR.ActionsRepL(rer, qm, lq1, code, eb);
              var ia := [LS.Areg(r1)] + lq1;
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, eb);
              assert ia[0] == LS.Areg(r1) && ia[1..] == lq1;
              assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
              assert ia == [LS.Areg(r1), LS.Areg(quant1)] + cont;
              ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
              var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
              WO.WalkOkQuantForced(acts, code, pc, EaOf(b), greedy, min, delta, r1);
              assert CE.PSize(tc) < CE.PSize(t);
              assert LL.LkActsInS(ia, S) by {
                LL.LkActsInSTail(acts, S);
                assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(quant1, S);
                LL.LkActsInSCons(LS.Areg(quant1), cont, S);
                LL.LkActsInSCons(LS.Areg(r1), [LS.Areg(quant1)] + cont, S);
              }
              assert NB.EncOk(ia, inp, b) by {
                var parts := [LS.Areg(r1), LS.Areg(quant1)];
                assert parts + cont == ia;
                if NUL.NonNullableL(acts[0].r) { reveal NUL.NonNullableL; assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
                NB.EncOkExpand(acts, parts, inp, b);
              }
              var sub := ActionsTreeRepFRE(rer, qm, ia, code, pc + 1, inp, b, tc, ni, S);
              tstar := LT.GroupActionT(g, sub);
              // tr_reset at pc (the copy's clock-mark carries the Reset)
              NP.RACongGroupOutside(g, sub, tc, inp, S);
            case _ =>
          }
        } else {
          // min == 1: THE SEAM. The stamp is at pc (== em); the spec
          // walk has no check after this last forced body â€” insert it.
          assert em == pc;
          var q0 := L.Quantified(greedy, 0, LN.Inf, r1);
          match t {
            case GroupActionT(g, tc) =>
              assert g == LG.Reset(gidl);
              assert EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Areg(q0)] + cont, inp, b, tc);
              var pre := [LS.Areg(r1)];
              var rest := [LS.Areg(q0)] + cont;
              EL.PikeLkActionsConsIff(LS.Areg(q0), cont);
              EL.PikeLkActionsConsIff(LS.Areg(r1), rest);
              assert EL.PikeLkActions(pre) by {
                assert pre == [LS.Areg(r1)] + [];
                EL.PikeLkActionsConsIff(LS.Areg(r1), []);
              }
              assert pre + rest == [LS.Areg(r1), LS.Areg(q0)] + cont;
              assert CE.ConsumesBeforeAreg(pre) by {
                assert pre[0].Areg? && NUL.NonNullableL(pre[0].r);
              }
              var t1ck := CE.BoolCheckInsert(rer, pre, inp, rest, inp, b, tc);
              assert CE.LkConfinedTree(t1ck, S);   // BoolCheckInsert preserves it from LkConfinedTree(tc, S)
              var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
              assert ia == pre + [LS.Acheck(inp)] + rest;
              assert EL.BoolTreeLk(rer, ia, inp, b, t1ck);
              // representation of the checked list at pc+1: the body,
              // the zero-width check at the fork, the loop view
              assert AR.BackForkAt(code, e1x) by {
                assert NR.GetPcRE(code, e1x)
                    == Some(if greedy then RB.Fork(em, e1x + 1) else RB.Fork(e1x + 1, em));
                assert em <= e1x;
              }
              assert AR.NfaRepL(rer, qm, q0, code, e1x, e1x + 1) by {
                assert NUL.NonNullableL(r1)
                  && NR.GetPcRE(code, e1x)
                     == Some(if greedy then RB.Fork(em, e1x + 1) else RB.Fork(e1x + 1, em))
                  && em <= e1x
                  && (exists qid2: int ::
                        NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid2, false))
                        && qid2 in qm.quants && qm.quants[qid2] == L.DefGroups(r1))
                  && AR.NfaRepL(rer, qm, r1, code, em + 1, e1x);
              }
              FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              var lq := [LS.Areg(q0)] + cont;
              assert AR.ActionRepL(rer, qm, LS.Areg(q0), code, e1x, e1x + 1);
              assert lq[0] == LS.Areg(q0) && lq[1..] == cont;
              assert AR.ActionsRepL(rer, qm, lq, code, e1x);
              var lc := [LS.Acheck(inp)] + lq;
              EL.PikeLkActionsConsIff(LS.Acheck(inp), lq);
              assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1x, e1x);
              assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
              assert AR.ActionsRepL(rer, qm, lc, code, e1x);
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, e1x);
              assert ia == [LS.Areg(r1)] + lc;
              assert ia[0] == LS.Areg(r1) && ia[1..] == lc;
              assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
              EL.PikeLkActionsConsIff(LS.Areg(r1), lc);
              assert EL.PikeLkActions(ia);
              ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
              var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
              WO.WalkOkQuantSeam(acts, code, pc, EaOf(b), greedy, r1, inp);
              assert CE.PSize(t1ck) == CE.PSize(tc);
              assert CE.PSize(t1ck) < CE.PSize(t);
              assert LL.LkActsInS(ia, S) by {
                LL.LkActsInSTail(acts, S);
                assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(q0, S);
                LL.LkActsInSCons(LS.Areg(q0), cont, S);
                LL.LkActsInSCons(LS.Acheck(inp), [LS.Areg(q0)] + cont, S);
                LL.LkActsInSCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont), S);
                assert ia == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
              }
              assert NB.EncOk(ia, inp, b) by {
                NB.EncodableTail(acts, inp, b);
                if b == BS.CannotExit { NB.EncOkIter(r1, q0, cont, inp); }
                else { NB.EncOkIterLift(r1, q0, cont, inp); }
              }
              var sub := ActionsTreeRepFRE(rer, qm, ia, code, pc + 1, inp, b, t1ck, ni, S);
              tstar := LT.GroupActionT(g, sub);
              // tr_reset at pc (the do-while stamp; the VM's
              // SetQuantToClock preserves exit_allowed, so b carries)
              assert LL.LeavesAgreeAtOutside(t1ck, tc, inp, S);
              NP.ResFromLeavesOutside(t1ck, tc, inp, S);
              NP.RATransOutside(sub, t1ck, tc, inp, S);
              NP.RACongGroupOutside(g, sub, tc, inp, S);
            case _ =>
          }
        }
        }
      case NN(kx) =>
        assert {:split_here} true;   // (E3) section: the bounded arm
        var em := AR.NfaRepLQuantInv(rer, qm, greedy, min, kx, r1, code, pc, pcmid);
        var quant1 := L.Quantified(greedy, min - 1, delta, r1);
        var eb: nat :| (exists qid: int ::
              NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
              && qid in qm.quants && qm.quants[qid] == gidl)
          && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
          && AR.NfaRepMinL(rer, qm, min - 1, r1, code, eb, em);
        AR.NfaRepLQuantIntro(rer, qm, greedy, min - 1, kx, r1, code, eb, em, pcmid);
        assert AR.NfaRepL(rer, qm, quant1, code, eb, pcmid);
        match t {
          case GroupActionT(g, tc) =>
            assert g == LG.Reset(gidl);
            EL.PikeLkActionsConsIff(LS.Areg(quant1), cont);
            EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
            FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
            assert AR.ActionRepL(rer, qm, LS.Areg(quant1), code, eb, pcmid);
            var lq1 := [LS.Areg(quant1)] + cont;
            assert lq1[0] == LS.Areg(quant1) && lq1[1..] == cont;
            assert AR.ActionsRepL(rer, qm, lq1, code, eb);
            var ia := [LS.Areg(r1)] + lq1;
            assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, eb);
            assert ia[0] == LS.Areg(r1) && ia[1..] == lq1;
            assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
            assert ia == [LS.Areg(r1), LS.Areg(quant1)] + cont;
            ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
            var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
              WO.WalkOkQuantForced(acts, code, pc, EaOf(b), greedy, min, delta, r1);
            assert CE.PSize(tc) < CE.PSize(t);
            assert LL.LkActsInS(ia, S) by {
              LL.LkActsInSTail(acts, S);
              assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(quant1, S);
              LL.LkActsInSCons(LS.Areg(quant1), cont, S);
              LL.LkActsInSCons(LS.Areg(r1), [LS.Areg(quant1)] + cont, S);
            }
            assert NB.EncOk(ia, inp, b) by {
              var parts := [LS.Areg(r1), LS.Areg(quant1)];
              assert parts + cont == ia;
              if NUL.NonNullableL(acts[0].r) { reveal NUL.NonNullableL; assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
              NB.EncOkExpand(acts, parts, inp, b);
            }
            var sub := ActionsTreeRepFRE(rer, qm, ia, code, pc + 1, inp, b, tc, ni, S);
            tstar := LT.GroupActionT(g, sub);
            // tr_reset at pc (the clock-mark carries the Reset node)
            NP.RACongGroupOutside(g, sub, tc, inp, S);
          case _ =>
        }
    }
  }

  /** (2026-08-29 E3) the `Quantified` arm of `ActionsTreeRepFRE`, min == 0 && delta.NN? — extracted from a 350-line
      case so each branch is its own VC (the parent no longer needs `{:isolate_assertions}`). */
  lemma ATR_QuantNN(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, greedy: bool, min: nat, delta: LN.NoI, r1: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTree(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActions(cont)
    requires EL.PikeLkRegex(L.Quantified(greedy, min, delta, r1))
    requires min == 0 && delta.NN?
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 1
  {
    assert acts == [acts[0]] + cont;
    EL.PikeLkActionsConsIff(acts[0], cont);
    var gidl := L.DefGroups(r1);
    // min == 0, bounded delta: spent (k == 0) or one optional layer
    var k := delta.n;
    var em := AR.NfaRepLQuantInv(rer, qm, greedy, 0, k, r1, code, pc, pcmid);
    assert em == pc;   // the forced chain is empty
    if k == 0 {
      // spent quantifier: no code, epsilon-continue with cont
      assert pc == pcmid;
      WO.WalkOkQuantSpent(acts, code, pc, EaOf(b), greedy, r1);
      assert LS.ActionsRegexSize(cont) < LS.ActionsRegexSize(acts);
      assert MsizeA(cont) < MsizeA(acts);
      assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
      assert NB.EncOk(cont, inp, b) by { NB.EncOkTailReg(acts, inp, b); }
      tstar := ActionsTreeRepFRE(rer, qm, cont, code, pcmid, inp, b, t, n - 1, S);
    } else {
      // one bounded layer: the fork skips to the common end pcmid
      var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
      assert quant == L.Quantified(greedy, 0, LN.NN(k - 1), r1);
      var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, pcmid) else RB.Fork(pcmid, pc + 1))
        && (exists qid: int ::
              NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
              && qid in qm.quants && qm.quants[qid] == gidl)
        && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
        && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && AR.NfaRepOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
      AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
      AR.NfaRepIncrOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
      match t {
        case Choice(ta, tb) =>
          var itert := if greedy then ta else tb;
          var skipt := if greedy then tb else ta;
          match itert {
            case GroupActionT(g, ti) =>
              assert g == LG.Reset(gidl);
              WO.WalkOkQuantLayer(acts, code, pc, EaOf(b), greedy, delta, r1,
                                  if greedy then pc + 1 else pcmid,
                                  if greedy then pcmid else pc + 1, inp);
              // skip branch: cont at the common end pcmid
              assert CE.PSize(skipt) < CE.PSize(t);
              assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
              assert NB.EncOk(cont, inp, b) by { NB.EncOkTailReg(acts, inp, b); }
              var subs := ActionsTreeRepFRE(rer, qm, cont, code, pcmid, inp, b, skipt, n - 1, S);
              // iteration branch at pc+3 with the NN(k-1) continuation at e1+1
              EL.PikeLkActionsConsIff(LS.Areg(quant), cont);
              EL.PikeLkActionsConsIff(LS.Acheck(inp), [LS.Areg(quant)] + cont);
              EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
              FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              var lq := [LS.Areg(quant)] + cont;
              assert AR.NfaRepMinL(rer, qm, 0, r1, code, e1 + 1, e1 + 1);
              AR.NfaRepLQuantIntro(rer, qm, greedy, 0, k - 1, r1, code, e1 + 1, e1 + 1, pcmid);
              assert AR.ActionRepL(rer, qm, LS.Areg(quant), code, e1 + 1, pcmid);
              assert lq[0] == LS.Areg(quant) && lq[1..] == cont;
              assert AR.ActionsRepL(rer, qm, lq, code, e1 + 1);
              // Acheck as the fall-through EndLoop onto the next layer
              var lc := [LS.Acheck(inp)] + lq;
              assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1, e1 + 1);
              assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
              assert AR.ActionsRepL(rer, qm, lc, code, e1);
              var ia := [LS.Areg(r1)] + lc;
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 3, e1);
              assert ia[0] == LS.Areg(r1) && ia[1..] == lc;
              assert AR.ActionsRepL(rer, qm, ia, code, pc + 3);
              assert ia == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
              ActionsRepLToFuel(rer, qm, ia, code, pc + 3);
              var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, pc + 3, ni);
              assert CE.PSize(ti) < CE.PSize(t);
              assert LL.LkActsInS(ia, S) by {
                LL.LkActsInSTail(acts, S);
                assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(quant, S);
                LL.LkActsInSCons(LS.Areg(quant), cont, S);
                LL.LkActsInSCons(LS.Acheck(inp), lq, S);
                LL.LkActsInSCons(LS.Areg(r1), lc, S);
              }
              assert NB.EncOk(ia, inp, BS.CannotExit) by {
                NB.EncodableTail(acts, inp, b);
                NB.EncOkIter(r1, quant, cont, inp);
              }
              var subi := ActionsTreeRepFRE(rer, qm, ia, code, pc + 3, inp, BS.CannotExit, ti, ni, S);
              // assemble: subi at pc+3 (false) -> tr_begin at pc+2 ->
              // tr_reset at pc+1 -> tr_choice with the skip at pcmid
              assert TR.TreeRepRE(qm, subi, code, pc + 3, inp, false);
              assert TR.TreeRepRE(qm, subi, code, pc + 2, inp, EaOf(b));
              var iterstar := LT.GroupActionT(g, subi);
              assert TR.TreeRepRE(qm, iterstar, code, pc + 1, inp, EaOf(b));
              tstar := if greedy then LT.Choice(iterstar, subs) else LT.Choice(subs, iterstar);
              NP.RACongGroupOutside(g, subi, ti, inp, S);
              if greedy {
                NP.RACongChoiceOutside(iterstar, itert, subs, skipt, inp, S);
              } else {
                NP.RACongChoiceOutside(subs, skipt, iterstar, itert, inp, S);
              }
              assert TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b));
            case _ =>
          }
        case _ =>
      }
    }
  }

  /** (2026-08-29 E3) the `Quantified` arm of `ActionsTreeRepFRE`, min == 0 && delta == LN.Inf — extracted from a 350-line
      case so each branch is its own VC (the parent no longer needs `{:isolate_assertions}`). */
  lemma ATR_QuantStar(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, greedy: bool, min: nat, delta: LN.NoI, r1: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTree(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActions(cont)
    requires EL.PikeLkRegex(L.Quantified(greedy, min, delta, r1))
    requires min == 0 && delta == LN.Inf
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 1
  {
    assert acts == [acts[0]] + cont;
    EL.PikeLkActionsConsIff(acts[0], cont);
    var gidl := L.DefGroups(r1);
    assert min == 0 && delta == LN.Inf;
    var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
    assert quant == L.Quantified(greedy, 0, LN.Inf, r1) == L.Quantified(greedy, min, delta, r1);
    if exists e1: nat :: NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                 && (exists qid: int ::
                       NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                       && qid in qm.quants && qm.quants[qid] == gidl)
                 && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                 && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                 && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                 && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                 && pcmid == e1 + 2 {
      // the star FAST PATH (forward decision point)
      var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                   && (exists qid: int ::
                         NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                         && qid in qm.quants && qm.quants[qid] == gidl)
                   && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                   && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                   && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                   && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                   && pcmid == e1 + 2;
      AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
      match t {
        case Choice(ta, tb) =>
          var itert := if greedy then ta else tb;
          var skipt := if greedy then tb else ta;
          match itert {
            case GroupActionT(g, ti) =>
              assert g == LG.Reset(gidl);
              WO.WalkOkQuantLayer(acts, code, pc, EaOf(b), greedy, delta, r1,
                                  if greedy then pc + 1 else pcmid,
                                  if greedy then pcmid else pc + 1, inp);
              // skip branch at pcmid == e1+2
              assert CE.PSize(skipt) < CE.PSize(t);
              assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
              assert NB.EncOk(cont, inp, b) by { NB.EncOkTailReg(acts, inp, b); }
              var subs := ActionsTreeRepFRE(rer, qm, cont, code, pcmid, inp, b, skipt, n - 1, S);
              // iteration branch: [Areg r1, Acheck inp, Areg quant] + cont at pc+3
              EL.PikeLkActionsConsIff(LS.Areg(quant), cont);
              EL.PikeLkActionsConsIff(LS.Acheck(inp), [LS.Areg(quant)] + cont);
              EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
              FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              // [Areg quant]+cont at pc (the star block itself, ending at pcmid)
              var lq := [LS.Areg(quant)] + cont;
              assert AR.ActionRepL(rer, qm, LS.Areg(quant), code, pc, pcmid);
              assert lq[0] == LS.Areg(quant) && lq[1..] == cont;
              assert AR.ActionsRepL(rer, qm, lq, code, pc);
              // absorbed back-jump: lq at e1+1 via jump_bc
              AR.ActionsRepLJmp(rer, qm, lq, code, e1 + 1, pc);
              // [Acheck inp]+lq at e1 (fall-through EndLoop)
              var lc := [LS.Acheck(inp)] + lq;
              assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1, e1 + 1);
              assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
              assert AR.ActionsRepL(rer, qm, lc, code, e1);
              // [Areg r1]+lc at pc+3
              var ia := [LS.Areg(r1)] + lc;
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 3, e1);
              assert ia[0] == LS.Areg(r1) && ia[1..] == lc;
              assert AR.ActionsRepL(rer, qm, ia, code, pc + 3);
              assert ia == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
              ActionsRepLToFuel(rer, qm, ia, code, pc + 3);
              var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, pc + 3, ni);
              assert CE.PSize(ti) < CE.PSize(t);
              assert LL.LkActsInS(ia, S) by {
                LL.LkActsInSTail(acts, S);
                assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(quant, S);
                LL.LkActsInSCons(LS.Areg(quant), cont, S);
                LL.LkActsInSCons(LS.Acheck(inp), lq, S);
                LL.LkActsInSCons(LS.Areg(r1), lc, S);
              }
              assert NB.EncOk(ia, inp, BS.CannotExit) by {
                NB.EncodableTail(acts, inp, b);
                NB.EncOkIter(r1, quant, cont, inp);
              }
              var subi := ActionsTreeRepFRE(rer, qm, ia, code, pc + 3, inp, BS.CannotExit, ti, ni, S);
              // assemble: subi at pc+3 (false) â†’ tr_begin at pc+2 (any b) â†’
              // tr_reset at pc+1 (consumes the Reset node at b) â†’ tr_choice
              assert TR.TreeRepRE(qm, subi, code, pc + 3, inp, false);
              assert TR.TreeRepRE(qm, subi, code, pc + 2, inp, EaOf(b));
              var iterstar := LT.GroupActionT(g, subi);
              assert TR.TreeRepRE(qm, iterstar, code, pc + 1, inp, EaOf(b));
              tstar := if greedy then LT.Choice(iterstar, subs) else LT.Choice(subs, iterstar);
              NP.RACongGroupOutside(g, subi, ti, inp, S);
              if greedy {
                NP.RACongChoiceOutside(iterstar, itert, subs, skipt, inp, S);
              } else {
                NP.RACongChoiceOutside(subs, skipt, iterstar, itert, inp, S);
              }
              assert TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b));
            case _ =>
          }
        case _ =>
      }
    } else {
      // the LOOP VIEW: a bare star at the do-while's backward fork.
      // WalkOk pins the flag to CanExit; the whole configuration is
      // delegated to the fused fork lemma, and the extra Progress it
      // returns is invisible to the leaves.
      AR.NfaRepLStarLoopViews(rer, qm, greedy, r1, code, pc, pcmid);
      if NUL.NonNullableL(r1) {
        var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em))
          && em <= pc
          && (exists qid: int ::
                NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                && qid in qm.quants && qm.quants[qid] == gidl)
          && AR.NfaRepL(rer, qm, r1, code, em + 1, pc)
          && pcmid == pc + 1;
        WO.WalkOkLoopView(acts, code, pc, EaOf(b), greedy, LN.Inf, r1,
                          if greedy then em else pc + 1,
                          if greedy then pc + 1 else em, inp);
      } else {
        // §2.5b: the CIN loop view (a greedy star at the CIN loop's end fork)
        var em, e1 := AR.NfaRepLStarCinInv(rer, qm, r1, code, pc, pcmid);
        WO.WalkOkLoopView(acts, code, pc, EaOf(b), greedy, LN.Inf, r1, em + 1, e1 + 3, inp);
      }
      assert EaOf(b) == true;
      assert b == BS.CanExit;
      assert AR.BackForkAt(code, pc);
      var sub := AtBackForkTreeRep(rer, qm, acts, code, pc, inp, t, n, S);
      tstar := LT.Progress(sub);
      NP.RAProgressPassOutside(sub, inp, S);
      assert NP.ResAgreeAtOutside(tstar, t, inp, S);
  }
  }

  lemma ActionsTreeRepFRE(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, code: RB.code, pc: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTree(t, S)
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 2
  {
    if |acts| == 0 && NR.GetPcRE(code, pc) == Some(RB.Accept) {
      assert t == LT.Match;
      tstar := LT.Match;
    } else if exists pcstart: nat :: NR.GetPcRE(code, pc) == Some(RB.Jmp(pcstart)) && ActionsRepFuelL(rer, qm, acts, code, pcstart, n - 1) {
      var pcstart: nat :| NR.GetPcRE(code, pc) == Some(RB.Jmp(pcstart)) && ActionsRepFuelL(rer, qm, acts, code, pcstart, n - 1);
      WO.WalkOkJmp(acts, code, pc, EaOf(b), pcstart);
      tstar := ActionsTreeRepFRE(rer, qm, acts, code, pcstart, inp, b, t, n - 1, S);
      // tr_jmp
      assert TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b));
    } else {
      var cont := acts[1..];
      var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1);
      EL.PikeLkActionsTail(acts);
      assert acts == [acts[0]] + cont;
      EL.PikeLkActionsConsIff(acts[0], cont);
      match acts[0]
      case Acheck(strcheck) =>
        tstar := ATR_Acheck(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, S);
      case Aclose(gid) =>
        tstar := ATR_Aclose(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, gid, S);
      case Areg(r) =>
        assert EL.PikeLkRegex(r);
        match r
        case Epsilon =>
          tstar := ATR_Epsilon(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, S);
        case Character(cd) =>
          tstar := ATR_Character(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, cd, S);
        case Disjunction(r1, r2) =>
          tstar := ATR_Disjunction(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, r1, r2, S);
        case Sequence(r1, r2) =>
          tstar := ATR_Sequence(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, r1, r2, S);
        case Quantified(greedy, min, delta, r1) => {
          if min > 0 { tstar := ATR_QuantMin(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, greedy, min, delta, r1, S); }
          else if delta.NN? { tstar := ATR_QuantNN(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, greedy, min, delta, r1, S); }
          else { tstar := ATR_QuantStar(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, greedy, min, delta, r1, S); }
        }
        case Group(gid, r1) =>
          tstar := ATR_Group(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, gid, r1, S);
        case AnchorR(la) =>
          tstar := ATR_AnchorR(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, la, S);
        case LookaroundR(lk, r1) =>
          tstar := ATR_LookaroundR(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, lk, r1, S);
        case Backreference(gid) =>   // not pike
    }
  }

  lemma ATR_Acheck(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTree(t, S)
    requires |acts| > 0 && acts[0].Acheck?
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActions(cont)
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
        assert LS.ActionsRegexSize(acts) == LS.ActionsRegexSize(cont);
        if NR.GetPcRE(code, pc) == Some(RB.EndLoop) {
          assert pcmid == pc + 1;
          if b == BS.CanExit {
            match t {
              case Progress(tc) =>
                WO.WalkOkAcheckEndLoop(acts, code, pc, EaOf(b));
                assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
                assert NB.EncOk(cont, inp, BS.CanExit) by { NB.EncOkTailCheck(acts, inp); }
                var sub := ActionsTreeRepFRE(rer, qm, cont, code, pc + 1, inp, BS.CanExit, tc, n - 1, S);
                tstar := LT.Progress(sub);
                // tr_progress (fall-through EndLoop)
                NP.RACongProgressOutside(sub, tc, inp, S);
              case _ =>
            }
          } else {
            // t == Mismatch: tr_progressfail
            tstar := LT.Mismatch;
          }
        } else {
          // the zero-width check at the do-while's backward fork
          assert AR.BackForkAt(code, pc) && pcmid == pc;
          if b == BS.CanExit {
            match t {
              case Progress(tc) =>
                WO.WalkOkAcheckBackFork(acts, code, pc, EaOf(b));
                assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
                assert NB.EncOk(cont, inp, BS.CanExit) by { NB.EncOkTailCheck(acts, inp); }
                var sub := AtBackForkTreeRep(rer, qm, cont, code, pc, inp, tc, n - 1, S);
                tstar := LT.Progress(sub);
                NP.RACongProgressOutside(sub, tc, inp, S);
              case _ =>
            }
          } else {
            // t == Mismatch: the dissolved guard fails â€” tr_plusfail
            tstar := LT.Mismatch;
            var fx: int, fy: int :| NR.GetPcRE(code, pc) == Some(RB.Fork(fx, fy))
              && fx >= 0 && fy >= 0 && (fx as nat <= pc || fy as nat <= pc);
            assert TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b));
          }
        }
  }

  lemma ATR_Aclose(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, gid: LG.GroupId, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTree(t, S)
    requires |acts| > 0 && acts[0] == LS.Aclose(gid)
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActions(cont)
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
        match t {
          case GroupActionT(g, tc) =>
            assert g == LG.Close(gid);
            WO.WalkOkAclose(acts, code, pc, EaOf(b));
            assert CE.PSize(tc) < CE.PSize(t);
            assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
            assert NB.EncOk(cont, inp, b) by { NB.EncOkTailReg(acts, inp, b); }
            var sub := ActionsTreeRepFRE(rer, qm, cont, code, pc + 1, inp, b, tc, n - 1, S);
            tstar := LT.GroupActionT(g, sub);
            // tr_close
            NP.RACongGroupOutside(g, sub, tc, inp, S);
          case _ =>
        }
  }

  lemma ATR_Epsilon(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTree(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Epsilon)
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActions(cont)
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
          assert pcmid == pc;
          WO.WalkOkEpsilon(acts, code, pc, EaOf(b));
          assert MsizeA(cont) < MsizeA(acts);
          assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
          assert NB.EncOk(cont, inp, b) by { NB.EncOkTailReg(acts, inp, b); }
          tstar := ActionsTreeRepFRE(rer, qm, cont, code, pc, inp, b, t, n - 1, S);
  }

  lemma ATR_Character(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, cd: LC.CharDescr, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTree(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Character(cd))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActions(cont)
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
          var ce :| NR.GetPcRE(code, pc) == Some(RB.Consume(ce)) && AR.ExpectationMatches(rer, ce, cd);
          AR.ReadAgree(rer, ce, cd, inp);
          match LC.ReadChar(rer, cd, inp, WP.Forward) {
            case None =>
              // t == Mismatch; tr_readfail (ReadCharE == None by ReadAgree)
              tstar := LT.Mismatch;
            case Some(pair) =>
              match t {
                case Read(c, tc) =>
                  assert c == pair.0;
                  WO.WalkOkCharacter(acts, code, pc, EaOf(b));
                  assert CE.PSize(tc) < CE.PSize(t);
                  assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
                  assert NB.EncOk(cont, pair.1, BS.CanExit) by {
                    assert |inp.next| > 0 && pair.1 == LC.Input(inp.next[1..], [inp.next[0]] + inp.pref);
                    NB.EncOkRead(acts, inp, b, pair.1);
                  }
                  var sub := ActionsTreeRepFRE(rer, qm, cont, code, pc + 1, pair.1, BS.CanExit, tc, n - 1, S);
                  tstar := LT.Read(c, sub);
                  // tr_read with witness (ce, pair.1)
                  assert AR.ReadCharE(ce, inp) == Some((c, pair.1));
                  NP.RACongReadOutside(c, sub, tc, inp, S);
                case _ =>
              }
          }
  }

  lemma ATR_Disjunction(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, r1: L.Regex, r2: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTree(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Disjunction(r1, r2))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActions(cont)
    requires EL.PikeLkRegex(L.Disjunction(r1, r2))
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
          EL.PikeLkActionsConsIff(LS.Areg(r1), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
          var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.Fork(pc + 1, e1 + 1))
                       && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid))
                       && AR.NfaRepL(rer, qm, r2, code, e1 + 1, pcmid);
          AR.NfaRepIncrL(rer, qm, r1, code, pc + 1, e1);
          match t {
            case Choice(ta, tb) =>
              WO.WalkOkAlt(acts, code, pc, EaOf(b), r1, r2, pc + 1, e1 + 1);
              // left branch: [Areg r1]+cont at pc+1 (cont reached via Jmp(e1â†’pcmid))
              var la := [LS.Areg(r1)] + cont;
              assert AR.ActionsRepL(rer, qm, cont, code, e1) by {
                FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                assert NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid));
              }
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, e1);
              assert la[0] == LS.Areg(r1) && la[1..] == cont;
              assert AR.ActionsRepL(rer, qm, la, code, pc + 1);
              ActionsRepLToFuel(rer, qm, la, code, pc + 1);
              var na: nat :| ActionsRepFuelL(rer, qm, la, code, pc + 1, na);
              assert CE.PSize(ta) < CE.PSize(t);
              assert LL.LkActsInS(la, S) by { LL.LkActsInSTail(acts, S); LL.LkActsInSCons(LS.Areg(r1), cont, S); }
              assert NB.EncOk(la, inp, b) by {
                var parts := [LS.Areg(r1)];
                assert parts + cont == la;
                if NUL.NonNullableL(acts[0].r) { assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
                NB.EncOkExpand(acts, parts, inp, b);
              }
              var suba := ActionsTreeRepFRE(rer, qm, la, code, pc + 1, inp, b, ta, na, S);
              // right branch: [Areg r2]+cont at e1+1
              var lb := [LS.Areg(r2)] + cont;
              FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              assert AR.ActionRepL(rer, qm, LS.Areg(r2), code, e1 + 1, pcmid);
              assert lb[0] == LS.Areg(r2) && lb[1..] == cont;
              assert AR.ActionsRepL(rer, qm, lb, code, e1 + 1);
              ActionsRepLToFuel(rer, qm, lb, code, e1 + 1);
              var nb: nat :| ActionsRepFuelL(rer, qm, lb, code, e1 + 1, nb);
              assert CE.PSize(tb) < CE.PSize(t);
              assert LL.LkActsInS(lb, S) by { LL.LkActsInSTail(acts, S); LL.LkActsInSCons(LS.Areg(r2), cont, S); }
              assert NB.EncOk(lb, inp, b) by {
                var parts := [LS.Areg(r2)];
                assert parts + cont == lb;
                if NUL.NonNullableL(acts[0].r) { assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
                NB.EncOkExpand(acts, parts, inp, b);
              }
              var subb := ActionsTreeRepFRE(rer, qm, lb, code, e1 + 1, inp, b, tb, nb, S);
              tstar := LT.Choice(suba, subb);
              // tr_choice with the forward Fork(pc+1, e1+1)
              NP.RACongChoiceOutside(suba, ta, subb, tb, inp, S);
            case _ =>
          }
  }

  lemma ATR_Sequence(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, r1: L.Regex, r2: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTree(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Sequence(r1, r2))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActions(cont)
    requires EL.PikeLkRegex(L.Sequence(r1, r2))
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
          EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
          assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
          var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
          var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
          assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
          assert AR.ActionRepL(rer, qm, LS.Areg(r2), code, e1, pcmid);
          assert ([LS.Areg(r2)] + cont)[0] == LS.Areg(r2) && ([LS.Areg(r2)] + cont)[1..] == cont;
          FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
          assert AR.ActionsRepL(rer, qm, [LS.Areg(r2)] + cont, code, e1);
          assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc, e1);
          assert na[0] == LS.Areg(r1) && na[1..] == [LS.Areg(r2)] + cont;
          assert AR.ActionsRepL(rer, qm, na, code, pc);
          assert LS.ActionsRegexSize(na) < LS.ActionsRegexSize(acts);
          assert MsizeA(na) < MsizeA(acts);
          ActionsRepLToFuel(rer, qm, na, code, pc);
          var nn: nat :| ActionsRepFuelL(rer, qm, na, code, pc, nn);
          WO.WalkOkSeq(acts, code, pc, EaOf(b), r1, r2);
          assert LL.LkActsInS(na, S) by {
            LL.LkActsInSTail(acts, S);
            LL.LkActsInSCons(LS.Areg(r2), cont, S);
            LL.LkActsInSCons(LS.Areg(r1), [LS.Areg(r2)] + cont, S);
          }
          assert NB.EncOk(na, inp, b) by {
            var parts := [LS.Areg(r1), LS.Areg(r2)];
            assert parts + cont == na;
            if NUL.NonNullableL(acts[0].r) {
              if NUL.NonNullableL(r1) { assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
              else { assert parts[1].Areg? && NUL.NonNullableL(parts[1].r); }
            }
            NB.EncOkExpand(acts, parts, inp, b);
          }
          tstar := ActionsTreeRepFRE(rer, qm, na, code, pc, inp, b, t, nn, S);
  }

  lemma ATR_Group(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, gid: LG.GroupId, r1: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTree(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Group(gid, r1))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActions(cont)
    requires EL.PikeLkRegex(L.Group(gid, r1))
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
          EL.PikeLkActionsConsIff(LS.Aclose(gid), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
          var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid as int)))
                       && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(gid as int)))
                       && pcmid == e1 + 1;
          match t {
            case GroupActionT(g, tc) =>
              assert g == LG.Open(gid);
              WO.WalkOkGroup(acts, code, pc, EaOf(b), gid, r1);
              var lc := [LS.Aclose(gid)] + cont;
              assert AR.ActionRepL(rer, qm, LS.Aclose(gid), code, e1, e1 + 1);
              assert lc[0] == LS.Aclose(gid) && lc[1..] == cont;
              FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              assert AR.ActionsRepL(rer, qm, lc, code, e1);
              var ga := [LS.Areg(r1)] + lc;
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, e1);
              assert ga[0] == LS.Areg(r1) && ga[1..] == lc;
              assert AR.ActionsRepL(rer, qm, ga, code, pc + 1);
              assert ga == [LS.Areg(r1), LS.Aclose(gid)] + cont;
              ActionsRepLToFuel(rer, qm, ga, code, pc + 1);
              var ng: nat :| ActionsRepFuelL(rer, qm, ga, code, pc + 1, ng);
              assert CE.PSize(tc) < CE.PSize(t);
              assert LL.LkActsInS(ga, S) by {
                LL.LkActsInSTail(acts, S);
                LL.LkActsInSCons(LS.Aclose(gid), cont, S);
                LL.LkActsInSCons(LS.Areg(r1), [LS.Aclose(gid)] + cont, S);
              }
              assert NB.EncOk(ga, inp, b) by {
                var parts := [LS.Areg(r1), LS.Aclose(gid)];
                assert parts + cont == ga;
                if NUL.NonNullableL(acts[0].r) { assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
                NB.EncOkExpand(acts, parts, inp, b);
              }
              var sub := ActionsTreeRepFRE(rer, qm, ga, code, pc + 1, inp, b, tc, ng, S);
              tstar := LT.GroupActionT(g, sub);
              // tr_open
              NP.RACongGroupOutside(g, sub, tc, inp, S);
            case _ =>
          }
  }

  lemma ATR_AnchorR(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, la: L.Anchor, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTree(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.AnchorR(la))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActions(cont)
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
          // NfaRepL(AnchorR) => AnchorAssertion(ra) at pc with TrAnchor(ra) == la, pcmid == pc + 1
          var ra: R.anchor :| NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(ra))
                              && T.TrAnchor(ra) == la;
          TR.AnchorAgreeInput(rer, ra, inp);
          if LS.AnchorSatisfied(rer, la, inp) {
            match t {
              case AnchorPass(la2, tc) =>
                assert la2 == la;
                WO.WalkOkAnchor(acts, code, pc, EaOf(b));
                assert CE.PSize(tc) < CE.PSize(t);
                assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
                assert NB.EncOk(cont, inp, b) by { NB.EncOkTailReg(acts, inp, b); }
                var sub := ActionsTreeRepFRE(rer, qm, cont, code, pc + 1, inp, b, tc, n - 1, S);
                tstar := LT.AnchorPass(la2, sub);
                // tr_anchorpass (is_satisfied via the agreement)
                NP.RACongAnchorOutside(la2, sub, tc, inp, S);
              case _ =>
            }
          } else {
            // t == Mismatch; tr_anchorfail via the agreement
            tstar := LT.Mismatch;
          }
  }

  lemma ATR_LookaroundR(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, lk: L.Lookaround, r1: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTree(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.LookaroundR(lk, r1))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActions(cont)
    requires EL.PikeLkRegex(L.LookaroundR(lk, r1))
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
    var r := L.LookaroundR(lk, r1);
          // THE GATE. `NfaRepL`'s lookaround arm pins one zero-width
          // instruction at `pc`, whose bare lid the `looks` table maps back to
          // this (flavour, body); `OracleOkAt` says the oracle column agrees
          // with the body's walk, which is what `BoolTreeLk`'s rule decided by.
          // The checked tree DROPS the wrapper: it is the continuation's tree
          // on a pass, `Mismatch` on a kill.
          var lid: int :| NR.GetPcRE(code, pc)
                            == Some(if AR.PositiveL(lk) then RB.CheckOracle(lid)
                                                        else RB.NegCheckOracle(lid))
                          && lid in qm.looks && qm.looks[lid] == (lk, r1);
          assert pcmid == pc + 1;
          assert LL.OracleOkAt(rer, qm, inp);
          var tlkc := FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
          var bit := LOr.view_get_oracle(qm.ov, TR.CpOf(inp), lid);
          assert bit <==> LT.TreeRes(tlkc, LG.Empty, inp, L.LkDir(lk)).Some?;
          LT.FirstTreeLeaf(tlkc, LG.Empty, inp, L.LkDir(lk));
          // L3a/L3b: a POSITIVE look (fwd/bwd) body may CAPTURE (`NoLkBrL`, not
          // group-free); its confinement is supplied by `LkConfinedTree(t, S)`
          // in the pass branch below. The NEGATIVE flavours keep a group-free
          // body, so its body tree is `GmNeutral` -- exactly what the
          // capture-free `LAAtGatePass` path requires.
          if !L.Positivity(lk) {
            assert EL.PikeLkRegex(r);   // == GroupFreeL(r1) in this (negative) branch
            LL.ComputeTrGmNeutral(rer, r1, inp, LG.Empty, L.LkDir(lk));   // GmNeutralTree(tlkc)
          }
          match t {
            case LK(lk2, tlk, tc) =>
              // the gate passed: `LkGateOk(.., true)` pins tlk == tlkc and the
              // verdict, so the engine's bit agrees
              assert tlk == tlkc && LS.LkResult(lk, tlk, LG.Empty, inp).Some?;
              assert bit == AR.PositiveL(lk);
              WO.WalkOkLookaround(acts, code, pc, EaOf(b));
              assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
              assert NB.EncOk(cont, inp, b) by { NB.EncOkTailReg(acts, inp, b); }
              var sub := ActionsTreeRepFRE(rer, qm, cont, code, pc + 1, inp, b, tc, n - 1, S);
              tstar := sub;
              // tr_lk / tr_neglk: the gate rule carries the SAME tree onward
              assert TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b));
              if L.Positivity(lk) {
                // L3a/L3b: a POSITIVE look (fwd/bwd) gate may fold captures within
                // S -- use the confinement path (works for capture-free bodies
                // too, since GmNeutral => GmConfinedTree(_, S)).
                assert CE.GmConfinedTree(tlk, S);   // from LkConfinedTree(t, S), t == LK(_,tlk,tc)
                assert |LT.TreeLeaves(tlk, LG.Empty, inp, L.LkDir(lk))| > 0 by {
                  assert LT.TreeRes(tlk, LG.Empty, inp, L.LkDir(lk)).Some?;   // LkResult(lk,tlk,Empty).Some?, positive
                  LT.HdErrorNoneNil(LT.TreeLeaves(tlk, LG.Empty, inp, L.LkDir(lk)));
                }
                LL.LAAtReflOutside(tc, inp, S);
                LL.LKNodeOutside(lk, tlk, tc, tc, inp, S);
                NP.ResFromLeavesOutside(tc, LT.LK(lk, tlk, tc), inp, S);
                NP.RATransOutside(sub, tc, LT.LK(lk, tlk, tc), inp, S);
              } else {
                LL.LAAtGatePass(lk, tlk, tc, inp);
                LL.LeavesAgreeAtWeaken(LT.LK(lk, tlk, tc), tc, inp, S);
                NP.ResFromLeavesOutside(LT.LK(lk, tlk, tc), tc, inp, S);
                NP.RASymOutside(LT.LK(lk, tlk, tc), tc, inp, S);
                NP.RATransOutside(sub, tc, LT.LK(lk, tlk, tc), inp, S);
              }
            case LKFail(lk2, tlk) =>
              assert tlk == tlkc && LS.LkResult(lk, tlk, LG.Empty, inp).None?;
              assert bit != AR.PositiveL(lk);
              tstar := LT.Mismatch;
              // tr_lkfail / tr_neglkfail
              assert TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b));
              LL.LAAtGateFail(lk, tlk, inp);
              LL.LeavesAgreeAtWeaken(LT.Mismatch, LT.LKFail(lk, tlk), inp, S);
              NP.ResFromLeavesOutside(LT.Mismatch, LT.LKFail(lk, tlk), inp, S);
            case _ =>
          }
  }

  /** The fused fork lemma: at the do-while's backward fork with the walk
      allowed to exit, the (possibly transparent-headed) continuation's spec
      tree yields a checked Choice whose `Progress` wrapper is consumed by
      `tr_plus` together with the fork. Pops `Epsilon`/`Sequence`/spent
      heads; every other head shape contradicts the pinned Fork; at the
      loop-view star, the iteration is lifted to `CanExit` (`BoolFlagLift` â€”
      the engine runs it at `exit_allowed == true`) and both branches are
      built by the general construction. */
  lemma AtBackForkTreeRep(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, code: RB.code, pc: nat, inp: LC.Input, tc: LT.Tree, n: nat, S: set<LG.GroupId>)
    returns (tcstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, BS.CanExit)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, true)
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, BS.CanExit, tc)
    requires AR.BackForkAt(code, pc)
    requires CE.LkConfinedTree(tc, S)
    ensures TR.TreeRepRE(qm, LT.Progress(tcstar), code, pc, inp, true)
    ensures NP.ResAgreeAtOutside(tcstar, tc, inp, S)
    decreases CE.PSize(tc), MsizeA(acts), n, 0
  {
    var fx: int, fy: int :| NR.GetPcRE(code, pc) == Some(RB.Fork(fx, fy))
      && fx >= 0 && fy >= 0 && (fx as nat <= pc || fy as nat <= pc);
    // Accept and Jmp bottoms contradict the pinned Fork: the fuel derivation
    // must be a cons step.
    assert |acts| > 0;
    var cont := acts[1..];
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1);
    EL.PikeLkActionsTail(acts);
    assert acts == [acts[0]] + cont;
    EL.PikeLkActionsConsIff(acts[0], cont);
    match acts[0]
    case Acheck(strcheck) =>
      // a stacked check: also zero-width at the fork (EndLoop is refuted);
      // its Progress collapses into the same leaves
      assert pcmid == pc;
      assert LS.ActionsRegexSize(acts) == LS.ActionsRegexSize(cont);
      match tc {
        case Progress(tc2) =>
          WO.WalkOkAcheckBackFork(acts, code, pc, true);
          assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
          assert NB.EncOk(cont, inp, BS.CanExit) by { NB.EncOkTailCheck(acts, inp); }
          var sub := AtBackForkTreeRep(rer, qm, cont, code, pc, inp, tc2, n - 1, S);
          tcstar := sub;
          NP.RAProgressPassOutside(tc2, inp, S);
          assert NP.ResAgreeAtOutside(tcstar, tc, inp, S);
        case _ =>
      }
    case Aclose(gid) =>
      // pins SetRegisterToCP: contradiction with the Fork
      assert false;
    case Areg(r) =>
      assert EL.PikeLkRegex(r);
      match r
      case Epsilon =>
        assert pcmid == pc;
        WO.WalkOkEpsilon(acts, code, pc, true);
        assert MsizeA(cont) < MsizeA(acts);
        assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
        assert NB.EncOk(cont, inp, BS.CanExit) by { NB.EncOkTailReg(acts, inp, BS.CanExit); }
        tcstar := AtBackForkTreeRep(rer, qm, cont, code, pc, inp, tc, n - 1, S);
      case Character(cd) =>
        var ce :| NR.GetPcRE(code, pc) == Some(RB.Consume(ce)) && AR.ExpectationMatches(rer, ce, cd);
        assert false;   // Consume != Fork
      case AnchorR(la) =>
        var ra: R.anchor :| NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(ra)) && T.TrAnchor(ra) == la;
        assert false;   // AnchorAssertion != Fork
      case Disjunction(r1, r2) =>
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.Fork(pc + 1, e1 + 1))
          && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
          && NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid))
          && AR.NfaRepL(rer, qm, r2, code, e1 + 1, pcmid);
        AR.NfaRepIncrL(rer, qm, r1, code, pc + 1, e1);
        assert false;   // both arms forward: contradicts the backward arm
      case Sequence(r1, r2) =>
        EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
        EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        assert AR.ActionRepL(rer, qm, LS.Areg(r2), code, e1, pcmid);
        assert ([LS.Areg(r2)] + cont)[0] == LS.Areg(r2) && ([LS.Areg(r2)] + cont)[1..] == cont;
        FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
        assert AR.ActionsRepL(rer, qm, [LS.Areg(r2)] + cont, code, e1);
        assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc, e1);
        assert na[0] == LS.Areg(r1) && na[1..] == [LS.Areg(r2)] + cont;
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert LS.ActionsRegexSize(na) < LS.ActionsRegexSize(acts);
        assert MsizeA(na) < MsizeA(acts);
        ActionsRepLToFuel(rer, qm, na, code, pc);
        var nn: nat :| ActionsRepFuelL(rer, qm, na, code, pc, nn);
        WO.WalkOkSeq(acts, code, pc, true, r1, r2);
          assert LL.LkActsInS(na, S) by {
          LL.LkActsInSTail(acts, S);
          LL.LkActsInSCons(LS.Areg(r2), cont, S);
          LL.LkActsInSCons(LS.Areg(r1), [LS.Areg(r2)] + cont, S);
        }
        assert NB.EncOk(na, inp, BS.CanExit) by {
          var parts := [LS.Areg(r1), LS.Areg(r2)];
          assert parts + cont == na;
          if NUL.NonNullableL(acts[0].r) {
            if NUL.NonNullableL(r1) { assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
            else { assert parts[1].Areg? && NUL.NonNullableL(parts[1].r); }
          }
          NB.EncOkExpand(acts, parts, inp, BS.CanExit);
        }
        tcstar := AtBackForkTreeRep(rer, qm, na, code, pc, inp, tc, nn, S);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        if min > 0 {
          // every forced-copy head pins a clock-mark: contradiction
          match delta {
            case Inf =>
              if NUL.NonNullableL(r1) {
                var em, e1x := AR.NfaRepLPlusInv(rer, qm, greedy, min, r1, code, pc, pcmid);
                if em == pc {
                  assert false;    // SetQuantToClock != Fork
                } else {
                  var eb: nat :| (exists qid: int ::
                        NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                        && qid in qm.quants && qm.quants[qid] == gidl)
                    && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                    && AR.NfaRepMinL(rer, qm, min - 2, r1, code, eb, em);
                  assert false;    // SetQuantToClock != Fork
                }
              } else if greedy {
                // §2.5b CIN-GREEDY: a forced copy (min > 1) pins a clock-mark at
                // pc; at min == 1 the head fork is FORWARD (both arms past pc),
                // contradicting the backward arm
                var em, e1x := AR.NfaRepLCinInv(rer, qm, greedy, min, r1, code, pc, pcmid);
                if min > 1 {
                  var eb: nat :| (exists qid: int ::
                        NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                        && qid in qm.quants && qm.quants[qid] == gidl)
                    && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                    && AR.NfaRepMinL(rer, qm, min - 2, r1, code, eb, em);
                  assert false;    // SetQuantToClock != Fork
                } else {
                  assert em == pc;
                  AR.NfaRepIncrL(rer, qm, r1, code, em + 3, e1x);
                  assert NR.GetPcRE(code, pc) == Some(RB.Fork(em + 1, e1x + 2));
                  assert fx == em + 1 && fy == e1x + 2;
                  assert false;    // both arms > pc: not a backward fork
                }
              } else {
                // the GENERIC scheme (§2.5a): `min >= 1` forced copies, so `pc`
                // still carries a clock-mark -- refuted the same way
                var em, e1x := AR.NfaRepLGenInv(rer, qm, greedy, min, r1, code, pc, pcmid);
                var eb: nat :| (exists qid: int ::
                      NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                      && qid in qm.quants && qm.quants[qid] == gidl)
                  && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                  && AR.NfaRepMinL(rer, qm, min - 1, r1, code, eb, em);
                assert false;    // SetQuantToClock != Fork
              }
            case NN(kx) =>
              var em := AR.NfaRepLQuantInv(rer, qm, greedy, min, kx, r1, code, pc, pcmid);
              var eb: nat :| (exists qid: int ::
                    NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                    && qid in qm.quants && qm.quants[qid] == gidl)
                && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                && AR.NfaRepMinL(rer, qm, min - 1, r1, code, eb, em);
              assert false;      // SetQuantToClock != Fork
          }
        } else if delta.NN? {
          var k := delta.n;
          var em := AR.NfaRepLQuantInv(rer, qm, greedy, 0, k, r1, code, pc, pcmid);
          assert em == pc;
          if k == 0 {
            // spent: transparent, peel
            assert pc == pcmid;
            WO.WalkOkQuantSpent(acts, code, pc, true, greedy, r1);
            assert LS.ActionsRegexSize(cont) < LS.ActionsRegexSize(acts);
            assert MsizeA(cont) < MsizeA(acts);
            assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
            assert NB.EncOk(cont, inp, BS.CanExit) by { NB.EncOkTailReg(acts, inp, BS.CanExit); }
            tcstar := AtBackForkTreeRep(rer, qm, cont, code, pc, inp, tc, n - 1, S);
          } else {
            // a bounded layer pins a FORWARD fork: contradiction
            var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, pcmid) else RB.Fork(pcmid, pc + 1))
              && (exists qid: int ::
                    NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                    && qid in qm.quants && qm.quants[qid] == gidl)
              && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
              && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
              && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
              && AR.NfaRepOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
            AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
            AR.NfaRepIncrOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
            assert false;
          }
        } else {
          assert min == 0 && delta == LN.Inf;
          if exists e1: nat :: NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                       && (exists qid: int ::
                             NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                             && qid in qm.quants && qm.quants[qid] == gidl)
                       && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                       && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                       && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                       && pcmid == e1 + 2 {
            // the fast path pins a forward fork: contradiction
            var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
              && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
              && pcmid == e1 + 2;
            AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
            assert false;
          } else {
            // THE LOOP VIEW: the star seen from the fork itself
            AR.NfaRepLStarLoopViews(rer, qm, greedy, r1, code, pc, pcmid);
            if NUL.NonNullableL(r1) {
            var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em))
              && em <= pc
              && (exists qid: int ::
                    NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                    && qid in qm.quants && qm.quants[qid] == gidl)
              && AR.NfaRepL(rer, qm, r1, code, em + 1, pc)
              && pcmid == pc + 1;
            var qid: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
              && qid in qm.quants && qm.quants[qid] == gidl;
            var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
            assert q0 == L.Quantified(greedy, 0, LN.Inf, r1) == r;
            WO.WalkOkLoopView(acts, code, pc, true, greedy, LN.Inf, r1,
                              if greedy then em else pc + 1,
                              if greedy then pc + 1 else em, inp);
            match tc {
              case Choice(cta, ctb) =>
                var itert := if greedy then cta else ctb;
                var skipt := if greedy then ctb else cta;
                match itert {
                  case GroupActionT(g, ti) =>
                    assert g == LG.Reset(gidl);
                    var il := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
                    assert EL.BoolTreeLk(rer, il, inp, BS.CannotExit, ti);
                    // skip branch: the general construction at the exit arm
                    assert CE.PSize(skipt) < CE.PSize(tc);
                    assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
                    assert NB.EncOk(cont, inp, BS.CanExit) by { NB.EncOkTailReg(acts, inp, BS.CanExit); }
                    var subs := ActionsTreeRepFRE(rer, qm, cont, code, pc + 1, inp, BS.CanExit, skipt, n - 1, S);
                    // iteration branch: lift to CanExit (the engine keeps
                    // exit_allowed through the back edge), then construct
                    EL.PikeLkActionsConsIff(LS.Areg(q0), cont);
                    EL.PikeLkActionsConsIff(LS.Acheck(inp), [LS.Areg(q0)] + cont);
                    EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
                    assert il == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
                    assert EL.PikeLkActions(il);
                    assert CE.ShieldedActs(il) by {
                      forall i | 0 <= i < |il| && il[i].Acheck?
                        ensures exists j :: 0 <= j < i && il[j].Areg? && NUL.NonNullableL(il[j].r)
                      {
                        assert il[0] == LS.Areg(r1);
                        assert i > 0;
                        assert il[0].Areg? && NUL.NonNullableL(il[0].r);
                      }
                    }
                    CE.BoolFlagLift(rer, il, inp, ti);
                    assert EL.BoolTreeLk(rer, il, inp, BS.CanExit, ti);
                    // representation of the iteration list at em+1
                    FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                    var lq := [LS.Areg(q0)] + cont;
                    assert AR.NfaRepL(rer, qm, q0, code, pc, pc + 1) by {
                      assert NUL.NonNullableL(r1)
                        && NR.GetPcRE(code, pc)
                           == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em))
                        && em <= pc
                        && (exists qid2: int ::
                              NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid2, false))
                              && qid2 in qm.quants && qm.quants[qid2] == L.DefGroups(r1))
                        && AR.NfaRepL(rer, qm, r1, code, em + 1, pc);
                    }
                    assert AR.ActionRepL(rer, qm, LS.Areg(q0), code, pc, pc + 1);
                    assert lq[0] == LS.Areg(q0) && lq[1..] == cont;
                    assert AR.ActionsRepL(rer, qm, lq, code, pc);
                    var lc := [LS.Acheck(inp)] + lq;
                    assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, pc, pc);
                    assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
                    assert AR.ActionsRepL(rer, qm, lc, code, pc);
                    assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, em + 1, pc);
                    assert il == [LS.Areg(r1)] + lc;
                    assert il[0] == LS.Areg(r1) && il[1..] == lc;
                    assert AR.ActionsRepL(rer, qm, il, code, em + 1);
                    ActionsRepLToFuel(rer, qm, il, code, em + 1);
                    var ni: nat :| ActionsRepFuelL(rer, qm, il, code, em + 1, ni);
                    assert CE.PSize(ti) < CE.PSize(tc);
                    assert LL.LkActsInS(il, S) by {
                      LL.LkActsInSTail(acts, S);
                      assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(q0, S);
                      LL.LkActsInSCons(LS.Areg(q0), cont, S);
                      LL.LkActsInSCons(LS.Acheck(inp), [LS.Areg(q0)] + cont, S);
                      LL.LkActsInSCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont), S);
                    }
                    assert NB.EncOk(il, inp, BS.CanExit) by {
                      NB.EncodableTail(acts, inp, BS.CanExit);
                      NB.EncOkIterLift(r1, q0, cont, inp);
                    }
                    var subi := ActionsTreeRepFRE(rer, qm, il, code, em + 1, inp, BS.CanExit, ti, ni, S);
                    // assemble: tr_reset at the stamp, then tr_plus at the fork
                    var iterstar := LT.GroupActionT(g, subi);
                    assert TR.TreeRepRE(qm, iterstar, code, em, inp, true);
                    tcstar := if greedy then LT.Choice(iterstar, subs) else LT.Choice(subs, iterstar);
                    NP.RACongGroupOutside(g, subi, ti, inp, S);
                    if greedy {
                      NP.RACongChoiceOutside(iterstar, itert, subs, skipt, inp, S);
                    } else {
                      NP.RACongChoiceOutside(subs, skipt, iterstar, itert, inp, S);
                    }
                    assert TR.TreeRepRE(qm, LT.Progress(tcstar), code, pc, inp, true);
                  case _ =>
                }
              case _ =>
            }
            } else {
              // §2.5b: THE CIN LOOP VIEW — the star seen from the CIN-greedy loop's
              // backward end fork: re-entry through the clock-mark and the BeginLoop
              // (the iteration walks at CannotExit; the loop's EndLoop IS the spec's
              // check, so nothing is lifted), exit straight to e1 + 3.
              var em, e1 := AR.NfaRepLStarCinInv(rer, qm, r1, code, pc, pcmid);
              var qidC: int :| NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qidC, false))
                && NR.GetPcRE(code, e1 + 2) == Some(RB.SetQuantToClock(qidC, true))
                && qidC in qm.quants && qm.quants[qidC] == gidl
                && AR.StampBodyOk(qm, qidC, r1);
              assert greedy;
              var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
              assert q0 == L.Quantified(greedy, 0, LN.Inf, r1) == r;
              WO.WalkOkLoopViewCin(acts, code, pc, true, greedy, LN.Inf, r1, em + 1, e1 + 3, inp);
              match tc {
                case Choice(cta, ctb) =>
                  var itert := cta;
                  var skipt := ctb;
                  match itert {
                    case GroupActionT(g, ti) =>
                      assert g == LG.Reset(gidl);
                      var il := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
                      assert EL.BoolTreeLk(rer, il, inp, BS.CannotExit, ti);
                      // skip branch: the general construction at the exit arm
                      assert CE.PSize(skipt) < CE.PSize(tc);
                      assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
                      assert NB.EncOk(cont, inp, BS.CanExit) by { NB.EncOkTailReg(acts, inp, BS.CanExit); }
                      var subs := ActionsTreeRepFRE(rer, qm, cont, code, pcmid, inp, BS.CanExit, skipt, n - 1, S);
                      // iteration branch at CannotExit from the body start em + 3
                      EL.PikeLkActionsConsIff(LS.Areg(q0), cont);
                      EL.PikeLkActionsConsIff(LS.Acheck(inp), [LS.Areg(q0)] + cont);
                      EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
                      assert il == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
                      assert EL.PikeLkActions(il);
                      FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                      var lq := [LS.Areg(q0)] + cont;
                      assert AR.ActionRepL(rer, qm, LS.Areg(q0), code, pc, pcmid);
                      assert lq[0] == LS.Areg(q0) && lq[1..] == cont;
                      assert AR.ActionsRepL(rer, qm, lq, code, pc);
                      var lc := [LS.Acheck(inp)] + lq;
                      assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1, e1 + 1);
                      assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
                      assert AR.ActionsRepL(rer, qm, lc, code, e1);
                      assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, em + 3, e1);
                      assert il[0] == LS.Areg(r1) && il[1..] == lc;
                      assert AR.ActionsRepL(rer, qm, il, code, em + 3);
                      ActionsRepLToFuel(rer, qm, il, code, em + 3);
                      var ni: nat :| ActionsRepFuelL(rer, qm, il, code, em + 3, ni);
                      assert CE.PSize(ti) < CE.PSize(tc);
                      assert LL.LkActsInS(il, S) by {
                        LL.LkActsInSTail(acts, S);
                        assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(q0, S);
                        LL.LkActsInSCons(LS.Areg(q0), cont, S);
                        LL.LkActsInSCons(LS.Acheck(inp), [LS.Areg(q0)] + cont, S);
                        LL.LkActsInSCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont), S);
                      }
                      assert NB.EncOk(il, inp, BS.CannotExit) by {
                        NB.EncodableTail(acts, inp, BS.CanExit);
                        NB.EncOkIter(r1, q0, cont, inp);
                      }
                      var subi := ActionsTreeRepFRE(rer, qm, il, code, em + 3, inp, BS.CannotExit, ti, ni, S);
                      // assemble: tr_begin at em + 2, tr_reset at em + 1, tr_plus at the fork
                      assert TR.TreeRepRE(qm, subi, code, em + 2, inp, true);
                      var iterstar := LT.GroupActionT(g, subi);
                      assert TR.TreeRepRE(qm, iterstar, code, em + 1, inp, true);
                      tcstar := LT.Choice(iterstar, subs);
                      NP.RACongGroupOutside(g, subi, ti, inp, S);
                      NP.RACongChoiceOutside(iterstar, itert, subs, skipt, inp, S);
                      assert TR.TreeRepRE(qm, LT.Progress(tcstar), code, pc, inp, true);
                    case _ =>
                  }
                case _ =>
              }
            }
          }
        }
      case Group(gid, r1) =>
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid as int)))
          && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
          && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(gid as int)))
          && pcmid == e1 + 1;
        assert false;   // SetRegisterToCP != Fork
      case LookaroundR(_, _) =>    // not pike
      case Backreference(_) =>     // not pike
  }

  // The construction theorem (port of actions_tree_rep, checked form).
  /** The construction theorem: whenever action stack `acts` is
      `ActionsRepL`-represented at `pc`, walk-guarded, and its spec `BoolTree`
      is `t`, the returned checked tree is `TreeRepRE`-represented at `pc`
      and agrees with `t` on leaves. */
  lemma ActionsTreeRepRE(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, code: RB.code, pc: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTree(t, S)
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
  {
    ActionsRepLToFuel(rer, qm, acts, code, pc);
    var n: nat :| ActionsRepFuelL(rer, qm, acts, code, pc, n);
    tstar := ActionsTreeRepFRE(rer, qm, acts, code, pc, inp, b, t, n, S);
  }

  // ===========================================================================
  // L4 depth-k (ADDITIVE): the RECURSIVE-FRAGMENT engine bridge. A
  // predicate-swapped mirror of the ActionsTreeRep* family above, threading the
  // depth-k predicates PikeLkActionsRec / LkConfinedTreeK (outer) with
  // LkConfinedTreeRec look-body confinement in the POSITIVE lookaround arm. The
  // Quantified min==1 seam consumes BoolCheckInsertK. Everything else is the
  // depth-1 proof verbatim: check-insertion / back-fork / per-shape cases are
  // unchanged, since the depth-1 confinement facts still hold at the top level.
  // ===========================================================================

  /** Fuel-indexed core of the construction: from the action-stack fuel bound,
      the walk guard, and `acts`'s spec `BoolTree` `t`, CONSTRUCTS the checked
      tree `tstar` â€” `TreeRepRE`-represented at `pc` with the walk's flag, and
      leaves-agreeing with `t`. One case per `Action`/`Regex` shape; the
      do-while cases plant/dissolve the progress check as described in the
      file header. */
  // {:isolate_assertions} is LOAD-BEARING here: as one VC this lemma times out
  // past 600s (measured). It is also the package's dominant cost â€” ~4300 tiny
  // batches, ~3800 cpu-seconds â€” and the way to fix that is to decompose the
  // LEMMA (its per-shape cases into standalone lemmas with small contexts),
  // not to split the file: this single lemma owns ~98% of the file's time and
  // is mutually recursive with AtBackForkTreeRepNested, so no file split can
  // separate them.
  /** (2026-08-29 E3) the `Quantified` arm of `ActionsTreeRepFRENested`, min > 0 — extracted from a 350-line
      case so each branch is its own VC (the parent no longer needs `{:isolate_assertions}`). */
  /** (§2.5b stage 2) the CIN-GREEDY arm of `ATR_QuantMinNested`: `min - 1` forced copies,
      then the stamped end-fork loop. Extracted so the parent stays within its
      batch budget; sectioned per E3. */
  lemma ATR_QuantCinNested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, greedy: bool, min: nat, delta: LN.NoI, r1: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTreeK(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActionsRec(cont)
    requires EL.PikeLkRegexRec(L.Quantified(greedy, min, delta, r1))
    requires min > 0 && delta == LN.Inf && !NUL.NonNullableL(r1) && greedy
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0   // below `ATR_QuantMin`'s `1`
  {
    // (§2.5b) the recursive nullability predicates' definitional axioms send z3 4.14 into
    // a matching loop (as in the LiftSimCore giants): every use here is opaque, so hide them.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL, AR.NfaRepStarCinL, MsizeA;   // every recursive call below decreases on PSize alone
    assert acts == [acts[0]] + cont;
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    var gidl := L.DefGroups(r1);
          // §2.5b CIN-GREEDY: `min - 1` forced copies, then the stamped end-fork
          // loop at the head fork `em`. A forced copy peels like the do-while's;
          // at `min == 1` the head IS the fork: its loop arm is the star's
          // iteration (BeginLoop/EndLoop are the spec's `Acheck`), its skip arm
          // is the nulled-exit stamp = the VIRTUAL CHAIN of the body's first
          // empty path over the continuation (`tr_stamp`), and rung A's
          // priority theorem (`NB.CinPlusPriorityBool`) relates the two shapes.
          var em, e1x := AR.NfaRepLCinInv(rer, qm, greedy, min, r1, code, pc, pcmid);
          var qidC: int :| NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qidC, false))
            && NR.GetPcRE(code, e1x + 2) == Some(RB.SetQuantToClock(qidC, true))
            && qidC in qm.quants && qm.quants[qidC] == gidl
            && AR.StampBodyOk(qm, qidC, r1);
          AR.NfaRepIncrL(rer, qm, r1, code, em + 3, e1x);
          assert {:split_here} true;   // (E3) section: the forced copy
          if min > 1 {
            var quant1 := L.Quantified(greedy, min - 1, LN.Inf, r1);
            var eb: nat :| (exists qid2: int ::
                  NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid2, false))
                  && qid2 in qm.quants && qm.quants[qid2] == gidl)
              && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
              && AR.NfaRepMinL(rer, qm, min - 2, r1, code, eb, em);
            AR.NfaRepLCinIntro(rer, qm, greedy, min - 1, r1, code, eb, em, e1x, pcmid, qidC);
            assert AR.NfaRepL(rer, qm, quant1, code, eb, pcmid);
            match t {
              case GroupActionT(g, tc) =>
                assert g == LG.Reset(gidl);
                EL.PikeLkActionsRecConsIff(LS.Areg(quant1), cont);
                EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
                FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                assert AR.ActionRepL(rer, qm, LS.Areg(quant1), code, eb, pcmid);
                var lq1 := [LS.Areg(quant1)] + cont;
                assert lq1[0] == LS.Areg(quant1) && lq1[1..] == cont;
                assert AR.ActionsRepL(rer, qm, lq1, code, eb);
                var ia := [LS.Areg(r1)] + lq1;
                assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, eb);
                assert ia[0] == LS.Areg(r1) && ia[1..] == lq1;
                assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
                assert ia == [LS.Areg(r1), LS.Areg(quant1)] + cont;
                ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
                var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
                WO.WalkOkQuantForced(acts, code, pc, EaOf(b), greedy, min, delta, r1);
                assert CE.PSize(tc) < CE.PSize(t);
                assert LL.LkActsInS(ia, S) by {
                  LL.LkActsInSTail(acts, S);
                  assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(quant1, S);
                  LL.LkActsInSCons(LS.Areg(quant1), cont, S);
                  LL.LkActsInSCons(LS.Areg(r1), [LS.Areg(quant1)] + cont, S);
                }
                assert NB.EncOk(ia, inp, b) by {
                  var parts := [LS.Areg(r1), LS.Areg(quant1)];
                  assert parts + cont == ia;
                  if NUL.NonNullableL(acts[0].r) { reveal NUL.NonNullableL; assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
                  NB.EncOkExpand(acts, parts, inp, b);
                }
                var sub := ActionsTreeRepFRENested(rer, qm, ia, code, pc + 1, inp, b, tc, ni, S);
                tstar := LT.GroupActionT(g, sub);
                NP.RACongGroupOutside(g, sub, tc, inp, S);
              case _ =>
            }
          } else {
            // min == 1: THE CIN HEAD FORK at pc == em
            assert {:split_here} true;   // (E3) section: the head fork
            assert em == pc;
            assert greedy && delta == LN.Inf;
            var q0 := L.Quantified(greedy, 0, LN.Inf, r1);
            assert acts == [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont;
            match t {
              case GroupActionT(g, tc) =>
                assert g == LG.Reset(gidl);
                assert EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Areg(q0)] + cont, inp, b, tc);
                EL.PikeLkActionsRecConsIff(LS.Areg(q0), cont);
                EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(q0)] + cont);
                EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
                var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
                assert ia == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
                assert EL.PikeLkActionsRec(ia) && EL.PikeLkActionsRec(cont);
                // the sub-stacks' confinement and encoding
                assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
                assert LL.LkBodiesInS(r1, S);
                assert LL.LkActsInS(ia, S) by {
                  assert LL.LkBodiesInS(q0, S);
                  LL.LkActsInSCons(LS.Areg(q0), cont, S);
                  LL.LkActsInSCons(LS.Acheck(inp), [LS.Areg(q0)] + cont, S);
                  LL.LkActsInSCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont), S);
                }
                assert NB.EncOk(cont, inp, b) by {
                  assert !NUL.NonNullableL(acts[0].r) by { reveal NUL.NonNullableL; }
                  NB.EncOkTailReg(acts, inp, b);
                }
                assert NB.EncOk(ia, inp, BS.CannotExit) by {
                  NB.EncodableTail(acts, inp, b);
                  NB.EncOkIter(r1, q0, cont, inp);
                }
                // the spec trees of the iteration and of the continuation live
                // INSIDE `tc` (at the body's first empty leaf), so both are
                // PSize-smaller than `t`
                assert NP.FirstEmptyPathL(rer, r1, inp).Some? by {
                  assert NP.FirstEmptyPathA(rer, [], inp) == Some([]);
                  NP.CINullableEmptyPathA(rer, r1, [], inp);
                  assert [LS.Areg(r1)] + [] == [LS.Areg(r1)];
                }
                assert [LS.Areg(r1), LS.Areg(q0)] + cont == [LS.Areg(r1)] + ([LS.Areg(q0)] + cont);
                var tcont0 := NB.BoolTreeLkEmptyPathSub(rer, r1, [LS.Areg(q0)] + cont, inp, b, tc);
                assert FS.NoiPred(LN.Inf) == LN.Inf;
                match tcont0 {
                  case Choice(ta, tb) =>
                    var ti: LT.Tree := *;
                    match ta {
                      case GroupActionT(g2, ti2) =>
                        assert g2 == LG.Reset(gidl);
                        ti := ti2;
                      case _ => assert false;
                    }
                    var tcont := tb;
                    assert EL.BoolTreeLk(rer, ia, inp, BS.CannotExit, ti);
                    assert EL.BoolTreeLk(rer, cont, inp, b, tcont);
                    assert CE.PSize(ti) < CE.PSize(t) && CE.PSize(tcont) < CE.PSize(t);
                    assert CE.LkConfinedTreeK(tc, S);
                    assert CE.LkConfinedTreeK(tcont0, S);
                    assert tcont0 == LT.Choice(ta, tb);
                    assert CE.LkConfinedTreeK(ta, S) && CE.LkConfinedTreeK(tb, S);
                    assert ta.GroupActionT? && ti == ta.t;
                    assert CE.LkConfinedTreeK(ti, S) && CE.LkConfinedTreeK(tcont, S);
                    assert {:split_here} true;   // (E3) section: representation
                    // representation of the two lists: the loop body at em + 3
                    // (EndLoop at e1x, the CIN loop view of the star at e1x + 1),
                    // the continuation at pcmid == e1x + 3
                    FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                    AR.NfaRepLStarCinIntro(rer, qm, r1, code, em, e1x, qidC);
                    assert AR.ActionRepL(rer, qm, LS.Areg(q0), code, e1x + 1, pcmid);
                    var lq := [LS.Areg(q0)] + cont;
                    assert lq[0] == LS.Areg(q0) && lq[1..] == cont;
                    assert AR.ActionsRepL(rer, qm, lq, code, e1x + 1);
                    var lc := [LS.Acheck(inp)] + lq;
                    assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1x, e1x + 1);
                    assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
                    assert AR.ActionsRepL(rer, qm, lc, code, e1x);
                    assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, em + 3, e1x);
                    assert ia[0] == LS.Areg(r1) && ia[1..] == lc;
                    assert AR.ActionsRepL(rer, qm, ia, code, em + 3);
                    ActionsRepLToFuel(rer, qm, ia, code, em + 3);
                    var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, em + 3, ni);
                    // the walk guard's CIN head arm
                    WO.WalkOkQuantCinHead(acts, code, pc, EaOf(b), greedy, min, delta, r1, em + 1, e1x + 2, inp);
                    var subi := ActionsTreeRepFRENested(rer, qm, ia, code, em + 3, inp, BS.CannotExit, ti, ni, S);
                    var subc := ActionsTreeRepFRENested(rer, qm, cont, code, pcmid, inp, b, tcont, n - 1, S);
                    assert {:split_here} true;   // (E3) section: assembly
                    // loop arm: tr_begin at em + 2, tr_reset at em + 1
                    assert TR.TreeRepRE(qm, subi, code, em + 2, inp, EaOf(b));
                    var tloop := LT.GroupActionT(LG.Reset(gidl), subi);
                    assert TR.TreeRepRE(qm, tloop, code, em + 1, inp, EaOf(b));
                    // skip arm: tr_stamp at e1x + 2 — the virtual chain of the
                    // body's first empty path, read off the oracle bits and tied
                    // to the spec path by rung B's `FirstEmptyPathRL`
                    assert LL.OracleOkAt(rer, qm, inp);
                    NT.FirstEmptyPathRL(rer, qm, qm.bodies[qidC], inp);
                    var p := NP.FirstEmptyPathL(rer, r1, inp).value;
                    assert TR.FirstEmptyPathR(qm, qm.bodies[qidC], inp) == Some(p);
                    var tskip := LT.GroupActionT(LG.Reset(gidl), TR.ChainT(p, subc));
                    assert TR.TreeRepRE(qm, tskip, code, e1x + 2, inp, EaOf(b)) by {
                      TR.PeelChainT(p, subc);
                      assert TR.StampShape(qm, qidC, tskip);
                      assert TR.PeelT(p, tskip.t) == Some(subc);
                      assert TR.TreeRepRE(qm, subc, code, e1x + 3, inp, EaOf(b));
                    }
                    tstar := LT.Choice(tloop, tskip);
                    assert TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b));   // tr_choice at the head fork
                    assert {:split_here} true;   // (E3) section: the relation
                    // the relation: rung A's theorem on the spec side, congruences on ours
                    NB.CinPlusPriorityBool(rer, r1, cont, inp, b, S, t, ti, tcont);
                    var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), ti),
                                          LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont)));
                    NB.ChainTEqChain(p, subc);
                    NB.RACongChainOutside(p, subc, tcont, inp, S);
                    NP.RACongGroupOutside(LG.Reset(gidl), subi, ti, inp, S);
                    NP.RACongGroupOutside(LG.Reset(gidl), NP.Chain(p, subc), NP.Chain(p, tcont), inp, S);
                    NP.RACongChoiceOutside(tloop, LT.GroupActionT(LG.Reset(gidl), ti),
                                           tskip, LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont)), inp, S);
                    NP.RATransOutside(tstar, tcin, t, inp, S);
                  case _ => assert false;
                }
              case _ =>
            }
          }
  }

  lemma ATR_QuantMinNested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, greedy: bool, min: nat, delta: LN.NoI, r1: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTreeK(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActionsRec(cont)
    requires EL.PikeLkRegexRec(L.Quantified(greedy, min, delta, r1))
    requires min > 0
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 1
  {
    // (§2.5b) hide the recursive nullability predicates (z3 4.14 matching loop; every use is opaque)
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL, AR.NfaRepStarCinL;
    assert acts == [acts[0]] + cont;
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    var gidl := L.DefGroups(r1);
    match delta {
      case Inf =>
        // the do-while: min-1 forced copies, the stamp, the body, the
        // backward fork
        if !NUL.NonNullableL(r1) {
          if !greedy {
          // §2.5a GENERIC (lazy): `min` forced copies, then the ordinary star loop at
          // `em`. Unlike the do-while there is NO seam -- the code's
          // BeginLoop/EndLoop sits exactly where the spec's `Acheck` is -- so
          // nothing has to be inserted with `CE.BoolCheckInsert` and this arm
          // needs no nullability hypothesis at all.
          var em, e1x := AR.NfaRepLGenInv(rer, qm, greedy, min, r1, code, pc, pcmid);
          var qidL: int :| NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qidL, false))
            && qidL in qm.quants && qm.quants[qidL] == gidl;
          AR.NfaRepIncrL(rer, qm, r1, code, em + 3, e1x);
          var quant1 := L.Quantified(greedy, min - 1, LN.Inf, r1);
          var eb: nat :| (exists qid2: int ::
                NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid2, false))
                && qid2 in qm.quants && qm.quants[qid2] == gidl)
            && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
            && AR.NfaRepMinL(rer, qm, min - 1, r1, code, eb, em);
          if min > 1 {
            // the residual is the same GENERIC shape with one copy fewer
            AR.NfaRepLGenIntro(rer, qm, greedy, min - 1, r1, code, eb, em, e1x, pcmid, qidL);
          } else {
            // min == 1: `NfaRepMinL(0, …)` forces `eb == em`, and the loop at
            // `em` IS `NfaRepL`'s `min == 0 && Inf` (star) arm, verbatim
            assert eb == em;
          }
          assert AR.NfaRepL(rer, qm, quant1, code, eb, pcmid);
          match t {
            case GroupActionT(g, tc) =>
              assert g == LG.Reset(gidl);
              EL.PikeLkActionsRecConsIff(LS.Areg(quant1), cont);
              EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
              FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              assert AR.ActionRepL(rer, qm, LS.Areg(quant1), code, eb, pcmid);
              var lq1 := [LS.Areg(quant1)] + cont;
              assert lq1[0] == LS.Areg(quant1) && lq1[1..] == cont;
              assert AR.ActionsRepL(rer, qm, lq1, code, eb);
              var ia := [LS.Areg(r1)] + lq1;
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, eb);
              assert ia[0] == LS.Areg(r1) && ia[1..] == lq1;
              assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
              assert ia == [LS.Areg(r1), LS.Areg(quant1)] + cont;
              ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
              var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
              WO.WalkOkQuantForced(acts, code, pc, EaOf(b), greedy, min, delta, r1);
              assert CE.PSize(tc) < CE.PSize(t);
              assert LL.LkActsInS(ia, S) by {
                LL.LkActsInSTail(acts, S);
                assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(quant1, S);
                LL.LkActsInSCons(LS.Areg(quant1), cont, S);
                LL.LkActsInSCons(LS.Areg(r1), [LS.Areg(quant1)] + cont, S);
              }
              assert NB.EncOk(ia, inp, b) by {
                var parts := [LS.Areg(r1), LS.Areg(quant1)];
                assert parts + cont == ia;
                if NUL.NonNullableL(acts[0].r) { reveal NUL.NonNullableL; assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
                NB.EncOkExpand(acts, parts, inp, b);
              }
              var sub := ActionsTreeRepFRENested(rer, qm, ia, code, pc + 1, inp, b, tc, ni, S);
              tstar := LT.GroupActionT(g, sub);
              NP.RACongGroupOutside(g, sub, tc, inp, S);
            case _ =>
          }
          } else {
            tstar := ATR_QuantCinNested(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, greedy, min, delta, r1, S);
          }
        } else {
          assert {:split_here} true;   // (E3) section: the do-while arm
          var em, e1x := AR.NfaRepLPlusInv(rer, qm, greedy, min, r1, code, pc, pcmid);
          assert NUL.NonNullableL(r1);
          var qid: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
            && qid in qm.quants && qm.quants[qid] == gidl;
          AR.NfaRepIncrL(rer, qm, r1, code, em + 1, e1x);
          if min > 1 {
          // a forced copy: stamp at pc, body at pc+1, the smaller
          // do-while continues at eb
          var quant1 := L.Quantified(greedy, min - 1, LN.Inf, r1);
          var eb: nat :| (exists qid2: int ::
                NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid2, false))
                && qid2 in qm.quants && qm.quants[qid2] == gidl)
            && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
            && AR.NfaRepMinL(rer, qm, min - 2, r1, code, eb, em);
          AR.NfaRepLPlusIntro(rer, qm, greedy, min - 1, r1, code, eb, em, e1x, pcmid, qid);
          assert AR.NfaRepL(rer, qm, quant1, code, eb, pcmid);
          match t {
            case GroupActionT(g, tc) =>
              assert g == LG.Reset(gidl);
              EL.PikeLkActionsRecConsIff(LS.Areg(quant1), cont);
              EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
              FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              assert AR.ActionRepL(rer, qm, LS.Areg(quant1), code, eb, pcmid);
              var lq1 := [LS.Areg(quant1)] + cont;
              assert lq1[0] == LS.Areg(quant1) && lq1[1..] == cont;
              assert AR.ActionsRepL(rer, qm, lq1, code, eb);
              var ia := [LS.Areg(r1)] + lq1;
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, eb);
              assert ia[0] == LS.Areg(r1) && ia[1..] == lq1;
              assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
              assert ia == [LS.Areg(r1), LS.Areg(quant1)] + cont;
              ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
              var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
              WO.WalkOkQuantForced(acts, code, pc, EaOf(b), greedy, min, delta, r1);
              assert CE.PSize(tc) < CE.PSize(t);
              assert LL.LkActsInS(ia, S) by {
                LL.LkActsInSTail(acts, S);
                assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(quant1, S);
                LL.LkActsInSCons(LS.Areg(quant1), cont, S);
                LL.LkActsInSCons(LS.Areg(r1), [LS.Areg(quant1)] + cont, S);
              }
              assert NB.EncOk(ia, inp, b) by {
                var parts := [LS.Areg(r1), LS.Areg(quant1)];
                assert parts + cont == ia;
                if NUL.NonNullableL(acts[0].r) { reveal NUL.NonNullableL; assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
                NB.EncOkExpand(acts, parts, inp, b);
              }
              var sub := ActionsTreeRepFRENested(rer, qm, ia, code, pc + 1, inp, b, tc, ni, S);
              tstar := LT.GroupActionT(g, sub);
              // tr_reset at pc (the copy's clock-mark carries the Reset)
              NP.RACongGroupOutside(g, sub, tc, inp, S);
            case _ =>
          }
        } else {
          // min == 1: THE SEAM. The stamp is at pc (== em); the spec
          // walk has no check after this last forced body â€” insert it.
          assert em == pc;
          var q0 := L.Quantified(greedy, 0, LN.Inf, r1);
          match t {
            case GroupActionT(g, tc) =>
              assert g == LG.Reset(gidl);
              assert EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Areg(q0)] + cont, inp, b, tc);
              var pre := [LS.Areg(r1)];
              var rest := [LS.Areg(q0)] + cont;
              EL.PikeLkActionsRecConsIff(LS.Areg(q0), cont);
              EL.PikeLkActionsRecConsIff(LS.Areg(r1), rest);
              assert EL.PikeLkActionsRec(pre) by {
                assert pre == [LS.Areg(r1)] + [];
                EL.PikeLkActionsRecConsIff(LS.Areg(r1), []);
              }
              assert pre + rest == [LS.Areg(r1), LS.Areg(q0)] + cont;
              assert CE.ConsumesBeforeAreg(pre) by {
                assert pre[0].Areg? && NUL.NonNullableL(pre[0].r);
              }
              var t1ck := CE.BoolCheckInsertK(rer, pre, inp, rest, inp, b, tc);
              assert CE.LkConfinedTreeK(t1ck, S);   // BoolCheckInsert preserves it from LkConfinedTree(tc, S)
              var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
              assert ia == pre + [LS.Acheck(inp)] + rest;
              assert EL.BoolTreeLk(rer, ia, inp, b, t1ck);
              // representation of the checked list at pc+1: the body,
              // the zero-width check at the fork, the loop view
              assert AR.BackForkAt(code, e1x) by {
                assert NR.GetPcRE(code, e1x)
                    == Some(if greedy then RB.Fork(em, e1x + 1) else RB.Fork(e1x + 1, em));
                assert em <= e1x;
              }
              assert AR.NfaRepL(rer, qm, q0, code, e1x, e1x + 1) by {
                assert NUL.NonNullableL(r1)
                  && NR.GetPcRE(code, e1x)
                     == Some(if greedy then RB.Fork(em, e1x + 1) else RB.Fork(e1x + 1, em))
                  && em <= e1x
                  && (exists qid2: int ::
                        NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid2, false))
                        && qid2 in qm.quants && qm.quants[qid2] == L.DefGroups(r1))
                  && AR.NfaRepL(rer, qm, r1, code, em + 1, e1x);
              }
              FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              var lq := [LS.Areg(q0)] + cont;
              assert AR.ActionRepL(rer, qm, LS.Areg(q0), code, e1x, e1x + 1);
              assert lq[0] == LS.Areg(q0) && lq[1..] == cont;
              assert AR.ActionsRepL(rer, qm, lq, code, e1x);
              var lc := [LS.Acheck(inp)] + lq;
              EL.PikeLkActionsRecConsIff(LS.Acheck(inp), lq);
              assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1x, e1x);
              assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
              assert AR.ActionsRepL(rer, qm, lc, code, e1x);
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, e1x);
              assert ia == [LS.Areg(r1)] + lc;
              assert ia[0] == LS.Areg(r1) && ia[1..] == lc;
              assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
              EL.PikeLkActionsRecConsIff(LS.Areg(r1), lc);
              assert EL.PikeLkActionsRec(ia);
              ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
              var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
              WO.WalkOkQuantSeam(acts, code, pc, EaOf(b), greedy, r1, inp);
              assert CE.PSize(t1ck) == CE.PSize(tc);
              assert CE.PSize(t1ck) < CE.PSize(t);
              assert LL.LkActsInS(ia, S) by {
                LL.LkActsInSTail(acts, S);
                assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(q0, S);
                LL.LkActsInSCons(LS.Areg(q0), cont, S);
                LL.LkActsInSCons(LS.Acheck(inp), [LS.Areg(q0)] + cont, S);
                LL.LkActsInSCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont), S);
                assert ia == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
              }
              assert NB.EncOk(ia, inp, b) by {
                NB.EncodableTail(acts, inp, b);
                if b == BS.CannotExit { NB.EncOkIter(r1, q0, cont, inp); }
                else { NB.EncOkIterLift(r1, q0, cont, inp); }
              }
              var sub := ActionsTreeRepFRENested(rer, qm, ia, code, pc + 1, inp, b, t1ck, ni, S);
              tstar := LT.GroupActionT(g, sub);
              // tr_reset at pc (the do-while stamp; the VM's
              // SetQuantToClock preserves exit_allowed, so b carries)
              assert LL.LeavesAgreeAtOutside(t1ck, tc, inp, S);
              NP.ResFromLeavesOutside(t1ck, tc, inp, S);
              NP.RATransOutside(sub, t1ck, tc, inp, S);
              NP.RACongGroupOutside(g, sub, tc, inp, S);
            case _ =>
          }
        }
        }
      case NN(kx) =>
        assert {:split_here} true;   // (E3) section: the bounded arm
        var em := AR.NfaRepLQuantInv(rer, qm, greedy, min, kx, r1, code, pc, pcmid);
        var quant1 := L.Quantified(greedy, min - 1, delta, r1);
        var eb: nat :| (exists qid: int ::
              NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
              && qid in qm.quants && qm.quants[qid] == gidl)
          && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
          && AR.NfaRepMinL(rer, qm, min - 1, r1, code, eb, em);
        AR.NfaRepLQuantIntro(rer, qm, greedy, min - 1, kx, r1, code, eb, em, pcmid);
        assert AR.NfaRepL(rer, qm, quant1, code, eb, pcmid);
        match t {
          case GroupActionT(g, tc) =>
            assert g == LG.Reset(gidl);
            EL.PikeLkActionsRecConsIff(LS.Areg(quant1), cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
            FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
            assert AR.ActionRepL(rer, qm, LS.Areg(quant1), code, eb, pcmid);
            var lq1 := [LS.Areg(quant1)] + cont;
            assert lq1[0] == LS.Areg(quant1) && lq1[1..] == cont;
            assert AR.ActionsRepL(rer, qm, lq1, code, eb);
            var ia := [LS.Areg(r1)] + lq1;
            assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, eb);
            assert ia[0] == LS.Areg(r1) && ia[1..] == lq1;
            assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
            assert ia == [LS.Areg(r1), LS.Areg(quant1)] + cont;
            ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
            var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
              WO.WalkOkQuantForced(acts, code, pc, EaOf(b), greedy, min, delta, r1);
            assert CE.PSize(tc) < CE.PSize(t);
            assert LL.LkActsInS(ia, S) by {
              LL.LkActsInSTail(acts, S);
              assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(quant1, S);
              LL.LkActsInSCons(LS.Areg(quant1), cont, S);
              LL.LkActsInSCons(LS.Areg(r1), [LS.Areg(quant1)] + cont, S);
            }
            assert NB.EncOk(ia, inp, b) by {
              var parts := [LS.Areg(r1), LS.Areg(quant1)];
              assert parts + cont == ia;
              if NUL.NonNullableL(acts[0].r) { reveal NUL.NonNullableL; assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
              NB.EncOkExpand(acts, parts, inp, b);
            }
            var sub := ActionsTreeRepFRENested(rer, qm, ia, code, pc + 1, inp, b, tc, ni, S);
            tstar := LT.GroupActionT(g, sub);
            // tr_reset at pc (the clock-mark carries the Reset node)
            NP.RACongGroupOutside(g, sub, tc, inp, S);
          case _ =>
        }
    }
  }

  /** (2026-08-29 E3) the `Quantified` arm of `ActionsTreeRepFRENested`, min == 0 && delta.NN? — extracted from a 350-line
      case so each branch is its own VC (the parent no longer needs `{:isolate_assertions}`). */
  lemma ATR_QuantNNNested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, greedy: bool, min: nat, delta: LN.NoI, r1: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTreeK(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActionsRec(cont)
    requires EL.PikeLkRegexRec(L.Quantified(greedy, min, delta, r1))
    requires min == 0 && delta.NN?
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 1
  {
    assert acts == [acts[0]] + cont;
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    var gidl := L.DefGroups(r1);
    // min == 0, bounded delta: spent (k == 0) or one optional layer
    var k := delta.n;
    var em := AR.NfaRepLQuantInv(rer, qm, greedy, 0, k, r1, code, pc, pcmid);
    assert em == pc;   // the forced chain is empty
    if k == 0 {
      // spent quantifier: no code, epsilon-continue with cont
      assert pc == pcmid;
      WO.WalkOkQuantSpent(acts, code, pc, EaOf(b), greedy, r1);
      assert LS.ActionsRegexSize(cont) < LS.ActionsRegexSize(acts);
      assert MsizeA(cont) < MsizeA(acts);
      assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
      assert NB.EncOk(cont, inp, b) by { NB.EncOkTailReg(acts, inp, b); }
      tstar := ActionsTreeRepFRENested(rer, qm, cont, code, pcmid, inp, b, t, n - 1, S);
    } else {
      // one bounded layer: the fork skips to the common end pcmid
      var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
      assert quant == L.Quantified(greedy, 0, LN.NN(k - 1), r1);
      var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, pcmid) else RB.Fork(pcmid, pc + 1))
        && (exists qid: int ::
              NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
              && qid in qm.quants && qm.quants[qid] == gidl)
        && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
        && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && AR.NfaRepOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
      AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
      AR.NfaRepIncrOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
      match t {
        case Choice(ta, tb) =>
          var itert := if greedy then ta else tb;
          var skipt := if greedy then tb else ta;
          match itert {
            case GroupActionT(g, ti) =>
              assert g == LG.Reset(gidl);
              WO.WalkOkQuantLayer(acts, code, pc, EaOf(b), greedy, delta, r1,
                                  if greedy then pc + 1 else pcmid,
                                  if greedy then pcmid else pc + 1, inp);
              // skip branch: cont at the common end pcmid
              assert CE.PSize(skipt) < CE.PSize(t);
              assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
              assert NB.EncOk(cont, inp, b) by { NB.EncOkTailReg(acts, inp, b); }
              var subs := ActionsTreeRepFRENested(rer, qm, cont, code, pcmid, inp, b, skipt, n - 1, S);
              // iteration branch at pc+3 with the NN(k-1) continuation at e1+1
              EL.PikeLkActionsRecConsIff(LS.Areg(quant), cont);
              EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(quant)] + cont);
              EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
              FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              var lq := [LS.Areg(quant)] + cont;
              assert AR.NfaRepMinL(rer, qm, 0, r1, code, e1 + 1, e1 + 1);
              AR.NfaRepLQuantIntro(rer, qm, greedy, 0, k - 1, r1, code, e1 + 1, e1 + 1, pcmid);
              assert AR.ActionRepL(rer, qm, LS.Areg(quant), code, e1 + 1, pcmid);
              assert lq[0] == LS.Areg(quant) && lq[1..] == cont;
              assert AR.ActionsRepL(rer, qm, lq, code, e1 + 1);
              // Acheck as the fall-through EndLoop onto the next layer
              var lc := [LS.Acheck(inp)] + lq;
              assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1, e1 + 1);
              assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
              assert AR.ActionsRepL(rer, qm, lc, code, e1);
              var ia := [LS.Areg(r1)] + lc;
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 3, e1);
              assert ia[0] == LS.Areg(r1) && ia[1..] == lc;
              assert AR.ActionsRepL(rer, qm, ia, code, pc + 3);
              assert ia == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
              ActionsRepLToFuel(rer, qm, ia, code, pc + 3);
              var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, pc + 3, ni);
              assert CE.PSize(ti) < CE.PSize(t);
              assert LL.LkActsInS(ia, S) by {
                LL.LkActsInSTail(acts, S);
                assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(quant, S);
                LL.LkActsInSCons(LS.Areg(quant), cont, S);
                LL.LkActsInSCons(LS.Acheck(inp), lq, S);
                LL.LkActsInSCons(LS.Areg(r1), lc, S);
              }
              assert NB.EncOk(ia, inp, BS.CannotExit) by {
                NB.EncodableTail(acts, inp, b);
                NB.EncOkIter(r1, quant, cont, inp);
              }
              var subi := ActionsTreeRepFRENested(rer, qm, ia, code, pc + 3, inp, BS.CannotExit, ti, ni, S);
              // assemble: subi at pc+3 (false) -> tr_begin at pc+2 ->
              // tr_reset at pc+1 -> tr_choice with the skip at pcmid
              assert TR.TreeRepRE(qm, subi, code, pc + 3, inp, false);
              assert TR.TreeRepRE(qm, subi, code, pc + 2, inp, EaOf(b));
              var iterstar := LT.GroupActionT(g, subi);
              assert TR.TreeRepRE(qm, iterstar, code, pc + 1, inp, EaOf(b));
              tstar := if greedy then LT.Choice(iterstar, subs) else LT.Choice(subs, iterstar);
              NP.RACongGroupOutside(g, subi, ti, inp, S);
              if greedy {
                NP.RACongChoiceOutside(iterstar, itert, subs, skipt, inp, S);
              } else {
                NP.RACongChoiceOutside(subs, skipt, iterstar, itert, inp, S);
              }
              assert TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b));
            case _ =>
          }
        case _ =>
      }
    }
  }

  /** (2026-08-29 E3) the `Quantified` arm of `ActionsTreeRepFRENested`, min == 0 && delta == LN.Inf — extracted from a 350-line
      case so each branch is its own VC (the parent no longer needs `{:isolate_assertions}`). */
  lemma ATR_QuantStarNested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, greedy: bool, min: nat, delta: LN.NoI, r1: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTreeK(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActionsRec(cont)
    requires EL.PikeLkRegexRec(L.Quantified(greedy, min, delta, r1))
    requires min == 0 && delta == LN.Inf
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 1
  {
    assert acts == [acts[0]] + cont;
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    var gidl := L.DefGroups(r1);
    assert min == 0 && delta == LN.Inf;
    var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
    assert quant == L.Quantified(greedy, 0, LN.Inf, r1) == L.Quantified(greedy, min, delta, r1);
    if exists e1: nat :: NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                 && (exists qid: int ::
                       NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                       && qid in qm.quants && qm.quants[qid] == gidl)
                 && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                 && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                 && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                 && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                 && pcmid == e1 + 2 {
      // the star FAST PATH (forward decision point)
      var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                   && (exists qid: int ::
                         NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                         && qid in qm.quants && qm.quants[qid] == gidl)
                   && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                   && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                   && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                   && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                   && pcmid == e1 + 2;
      AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
      match t {
        case Choice(ta, tb) =>
          var itert := if greedy then ta else tb;
          var skipt := if greedy then tb else ta;
          match itert {
            case GroupActionT(g, ti) =>
              assert g == LG.Reset(gidl);
              WO.WalkOkQuantLayer(acts, code, pc, EaOf(b), greedy, delta, r1,
                                  if greedy then pc + 1 else pcmid,
                                  if greedy then pcmid else pc + 1, inp);
              // skip branch at pcmid == e1+2
              assert CE.PSize(skipt) < CE.PSize(t);
              assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
              assert NB.EncOk(cont, inp, b) by { NB.EncOkTailReg(acts, inp, b); }
              var subs := ActionsTreeRepFRENested(rer, qm, cont, code, pcmid, inp, b, skipt, n - 1, S);
              // iteration branch: [Areg r1, Acheck inp, Areg quant] + cont at pc+3
              EL.PikeLkActionsRecConsIff(LS.Areg(quant), cont);
              EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(quant)] + cont);
              EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
              FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              // [Areg quant]+cont at pc (the star block itself, ending at pcmid)
              var lq := [LS.Areg(quant)] + cont;
              assert AR.ActionRepL(rer, qm, LS.Areg(quant), code, pc, pcmid);
              assert lq[0] == LS.Areg(quant) && lq[1..] == cont;
              assert AR.ActionsRepL(rer, qm, lq, code, pc);
              // absorbed back-jump: lq at e1+1 via jump_bc
              AR.ActionsRepLJmp(rer, qm, lq, code, e1 + 1, pc);
              // [Acheck inp]+lq at e1 (fall-through EndLoop)
              var lc := [LS.Acheck(inp)] + lq;
              assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1, e1 + 1);
              assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
              assert AR.ActionsRepL(rer, qm, lc, code, e1);
              // [Areg r1]+lc at pc+3
              var ia := [LS.Areg(r1)] + lc;
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 3, e1);
              assert ia[0] == LS.Areg(r1) && ia[1..] == lc;
              assert AR.ActionsRepL(rer, qm, ia, code, pc + 3);
              assert ia == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
              ActionsRepLToFuel(rer, qm, ia, code, pc + 3);
              var ni: nat :| ActionsRepFuelL(rer, qm, ia, code, pc + 3, ni);
              assert CE.PSize(ti) < CE.PSize(t);
              assert LL.LkActsInS(ia, S) by {
                LL.LkActsInSTail(acts, S);
                assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(quant, S);
                LL.LkActsInSCons(LS.Areg(quant), cont, S);
                LL.LkActsInSCons(LS.Acheck(inp), lq, S);
                LL.LkActsInSCons(LS.Areg(r1), lc, S);
              }
              assert NB.EncOk(ia, inp, BS.CannotExit) by {
                NB.EncodableTail(acts, inp, b);
                NB.EncOkIter(r1, quant, cont, inp);
              }
              var subi := ActionsTreeRepFRENested(rer, qm, ia, code, pc + 3, inp, BS.CannotExit, ti, ni, S);
              // assemble: subi at pc+3 (false) â†’ tr_begin at pc+2 (any b) â†’
              // tr_reset at pc+1 (consumes the Reset node at b) â†’ tr_choice
              assert TR.TreeRepRE(qm, subi, code, pc + 3, inp, false);
              assert TR.TreeRepRE(qm, subi, code, pc + 2, inp, EaOf(b));
              var iterstar := LT.GroupActionT(g, subi);
              assert TR.TreeRepRE(qm, iterstar, code, pc + 1, inp, EaOf(b));
              tstar := if greedy then LT.Choice(iterstar, subs) else LT.Choice(subs, iterstar);
              NP.RACongGroupOutside(g, subi, ti, inp, S);
              if greedy {
                NP.RACongChoiceOutside(iterstar, itert, subs, skipt, inp, S);
              } else {
                NP.RACongChoiceOutside(subs, skipt, iterstar, itert, inp, S);
              }
              assert TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b));
            case _ =>
          }
        case _ =>
      }
    } else {
      // the LOOP VIEW: a bare star at the do-while's backward fork.
      // WalkOk pins the flag to CanExit; the whole configuration is
      // delegated to the fused fork lemma, and the extra Progress it
      // returns is invisible to the leaves.
      AR.NfaRepLStarLoopViews(rer, qm, greedy, r1, code, pc, pcmid);
      if NUL.NonNullableL(r1) {
        var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em))
          && em <= pc
          && (exists qid: int ::
                NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                && qid in qm.quants && qm.quants[qid] == gidl)
          && AR.NfaRepL(rer, qm, r1, code, em + 1, pc)
          && pcmid == pc + 1;
        WO.WalkOkLoopView(acts, code, pc, EaOf(b), greedy, LN.Inf, r1,
                          if greedy then em else pc + 1,
                          if greedy then pc + 1 else em, inp);
      } else {
        // §2.5b: the CIN loop view (a greedy star at the CIN loop's end fork)
        var em, e1 := AR.NfaRepLStarCinInv(rer, qm, r1, code, pc, pcmid);
        WO.WalkOkLoopView(acts, code, pc, EaOf(b), greedy, LN.Inf, r1, em + 1, e1 + 3, inp);
      }
      assert EaOf(b) == true;
      assert b == BS.CanExit;
      assert AR.BackForkAt(code, pc);
      var sub := AtBackForkTreeRepNested(rer, qm, acts, code, pc, inp, t, n, S);
      tstar := LT.Progress(sub);
      NP.RAProgressPassOutside(sub, inp, S);
      assert NP.ResAgreeAtOutside(tstar, t, inp, S);
  }
  }

  lemma ActionsTreeRepFRENested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, code: RB.code, pc: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTreeK(t, S)
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 2
  {
    if |acts| == 0 && NR.GetPcRE(code, pc) == Some(RB.Accept) {
      assert t == LT.Match;
      tstar := LT.Match;
    } else if exists pcstart: nat :: NR.GetPcRE(code, pc) == Some(RB.Jmp(pcstart)) && ActionsRepFuelL(rer, qm, acts, code, pcstart, n - 1) {
      var pcstart: nat :| NR.GetPcRE(code, pc) == Some(RB.Jmp(pcstart)) && ActionsRepFuelL(rer, qm, acts, code, pcstart, n - 1);
      WO.WalkOkJmp(acts, code, pc, EaOf(b), pcstart);
      tstar := ActionsTreeRepFRENested(rer, qm, acts, code, pcstart, inp, b, t, n - 1, S);
      // tr_jmp
      assert TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b));
    } else {
      var cont := acts[1..];
      var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1);
      EL.PikeLkActionsRecTail(acts);
      assert acts == [acts[0]] + cont;
      EL.PikeLkActionsRecConsIff(acts[0], cont);
      match acts[0]
      case Acheck(strcheck) =>
        tstar := ATR_AcheckNested(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, S);
      case Aclose(gid) =>
        tstar := ATR_AcloseNested(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, gid, S);
      case Areg(r) =>
        assert EL.PikeLkRegexRec(r);
        match r
        case Epsilon =>
          tstar := ATR_EpsilonNested(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, S);
        case Character(cd) =>
          tstar := ATR_CharacterNested(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, cd, S);
        case Disjunction(r1, r2) =>
          tstar := ATR_DisjunctionNested(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, r1, r2, S);
        case Sequence(r1, r2) =>
          tstar := ATR_SequenceNested(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, r1, r2, S);
        case Quantified(greedy, min, delta, r1) => {
          if min > 0 { tstar := ATR_QuantMinNested(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, greedy, min, delta, r1, S); }
          else if delta.NN? { tstar := ATR_QuantNNNested(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, greedy, min, delta, r1, S); }
          else { tstar := ATR_QuantStarNested(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, greedy, min, delta, r1, S); }
        }
        case Group(gid, r1) =>
          tstar := ATR_GroupNested(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, gid, r1, S);
        case AnchorR(la) =>
          tstar := ATR_AnchorRNested(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, la, S);
        case LookaroundR(lk, r1) =>
          tstar := ATR_LookaroundRNested(rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, lk, r1, S);
        case Backreference(gid) =>   // not pike
    }
  }

  lemma ATR_AcheckNested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTreeK(t, S)
    requires |acts| > 0 && acts[0].Acheck?
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActionsRec(cont)
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
        assert LS.ActionsRegexSize(acts) == LS.ActionsRegexSize(cont);
        if NR.GetPcRE(code, pc) == Some(RB.EndLoop) {
          assert pcmid == pc + 1;
          if b == BS.CanExit {
            match t {
              case Progress(tc) =>
                WO.WalkOkAcheckEndLoop(acts, code, pc, EaOf(b));
                assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
                assert NB.EncOk(cont, inp, BS.CanExit) by { NB.EncOkTailCheck(acts, inp); }
                var sub := ActionsTreeRepFRENested(rer, qm, cont, code, pc + 1, inp, BS.CanExit, tc, n - 1, S);
                tstar := LT.Progress(sub);
                // tr_progress (fall-through EndLoop)
                NP.RACongProgressOutside(sub, tc, inp, S);
              case _ =>
            }
          } else {
            // t == Mismatch: tr_progressfail
            tstar := LT.Mismatch;
          }
        } else {
          // the zero-width check at the do-while's backward fork
          assert AR.BackForkAt(code, pc) && pcmid == pc;
          if b == BS.CanExit {
            match t {
              case Progress(tc) =>
                WO.WalkOkAcheckBackFork(acts, code, pc, EaOf(b));
                assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
                assert NB.EncOk(cont, inp, BS.CanExit) by { NB.EncOkTailCheck(acts, inp); }
                var sub := AtBackForkTreeRepNested(rer, qm, cont, code, pc, inp, tc, n - 1, S);
                tstar := LT.Progress(sub);
                NP.RACongProgressOutside(sub, tc, inp, S);
              case _ =>
            }
          } else {
            // t == Mismatch: the dissolved guard fails â€” tr_plusfail
            tstar := LT.Mismatch;
            var fx: int, fy: int :| NR.GetPcRE(code, pc) == Some(RB.Fork(fx, fy))
              && fx >= 0 && fy >= 0 && (fx as nat <= pc || fy as nat <= pc);
            assert TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b));
          }
        }
  }

  lemma ATR_AcloseNested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, gid: LG.GroupId, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTreeK(t, S)
    requires |acts| > 0 && acts[0] == LS.Aclose(gid)
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActionsRec(cont)
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
        match t {
          case GroupActionT(g, tc) =>
            assert g == LG.Close(gid);
            WO.WalkOkAclose(acts, code, pc, EaOf(b));
            assert CE.PSize(tc) < CE.PSize(t);
            assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
            assert NB.EncOk(cont, inp, b) by { NB.EncOkTailReg(acts, inp, b); }
            var sub := ActionsTreeRepFRENested(rer, qm, cont, code, pc + 1, inp, b, tc, n - 1, S);
            tstar := LT.GroupActionT(g, sub);
            // tr_close
            NP.RACongGroupOutside(g, sub, tc, inp, S);
          case _ =>
        }
  }

  lemma ATR_EpsilonNested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTreeK(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Epsilon)
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActionsRec(cont)
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
          assert pcmid == pc;
          WO.WalkOkEpsilon(acts, code, pc, EaOf(b));
          assert MsizeA(cont) < MsizeA(acts);
          assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
          assert NB.EncOk(cont, inp, b) by { NB.EncOkTailReg(acts, inp, b); }
          tstar := ActionsTreeRepFRENested(rer, qm, cont, code, pc, inp, b, t, n - 1, S);
  }

  lemma ATR_CharacterNested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, cd: LC.CharDescr, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTreeK(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Character(cd))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActionsRec(cont)
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
          var ce :| NR.GetPcRE(code, pc) == Some(RB.Consume(ce)) && AR.ExpectationMatches(rer, ce, cd);
          AR.ReadAgree(rer, ce, cd, inp);
          match LC.ReadChar(rer, cd, inp, WP.Forward) {
            case None =>
              // t == Mismatch; tr_readfail (ReadCharE == None by ReadAgree)
              tstar := LT.Mismatch;
            case Some(pair) =>
              match t {
                case Read(c, tc) =>
                  assert c == pair.0;
                  WO.WalkOkCharacter(acts, code, pc, EaOf(b));
                  assert CE.PSize(tc) < CE.PSize(t);
                  assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
                  assert NB.EncOk(cont, pair.1, BS.CanExit) by {
                    assert |inp.next| > 0 && pair.1 == LC.Input(inp.next[1..], [inp.next[0]] + inp.pref);
                    NB.EncOkRead(acts, inp, b, pair.1);
                  }
                  var sub := ActionsTreeRepFRENested(rer, qm, cont, code, pc + 1, pair.1, BS.CanExit, tc, n - 1, S);
                  tstar := LT.Read(c, sub);
                  // tr_read with witness (ce, pair.1)
                  assert AR.ReadCharE(ce, inp) == Some((c, pair.1));
                  NP.RACongReadOutside(c, sub, tc, inp, S);
                case _ =>
              }
          }
  }

  lemma ATR_DisjunctionNested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, r1: L.Regex, r2: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTreeK(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Disjunction(r1, r2))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActionsRec(cont)
    requires EL.PikeLkRegexRec(L.Disjunction(r1, r2))
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.Fork(pc + 1, e1 + 1))
                       && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid))
                       && AR.NfaRepL(rer, qm, r2, code, e1 + 1, pcmid);
          AR.NfaRepIncrL(rer, qm, r1, code, pc + 1, e1);
          match t {
            case Choice(ta, tb) =>
              WO.WalkOkAlt(acts, code, pc, EaOf(b), r1, r2, pc + 1, e1 + 1);
              // left branch: [Areg r1]+cont at pc+1 (cont reached via Jmp(e1â†’pcmid))
              var la := [LS.Areg(r1)] + cont;
              assert AR.ActionsRepL(rer, qm, cont, code, e1) by {
                FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                assert NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid));
              }
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, e1);
              assert la[0] == LS.Areg(r1) && la[1..] == cont;
              assert AR.ActionsRepL(rer, qm, la, code, pc + 1);
              ActionsRepLToFuel(rer, qm, la, code, pc + 1);
              var na: nat :| ActionsRepFuelL(rer, qm, la, code, pc + 1, na);
              assert CE.PSize(ta) < CE.PSize(t);
              assert LL.LkActsInS(la, S) by { LL.LkActsInSTail(acts, S); LL.LkActsInSCons(LS.Areg(r1), cont, S); }
              assert NB.EncOk(la, inp, b) by {
                var parts := [LS.Areg(r1)];
                assert parts + cont == la;
                if NUL.NonNullableL(acts[0].r) { assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
                NB.EncOkExpand(acts, parts, inp, b);
              }
              var suba := ActionsTreeRepFRENested(rer, qm, la, code, pc + 1, inp, b, ta, na, S);
              // right branch: [Areg r2]+cont at e1+1
              var lb := [LS.Areg(r2)] + cont;
              FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              assert AR.ActionRepL(rer, qm, LS.Areg(r2), code, e1 + 1, pcmid);
              assert lb[0] == LS.Areg(r2) && lb[1..] == cont;
              assert AR.ActionsRepL(rer, qm, lb, code, e1 + 1);
              ActionsRepLToFuel(rer, qm, lb, code, e1 + 1);
              var nb: nat :| ActionsRepFuelL(rer, qm, lb, code, e1 + 1, nb);
              assert CE.PSize(tb) < CE.PSize(t);
              assert LL.LkActsInS(lb, S) by { LL.LkActsInSTail(acts, S); LL.LkActsInSCons(LS.Areg(r2), cont, S); }
              assert NB.EncOk(lb, inp, b) by {
                var parts := [LS.Areg(r2)];
                assert parts + cont == lb;
                if NUL.NonNullableL(acts[0].r) { assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
                NB.EncOkExpand(acts, parts, inp, b);
              }
              var subb := ActionsTreeRepFRENested(rer, qm, lb, code, e1 + 1, inp, b, tb, nb, S);
              tstar := LT.Choice(suba, subb);
              // tr_choice with the forward Fork(pc+1, e1+1)
              NP.RACongChoiceOutside(suba, ta, subb, tb, inp, S);
            case _ =>
          }
  }

  lemma ATR_SequenceNested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, r1: L.Regex, r2: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTreeK(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Sequence(r1, r2))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActionsRec(cont)
    requires EL.PikeLkRegexRec(L.Sequence(r1, r2))
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
          assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
          var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
          var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
          assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
          assert AR.ActionRepL(rer, qm, LS.Areg(r2), code, e1, pcmid);
          assert ([LS.Areg(r2)] + cont)[0] == LS.Areg(r2) && ([LS.Areg(r2)] + cont)[1..] == cont;
          FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
          assert AR.ActionsRepL(rer, qm, [LS.Areg(r2)] + cont, code, e1);
          assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc, e1);
          assert na[0] == LS.Areg(r1) && na[1..] == [LS.Areg(r2)] + cont;
          assert AR.ActionsRepL(rer, qm, na, code, pc);
          assert LS.ActionsRegexSize(na) < LS.ActionsRegexSize(acts);
          assert MsizeA(na) < MsizeA(acts);
          ActionsRepLToFuel(rer, qm, na, code, pc);
          var nn: nat :| ActionsRepFuelL(rer, qm, na, code, pc, nn);
          WO.WalkOkSeq(acts, code, pc, EaOf(b), r1, r2);
          assert LL.LkActsInS(na, S) by {
            LL.LkActsInSTail(acts, S);
            LL.LkActsInSCons(LS.Areg(r2), cont, S);
            LL.LkActsInSCons(LS.Areg(r1), [LS.Areg(r2)] + cont, S);
          }
          assert NB.EncOk(na, inp, b) by {
            var parts := [LS.Areg(r1), LS.Areg(r2)];
            assert parts + cont == na;
            if NUL.NonNullableL(acts[0].r) {
              if NUL.NonNullableL(r1) { assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
              else { assert parts[1].Areg? && NUL.NonNullableL(parts[1].r); }
            }
            NB.EncOkExpand(acts, parts, inp, b);
          }
          tstar := ActionsTreeRepFRENested(rer, qm, na, code, pc, inp, b, t, nn, S);
  }

  lemma ATR_GroupNested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, gid: LG.GroupId, r1: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTreeK(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Group(gid, r1))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActionsRec(cont)
    requires EL.PikeLkRegexRec(L.Group(gid, r1))
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
          EL.PikeLkActionsRecConsIff(LS.Aclose(gid), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
          var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid as int)))
                       && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(gid as int)))
                       && pcmid == e1 + 1;
          match t {
            case GroupActionT(g, tc) =>
              assert g == LG.Open(gid);
              WO.WalkOkGroup(acts, code, pc, EaOf(b), gid, r1);
              var lc := [LS.Aclose(gid)] + cont;
              assert AR.ActionRepL(rer, qm, LS.Aclose(gid), code, e1, e1 + 1);
              assert lc[0] == LS.Aclose(gid) && lc[1..] == cont;
              FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              assert AR.ActionsRepL(rer, qm, lc, code, e1);
              var ga := [LS.Areg(r1)] + lc;
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, e1);
              assert ga[0] == LS.Areg(r1) && ga[1..] == lc;
              assert AR.ActionsRepL(rer, qm, ga, code, pc + 1);
              assert ga == [LS.Areg(r1), LS.Aclose(gid)] + cont;
              ActionsRepLToFuel(rer, qm, ga, code, pc + 1);
              var ng: nat :| ActionsRepFuelL(rer, qm, ga, code, pc + 1, ng);
              assert CE.PSize(tc) < CE.PSize(t);
              assert LL.LkActsInS(ga, S) by {
                LL.LkActsInSTail(acts, S);
                LL.LkActsInSCons(LS.Aclose(gid), cont, S);
                LL.LkActsInSCons(LS.Areg(r1), [LS.Aclose(gid)] + cont, S);
              }
              assert NB.EncOk(ga, inp, b) by {
                var parts := [LS.Areg(r1), LS.Aclose(gid)];
                assert parts + cont == ga;
                if NUL.NonNullableL(acts[0].r) { assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
                NB.EncOkExpand(acts, parts, inp, b);
              }
              var sub := ActionsTreeRepFRENested(rer, qm, ga, code, pc + 1, inp, b, tc, ng, S);
              tstar := LT.GroupActionT(g, sub);
              // tr_open
              NP.RACongGroupOutside(g, sub, tc, inp, S);
            case _ =>
          }
  }

  lemma ATR_AnchorRNested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, la: L.Anchor, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTreeK(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.AnchorR(la))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActionsRec(cont)
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
          // NfaRepL(AnchorR) => AnchorAssertion(ra) at pc with TrAnchor(ra) == la, pcmid == pc + 1
          var ra: R.anchor :| NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(ra))
                              && T.TrAnchor(ra) == la;
          TR.AnchorAgreeInput(rer, ra, inp);
          if LS.AnchorSatisfied(rer, la, inp) {
            match t {
              case AnchorPass(la2, tc) =>
                assert la2 == la;
                WO.WalkOkAnchor(acts, code, pc, EaOf(b));
                assert CE.PSize(tc) < CE.PSize(t);
                assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
                assert NB.EncOk(cont, inp, b) by { NB.EncOkTailReg(acts, inp, b); }
                var sub := ActionsTreeRepFRENested(rer, qm, cont, code, pc + 1, inp, b, tc, n - 1, S);
                tstar := LT.AnchorPass(la2, sub);
                // tr_anchorpass (is_satisfied via the agreement)
                NP.RACongAnchorOutside(la2, sub, tc, inp, S);
              case _ =>
            }
          } else {
            // t == Mismatch; tr_anchorfail via the agreement
            tstar := LT.Mismatch;
          }
  }

  lemma ATR_LookaroundRNested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, cont: LS.Actions, code: RB.code, pc: nat, pcmid: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, n: nat, lk: L.Lookaround, r1: L.Regex, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTreeK(t, S)
    requires |acts| > 0 && acts[0] == LS.Areg(L.LookaroundR(lk, r1))
    requires cont == acts[1..]
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1)
    requires EL.PikeLkActionsRec(cont)
    requires EL.PikeLkRegexRec(L.LookaroundR(lk, r1))
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
    decreases CE.PSize(t), MsizeA(acts), n, 0
  {
    assert acts == [acts[0]] + cont;
    var r := L.LookaroundR(lk, r1);
          // THE GATE. `NfaRepL`'s lookaround arm pins one zero-width
          // instruction at `pc`, whose bare lid the `looks` table maps back to
          // this (flavour, body); `OracleOkAt` says the oracle column agrees
          // with the body's walk, which is what `BoolTreeLk`'s rule decided by.
          // The checked tree DROPS the wrapper: it is the continuation's tree
          // on a pass, `Mismatch` on a kill.
          var lid: int :| NR.GetPcRE(code, pc)
                            == Some(if AR.PositiveL(lk) then RB.CheckOracle(lid)
                                                        else RB.NegCheckOracle(lid))
                          && lid in qm.looks && qm.looks[lid] == (lk, r1);
          assert pcmid == pc + 1;
          assert LL.OracleOkAt(rer, qm, inp);
          var tlkc := FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
          var bit := LOr.view_get_oracle(qm.ov, TR.CpOf(inp), lid);
          assert bit <==> LT.TreeRes(tlkc, LG.Empty, inp, L.LkDir(lk)).Some?;
          LT.FirstTreeLeaf(tlkc, LG.Empty, inp, L.LkDir(lk));
          // A POSITIVE look (fwd/bwd) body may CAPTURE; its confinement is supplied
          // by `LkConfinedTree(t, S)` in the pass branch below. A passing NEGATIVE
          // gate has no body leaf, which is all `LAAtGatePassNeg` needs.
          match t {
            case LK(lk2, tlk, tc) =>
              // the gate passed: `LkGateOk(.., true)` pins tlk == tlkc and the
              // verdict, so the engine's bit agrees
              assert tlk == tlkc && LS.LkResult(lk, tlk, LG.Empty, inp).Some?;
              assert bit == AR.PositiveL(lk);
              WO.WalkOkLookaround(acts, code, pc, EaOf(b));
              assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
              assert NB.EncOk(cont, inp, b) by { NB.EncOkTailReg(acts, inp, b); }
              var sub := ActionsTreeRepFRENested(rer, qm, cont, code, pc + 1, inp, b, tc, n - 1, S);
              tstar := sub;
              // tr_lk / tr_neglk: the gate rule carries the SAME tree onward
              assert TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b));
              if L.Positivity(lk) {
                // L3a/L3b: a POSITIVE look (fwd/bwd) gate may fold captures within
                // S -- use the confinement path (works for capture-free bodies
                // too, since GmNeutral => GmConfinedTree(_, S)).
                assert CE.LkConfinedTreeRec(tlk, S);   // from LkConfinedTree(t, S), t == LK(_,tlk,tc)
                assert |LT.TreeLeaves(tlk, LG.Empty, inp, L.LkDir(lk))| > 0 by {
                  assert LT.TreeRes(tlk, LG.Empty, inp, L.LkDir(lk)).Some?;   // LkResult(lk,tlk,Empty).Some?, positive
                  LT.HdErrorNoneNil(LT.TreeLeaves(tlk, LG.Empty, inp, L.LkDir(lk)));
                }
                LL.LAAtReflOutside(tc, inp, S);
                LL.LKNodeOutsideRec(lk, tlk, tc, tc, inp, S);
                NP.ResFromLeavesOutside(tc, LT.LK(lk, tlk, tc), inp, S);
                NP.RATransOutside(sub, tc, LT.LK(lk, tlk, tc), inp, S);
              } else {
                LL.LAAtGatePassNeg(lk, tlk, tc, inp);
                LL.LeavesAgreeAtWeaken(LT.LK(lk, tlk, tc), tc, inp, S);
                NP.ResFromLeavesOutside(LT.LK(lk, tlk, tc), tc, inp, S);
                NP.RASymOutside(LT.LK(lk, tlk, tc), tc, inp, S);
                NP.RATransOutside(sub, tc, LT.LK(lk, tlk, tc), inp, S);
              }
            case LKFail(lk2, tlk) =>
              assert tlk == tlkc && LS.LkResult(lk, tlk, LG.Empty, inp).None?;
              assert bit != AR.PositiveL(lk);
              tstar := LT.Mismatch;
              // tr_lkfail / tr_neglkfail
              assert TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b));
              LL.LAAtGateFail(lk, tlk, inp);
              LL.LeavesAgreeAtWeaken(LT.Mismatch, LT.LKFail(lk, tlk), inp, S);
              NP.ResFromLeavesOutside(LT.Mismatch, LT.LKFail(lk, tlk), inp, S);
            case _ =>
          }
  }

  /** The fused fork lemma: at the do-while's backward fork with the walk
      allowed to exit, the (possibly transparent-headed) continuation's spec
      tree yields a checked Choice whose `Progress` wrapper is consumed by
      `tr_plus` together with the fork. Pops `Epsilon`/`Sequence`/spent
      heads; every other head shape contradicts the pinned Fork; at the
      loop-view star, the iteration is lifted to `CanExit` (`BoolFlagLift` â€”
      the engine runs it at `exit_allowed == true`) and both branches are
      built by the general construction. */
  lemma AtBackForkTreeRepNested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, code: RB.code, pc: nat, inp: LC.Input, tc: LT.Tree, n: nat, S: set<LG.GroupId>)
    returns (tcstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, BS.CanExit)
    requires !rer.multiline
    requires ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, true)
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, BS.CanExit, tc)
    requires AR.BackForkAt(code, pc)
    requires CE.LkConfinedTreeK(tc, S)
    ensures TR.TreeRepRE(qm, LT.Progress(tcstar), code, pc, inp, true)
    ensures NP.ResAgreeAtOutside(tcstar, tc, inp, S)
    decreases CE.PSize(tc), MsizeA(acts), n, 0
  {
    var fx: int, fy: int :| NR.GetPcRE(code, pc) == Some(RB.Fork(fx, fy))
      && fx >= 0 && fy >= 0 && (fx as nat <= pc || fy as nat <= pc);
    // Accept and Jmp bottoms contradict the pinned Fork: the fuel derivation
    // must be a cons step.
    assert |acts| > 0;
    var cont := acts[1..];
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + cont;
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    match acts[0]
    case Acheck(strcheck) =>
      // a stacked check: also zero-width at the fork (EndLoop is refuted);
      // its Progress collapses into the same leaves
      assert pcmid == pc;
      assert LS.ActionsRegexSize(acts) == LS.ActionsRegexSize(cont);
      match tc {
        case Progress(tc2) =>
          WO.WalkOkAcheckBackFork(acts, code, pc, true);
          assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
          assert NB.EncOk(cont, inp, BS.CanExit) by { NB.EncOkTailCheck(acts, inp); }
          var sub := AtBackForkTreeRepNested(rer, qm, cont, code, pc, inp, tc2, n - 1, S);
          tcstar := sub;
          NP.RAProgressPassOutside(tc2, inp, S);
          assert NP.ResAgreeAtOutside(tcstar, tc, inp, S);
        case _ =>
      }
    case Aclose(gid) =>
      // pins SetRegisterToCP: contradiction with the Fork
      assert false;
    case Areg(r) =>
      assert EL.PikeLkRegexRec(r);
      match r
      case Epsilon =>
        assert pcmid == pc;
        WO.WalkOkEpsilon(acts, code, pc, true);
        assert MsizeA(cont) < MsizeA(acts);
        assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
        assert NB.EncOk(cont, inp, BS.CanExit) by { NB.EncOkTailReg(acts, inp, BS.CanExit); }
        tcstar := AtBackForkTreeRepNested(rer, qm, cont, code, pc, inp, tc, n - 1, S);
      case Character(cd) =>
        var ce :| NR.GetPcRE(code, pc) == Some(RB.Consume(ce)) && AR.ExpectationMatches(rer, ce, cd);
        assert false;   // Consume != Fork
      case AnchorR(la) =>
        var ra: R.anchor :| NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(ra)) && T.TrAnchor(ra) == la;
        assert false;   // AnchorAssertion != Fork
      case Disjunction(r1, r2) =>
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.Fork(pc + 1, e1 + 1))
          && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
          && NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid))
          && AR.NfaRepL(rer, qm, r2, code, e1 + 1, pcmid);
        AR.NfaRepIncrL(rer, qm, r1, code, pc + 1, e1);
        assert false;   // both arms forward: contradicts the backward arm
      case Sequence(r1, r2) =>
        EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
        EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        assert AR.ActionRepL(rer, qm, LS.Areg(r2), code, e1, pcmid);
        assert ([LS.Areg(r2)] + cont)[0] == LS.Areg(r2) && ([LS.Areg(r2)] + cont)[1..] == cont;
        FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
        assert AR.ActionsRepL(rer, qm, [LS.Areg(r2)] + cont, code, e1);
        assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc, e1);
        assert na[0] == LS.Areg(r1) && na[1..] == [LS.Areg(r2)] + cont;
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert LS.ActionsRegexSize(na) < LS.ActionsRegexSize(acts);
        assert MsizeA(na) < MsizeA(acts);
        ActionsRepLToFuel(rer, qm, na, code, pc);
        var nn: nat :| ActionsRepFuelL(rer, qm, na, code, pc, nn);
        WO.WalkOkSeq(acts, code, pc, true, r1, r2);
          assert LL.LkActsInS(na, S) by {
          LL.LkActsInSTail(acts, S);
          LL.LkActsInSCons(LS.Areg(r2), cont, S);
          LL.LkActsInSCons(LS.Areg(r1), [LS.Areg(r2)] + cont, S);
        }
        assert NB.EncOk(na, inp, BS.CanExit) by {
          var parts := [LS.Areg(r1), LS.Areg(r2)];
          assert parts + cont == na;
          if NUL.NonNullableL(acts[0].r) {
            if NUL.NonNullableL(r1) { assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
            else { assert parts[1].Areg? && NUL.NonNullableL(parts[1].r); }
          }
          NB.EncOkExpand(acts, parts, inp, BS.CanExit);
        }
        tcstar := AtBackForkTreeRepNested(rer, qm, na, code, pc, inp, tc, nn, S);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        if min > 0 {
          // every forced-copy head pins a clock-mark: contradiction
          match delta {
            case Inf =>
              if NUL.NonNullableL(r1) {
                var em, e1x := AR.NfaRepLPlusInv(rer, qm, greedy, min, r1, code, pc, pcmid);
                if em == pc {
                  assert false;    // SetQuantToClock != Fork
                } else {
                  var eb: nat :| (exists qid: int ::
                        NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                        && qid in qm.quants && qm.quants[qid] == gidl)
                    && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                    && AR.NfaRepMinL(rer, qm, min - 2, r1, code, eb, em);
                  assert false;    // SetQuantToClock != Fork
                }
              } else if greedy {
                // §2.5b CIN-GREEDY: a forced copy (min > 1) pins a clock-mark at
                // pc; at min == 1 the head fork is FORWARD (both arms past pc),
                // contradicting the backward arm
                var em, e1x := AR.NfaRepLCinInv(rer, qm, greedy, min, r1, code, pc, pcmid);
                if min > 1 {
                  var eb: nat :| (exists qid: int ::
                        NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                        && qid in qm.quants && qm.quants[qid] == gidl)
                    && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                    && AR.NfaRepMinL(rer, qm, min - 2, r1, code, eb, em);
                  assert false;    // SetQuantToClock != Fork
                } else {
                  assert em == pc;
                  AR.NfaRepIncrL(rer, qm, r1, code, em + 3, e1x);
                  assert NR.GetPcRE(code, pc) == Some(RB.Fork(em + 1, e1x + 2));
                  assert fx == em + 1 && fy == e1x + 2;
                  assert false;    // both arms > pc: not a backward fork
                }
              } else {
                // the GENERIC scheme (§2.5a): `min >= 1` forced copies, so `pc`
                // still carries a clock-mark -- refuted the same way
                var em, e1x := AR.NfaRepLGenInv(rer, qm, greedy, min, r1, code, pc, pcmid);
                var eb: nat :| (exists qid: int ::
                      NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                      && qid in qm.quants && qm.quants[qid] == gidl)
                  && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                  && AR.NfaRepMinL(rer, qm, min - 1, r1, code, eb, em);
                assert false;    // SetQuantToClock != Fork
              }
            case NN(kx) =>
              var em := AR.NfaRepLQuantInv(rer, qm, greedy, min, kx, r1, code, pc, pcmid);
              var eb: nat :| (exists qid: int ::
                    NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                    && qid in qm.quants && qm.quants[qid] == gidl)
                && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                && AR.NfaRepMinL(rer, qm, min - 1, r1, code, eb, em);
              assert false;      // SetQuantToClock != Fork
          }
        } else if delta.NN? {
          var k := delta.n;
          var em := AR.NfaRepLQuantInv(rer, qm, greedy, 0, k, r1, code, pc, pcmid);
          assert em == pc;
          if k == 0 {
            // spent: transparent, peel
            assert pc == pcmid;
            WO.WalkOkQuantSpent(acts, code, pc, true, greedy, r1);
            assert LS.ActionsRegexSize(cont) < LS.ActionsRegexSize(acts);
            assert MsizeA(cont) < MsizeA(acts);
            assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
            assert NB.EncOk(cont, inp, BS.CanExit) by { NB.EncOkTailReg(acts, inp, BS.CanExit); }
            tcstar := AtBackForkTreeRepNested(rer, qm, cont, code, pc, inp, tc, n - 1, S);
          } else {
            // a bounded layer pins a FORWARD fork: contradiction
            var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, pcmid) else RB.Fork(pcmid, pc + 1))
              && (exists qid: int ::
                    NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                    && qid in qm.quants && qm.quants[qid] == gidl)
              && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
              && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
              && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
              && AR.NfaRepOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
            AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
            AR.NfaRepIncrOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
            assert false;
          }
        } else {
          assert min == 0 && delta == LN.Inf;
          if exists e1: nat :: NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                       && (exists qid: int ::
                             NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                             && qid in qm.quants && qm.quants[qid] == gidl)
                       && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                       && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                       && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                       && pcmid == e1 + 2 {
            // the fast path pins a forward fork: contradiction
            var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
              && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
              && pcmid == e1 + 2;
            AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
            assert false;
          } else {
            // THE LOOP VIEW: the star seen from the fork itself
            AR.NfaRepLStarLoopViews(rer, qm, greedy, r1, code, pc, pcmid);
            if NUL.NonNullableL(r1) {
            var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em))
              && em <= pc
              && (exists qid: int ::
                    NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                    && qid in qm.quants && qm.quants[qid] == gidl)
              && AR.NfaRepL(rer, qm, r1, code, em + 1, pc)
              && pcmid == pc + 1;
            var qid: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
              && qid in qm.quants && qm.quants[qid] == gidl;
            var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
            assert q0 == L.Quantified(greedy, 0, LN.Inf, r1) == r;
            WO.WalkOkLoopView(acts, code, pc, true, greedy, LN.Inf, r1,
                              if greedy then em else pc + 1,
                              if greedy then pc + 1 else em, inp);
            match tc {
              case Choice(cta, ctb) =>
                var itert := if greedy then cta else ctb;
                var skipt := if greedy then ctb else cta;
                match itert {
                  case GroupActionT(g, ti) =>
                    assert g == LG.Reset(gidl);
                    var il := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
                    assert EL.BoolTreeLk(rer, il, inp, BS.CannotExit, ti);
                    // skip branch: the general construction at the exit arm
                    assert CE.PSize(skipt) < CE.PSize(tc);
                    assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
                    assert NB.EncOk(cont, inp, BS.CanExit) by { NB.EncOkTailReg(acts, inp, BS.CanExit); }
                    var subs := ActionsTreeRepFRENested(rer, qm, cont, code, pc + 1, inp, BS.CanExit, skipt, n - 1, S);
                    // iteration branch: lift to CanExit (the engine keeps
                    // exit_allowed through the back edge), then construct
                    EL.PikeLkActionsRecConsIff(LS.Areg(q0), cont);
                    EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(q0)] + cont);
                    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
                    assert il == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
                    assert EL.PikeLkActionsRec(il);
                    assert CE.ShieldedActs(il) by {
                      forall i | 0 <= i < |il| && il[i].Acheck?
                        ensures exists j :: 0 <= j < i && il[j].Areg? && NUL.NonNullableL(il[j].r)
                      {
                        assert il[0] == LS.Areg(r1);
                        assert i > 0;
                        assert il[0].Areg? && NUL.NonNullableL(il[0].r);
                      }
                    }
                    CE.BoolFlagLiftRec(rer, il, inp, ti);
                    assert EL.BoolTreeLk(rer, il, inp, BS.CanExit, ti);
                    // representation of the iteration list at em+1
                    FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                    var lq := [LS.Areg(q0)] + cont;
                    assert AR.NfaRepL(rer, qm, q0, code, pc, pc + 1) by {
                      assert NUL.NonNullableL(r1)
                        && NR.GetPcRE(code, pc)
                           == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em))
                        && em <= pc
                        && (exists qid2: int ::
                              NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid2, false))
                              && qid2 in qm.quants && qm.quants[qid2] == L.DefGroups(r1))
                        && AR.NfaRepL(rer, qm, r1, code, em + 1, pc);
                    }
                    assert AR.ActionRepL(rer, qm, LS.Areg(q0), code, pc, pc + 1);
                    assert lq[0] == LS.Areg(q0) && lq[1..] == cont;
                    assert AR.ActionsRepL(rer, qm, lq, code, pc);
                    var lc := [LS.Acheck(inp)] + lq;
                    assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, pc, pc);
                    assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
                    assert AR.ActionsRepL(rer, qm, lc, code, pc);
                    assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, em + 1, pc);
                    assert il == [LS.Areg(r1)] + lc;
                    assert il[0] == LS.Areg(r1) && il[1..] == lc;
                    assert AR.ActionsRepL(rer, qm, il, code, em + 1);
                    ActionsRepLToFuel(rer, qm, il, code, em + 1);
                    var ni: nat :| ActionsRepFuelL(rer, qm, il, code, em + 1, ni);
                    assert CE.PSize(ti) < CE.PSize(tc);
                    assert LL.LkActsInS(il, S) by {
                      LL.LkActsInSTail(acts, S);
                      assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(q0, S);
                      LL.LkActsInSCons(LS.Areg(q0), cont, S);
                      LL.LkActsInSCons(LS.Acheck(inp), [LS.Areg(q0)] + cont, S);
                      LL.LkActsInSCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont), S);
                    }
                    assert NB.EncOk(il, inp, BS.CanExit) by {
                      NB.EncodableTail(acts, inp, BS.CanExit);
                      NB.EncOkIterLift(r1, q0, cont, inp);
                    }
                    var subi := ActionsTreeRepFRENested(rer, qm, il, code, em + 1, inp, BS.CanExit, ti, ni, S);
                    // assemble: tr_reset at the stamp, then tr_plus at the fork
                    var iterstar := LT.GroupActionT(g, subi);
                    assert TR.TreeRepRE(qm, iterstar, code, em, inp, true);
                    tcstar := if greedy then LT.Choice(iterstar, subs) else LT.Choice(subs, iterstar);
                    NP.RACongGroupOutside(g, subi, ti, inp, S);
                    if greedy {
                      NP.RACongChoiceOutside(iterstar, itert, subs, skipt, inp, S);
                    } else {
                      NP.RACongChoiceOutside(subs, skipt, iterstar, itert, inp, S);
                    }
                    assert TR.TreeRepRE(qm, LT.Progress(tcstar), code, pc, inp, true);
                  case _ =>
                }
              case _ =>
            }
            } else {
              // §2.5b: THE CIN LOOP VIEW — the star seen from the CIN-greedy loop's
              // backward end fork: re-entry through the clock-mark and the BeginLoop
              // (the iteration walks at CannotExit; the loop's EndLoop IS the spec's
              // check, so nothing is lifted), exit straight to e1 + 3.
              var em, e1 := AR.NfaRepLStarCinInv(rer, qm, r1, code, pc, pcmid);
              var qidC: int :| NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qidC, false))
                && NR.GetPcRE(code, e1 + 2) == Some(RB.SetQuantToClock(qidC, true))
                && qidC in qm.quants && qm.quants[qidC] == gidl
                && AR.StampBodyOk(qm, qidC, r1);
              assert greedy;
              var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
              assert q0 == L.Quantified(greedy, 0, LN.Inf, r1) == r;
              WO.WalkOkLoopViewCin(acts, code, pc, true, greedy, LN.Inf, r1, em + 1, e1 + 3, inp);
              match tc {
                case Choice(cta, ctb) =>
                  var itert := cta;
                  var skipt := ctb;
                  match itert {
                    case GroupActionT(g, ti) =>
                      assert g == LG.Reset(gidl);
                      var il := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
                      assert EL.BoolTreeLk(rer, il, inp, BS.CannotExit, ti);
                      // skip branch: the general construction at the exit arm
                      assert CE.PSize(skipt) < CE.PSize(tc);
                      assert LL.LkActsInS(cont, S) by { LL.LkActsInSTail(acts, S); }
                      assert NB.EncOk(cont, inp, BS.CanExit) by { NB.EncOkTailReg(acts, inp, BS.CanExit); }
                      var subs := ActionsTreeRepFRENested(rer, qm, cont, code, pcmid, inp, BS.CanExit, skipt, n - 1, S);
                      // iteration branch at CannotExit from the body start em + 3
                      EL.PikeLkActionsRecConsIff(LS.Areg(q0), cont);
                      EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(q0)] + cont);
                      EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
                      assert il == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
                      assert EL.PikeLkActionsRec(il);
                      FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                      var lq := [LS.Areg(q0)] + cont;
                      assert AR.ActionRepL(rer, qm, LS.Areg(q0), code, pc, pcmid);
                      assert lq[0] == LS.Areg(q0) && lq[1..] == cont;
                      assert AR.ActionsRepL(rer, qm, lq, code, pc);
                      var lc := [LS.Acheck(inp)] + lq;
                      assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1, e1 + 1);
                      assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
                      assert AR.ActionsRepL(rer, qm, lc, code, e1);
                      assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, em + 3, e1);
                      assert il[0] == LS.Areg(r1) && il[1..] == lc;
                      assert AR.ActionsRepL(rer, qm, il, code, em + 3);
                      ActionsRepLToFuel(rer, qm, il, code, em + 3);
                      var ni: nat :| ActionsRepFuelL(rer, qm, il, code, em + 3, ni);
                      assert CE.PSize(ti) < CE.PSize(tc);
                      assert LL.LkActsInS(il, S) by {
                        LL.LkActsInSTail(acts, S);
                        assert LL.LkBodiesInS(r1, S) && LL.LkBodiesInS(q0, S);
                        LL.LkActsInSCons(LS.Areg(q0), cont, S);
                        LL.LkActsInSCons(LS.Acheck(inp), [LS.Areg(q0)] + cont, S);
                        LL.LkActsInSCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont), S);
                      }
                      assert NB.EncOk(il, inp, BS.CannotExit) by {
                        NB.EncodableTail(acts, inp, BS.CanExit);
                        NB.EncOkIter(r1, q0, cont, inp);
                      }
                      var subi := ActionsTreeRepFRENested(rer, qm, il, code, em + 3, inp, BS.CannotExit, ti, ni, S);
                      // assemble: tr_begin at em + 2, tr_reset at em + 1, tr_plus at the fork
                      assert TR.TreeRepRE(qm, subi, code, em + 2, inp, true);
                      var iterstar := LT.GroupActionT(g, subi);
                      assert TR.TreeRepRE(qm, iterstar, code, em + 1, inp, true);
                      tcstar := LT.Choice(iterstar, subs);
                      NP.RACongGroupOutside(g, subi, ti, inp, S);
                      NP.RACongChoiceOutside(iterstar, itert, subs, skipt, inp, S);
                      assert TR.TreeRepRE(qm, LT.Progress(tcstar), code, pc, inp, true);
                    case _ =>
                  }
                case _ =>
              }
            }
          }
        }
      case Group(gid, r1) =>
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid as int)))
          && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
          && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(gid as int)))
          && pcmid == e1 + 1;
        assert false;   // SetRegisterToCP != Fork
      case LookaroundR(_, _) =>    // not pike
      case Backreference(_) =>     // not pike
  }

  // The construction theorem (port of actions_tree_rep, checked form).
  /** The construction theorem: whenever action stack `acts` is
      `ActionsRepL`-represented at `pc`, walk-guarded, and its spec `BoolTree`
      is `t`, the returned checked tree is `TreeRepRE`-represented at `pc`
      and agrees with `t` on leaves. */
  lemma ActionsTreeRepRENested(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, code: RB.code, pc: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, S: set<LG.GroupId>)
    returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires NB.EncOk(acts, inp, b)
    requires !rer.multiline
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires WO.WalkOk(acts, code, pc, EaOf(b))
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires CE.LkConfinedTreeK(t, S)
    ensures TR.TreeRepRE(qm, tstar, code, pc, inp, EaOf(b))
    ensures NP.ResAgreeAtOutside(tstar, t, inp, S)
  {
    ActionsRepLToFuel(rer, qm, acts, code, pc);
    var n: nat :| ActionsRepFuelL(rer, qm, acts, code, pc, n);
    tstar := ActionsTreeRepFRENested(rer, qm, acts, code, pc, inp, b, t, n, S);
  }

}
