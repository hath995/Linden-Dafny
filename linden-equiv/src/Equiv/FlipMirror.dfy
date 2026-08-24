// L5 CAPTURES — BRICK F1 (part 1): the FLIP tree mirror — builder + Someness fold.
//
// The flip-route spec mirror (L5_HANDOFF.md §5): a BACKWARD walk of a
// `GroupOkLB` stack mirrors the FORWARD walk of the KIND-FLIPPED reversal over
// the swapped window. Where the kind-PRESERVING mirror is provably vacuous for
// nested looks (`GateAgreeIsFalse`, TreeMirrorLk.dfy), the flip version's
// `LookaroundR` case is a REAL proven case: the flipped inner look walks the
// OTHER direction over the swapped input and reads the SAME chars, so the two
// sub-trees FULLY mirror — no gate hypothesis, no oracle, no exclusion of
// inner sub-trees.
//
// Contents:
//  - `FlipRevL` (= `FlipL o RevL`, the kind-flipping reversal), `FlipRevActs`,
//    plumbing (Cons/Tail/Append, `GroupOkLBActs`, DefGroups preservation).
//  - `TreeMirrorRelF` — `TM.TreeMirrorRel` + REAL `LK`/`LKFail` cases: kinds
//    related by `FlipLk` (original side pinned lookbehind-flavoured, the v1
//    GroupOkLB scope), FULL sub-tree recursion.
//  - `TreeResSomeMirrorF` — relation-related trees have the same
//    `TreeRes`-SUCCESS at ANY pair of group maps (success is gm-blind for
//    backreference-free trees, so no close-discipline machinery is needed).
//    This is exactly the gate-verdict fact the builder's `LookaroundR` case
//    consumes — the fact the no-flip route could not have.
//  - Fuel transport (`WorstInputSwap`/`RegexFuelFlipRev`/`ActionsFuelFlipRev`).
//  - THE BUILDER `ComputeTreeReverseF` (+ fuel-free `ComputeTrReverseF`):
//    the flip analogue of reasoning's `ComputeTreeReverse` (TreeMirror.dfy),
//    with the `assert false` LookaroundR arm replaced by the real case.
//  - `FlipMirrorSatisfiableNested` — the anti-vacuity witness: the mirror
//    APPLIES to a stack containing a nested lookbehind (its hypotheses are
//    satisfiable exactly where `GateAgree`'s were not).
//
// The leaf-VALUE fold (MirrorGm equality, needs the close discipline) is part
// 2 (`TreeResMirrorF`), consumed by F2 `BackBodyGmTieFlip`.

include "FlipRev.dfy"

/** F1 (part 1): the flip tree mirror — relation, Someness fold, and builder. */
module LindenElkFlipMirror {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LN = WarblreNumeric
  import LS = Semantics
  import LT = Tree
  import FU = FunctionalUtils
  import FS = FunctionalSemantics
  import SSx = StrictSuffix
  import SD = LindenSpanDuality
  import TM = LindenTreeMirror
  import TRM = LindenTreeResMirror
  import FR = LindenElkFlipRev

  // ===========================================================================
  // The kind-flipping reversal and its stack lift
  // ===========================================================================

  /** The KIND-FLIPPING reversal: `RevL` (reverse + anchor swap) followed by
      the look-kind flip. Under this map — and only under it — a reversed
      look's walk reads the same characters as the original's. */
  function FlipRevL(r: L.Regex): L.Regex {
    FR.FlipL(SD.RevL(r))
  }

  /** `FlipRevActs` maps a stack pointwise: regexes flip-reverse, checkpoints
      swap, closes pass through — `SD.RevActs` with `FlipRevL` in the `Areg`
      slot. */
  function FlipRevActs(acts: LS.Actions): LS.Actions {
    seq(|acts|, i requires 0 <= i < |acts| =>
      match acts[i]
      case Areg(r) => LS.Areg(FlipRevL(r))
      case Acheck(ip) => LS.Acheck(SD.SwapInput(ip))
      case Aclose(g) => LS.Aclose(g))
  }

  lemma FlipRevActsCons(a: LS.Action, acts: LS.Actions)
    ensures FlipRevActs([a] + acts)
         == [(match a case Areg(r) => LS.Areg(FlipRevL(r))
                      case Acheck(ip) => LS.Acheck(SD.SwapInput(ip))
                      case Aclose(g) => LS.Aclose(g))] + FlipRevActs(acts)
  {
    var lhs := FlipRevActs([a] + acts);
    var rhs := [(match a case Areg(r) => LS.Areg(FlipRevL(r))
                         case Acheck(ip) => LS.Acheck(SD.SwapInput(ip))
                         case Aclose(g) => LS.Aclose(g))] + FlipRevActs(acts);
    forall i | 0 <= i < |lhs| ensures lhs[i] == rhs[i] {}
  }

  lemma FlipRevActsTail(acts: LS.Actions)
    requires |acts| > 0
    ensures FlipRevActs(acts)[1..] == FlipRevActs(acts[1..])
  {
    var lhs := FlipRevActs(acts)[1..];
    var rhs := FlipRevActs(acts[1..]);
    forall i | 0 <= i < |lhs| ensures lhs[i] == rhs[i] {}
  }

  /** `FlipRevActs` distributes over concatenation (pointwise map). */
  lemma FlipRevActsAppend(xs: LS.Actions, ys: LS.Actions)
    ensures FlipRevActs(xs + ys) == FlipRevActs(xs) + FlipRevActs(ys)
  {
    var lhs := FlipRevActs(xs + ys);
    var rhs := FlipRevActs(xs) + FlipRevActs(ys);
    assert |lhs| == |rhs|;
    forall i | 0 <= i < |lhs| ensures lhs[i] == rhs[i] {
      if i < |xs| { assert (xs + ys)[i] == xs[i]; } else { assert (xs + ys)[i] == ys[i - |xs|]; }
    }
  }

  /** The v1 stack fragment: every `Areg` regex is `GroupOkLB` (groups + nested
      lookBEHIND-flavoured looks; no backreferences). */
  ghost predicate GroupOkLBActs(acts: LS.Actions) {
    forall i :: 0 <= i < |acts| ==>
      (acts[i].Acheck? || acts[i].Aclose? || (acts[i].Areg? && SD.GroupOkLB(acts[i].r)))
  }

  lemma GroupOkLBActsTail(acts: LS.Actions)
    requires |acts| > 0 && GroupOkLBActs(acts)
    ensures GroupOkLBActs(acts[1..])
  {
    forall i | 0 <= i < |acts[1..]|
      ensures acts[1..][i].Acheck? || acts[1..][i].Aclose?
           || (acts[1..][i].Areg? && SD.GroupOkLB(acts[1..][i].r))
    { assert acts[1..][i] == acts[i + 1]; }
  }

  lemma GroupOkLBActsCons(a: LS.Action, acts: LS.Actions)
    requires GroupOkLBActs(acts)
    requires a.Acheck? || a.Aclose? || (a.Areg? && SD.GroupOkLB(a.r))
    ensures GroupOkLBActs([a] + acts)
  {
    forall i | 0 <= i < |[a] + acts|
      ensures ([a] + acts)[i].Acheck? || ([a] + acts)[i].Aclose?
           || (([a] + acts)[i].Areg? && SD.GroupOkLB(([a] + acts)[i].r))
    { if i > 0 { assert ([a] + acts)[i] == acts[i - 1]; } }
  }

  /** `FlipRevL` preserves the defined-groups SET (RevL permutes, FlipL is
      gid-transparent). */
  lemma FlipRevLDefGroupsSet(r: L.Regex)
    ensures forall g: LG.GroupId :: g in L.DefGroups(FlipRevL(r)) <==> g in L.DefGroups(r)
    decreases r
  {
    FlipLDefGroups(SD.RevL(r));
    SD.RevLDefGroupsSet(r);
  }

  /** `FlipL` preserves `DefGroups` EXACTLY (kinds carry no gids). */
  lemma FlipLDefGroups(r: L.Regex)
    ensures L.DefGroups(FR.FlipL(r)) == L.DefGroups(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => FlipLDefGroups(r1); FlipLDefGroups(r2);
    case Sequence(r1, r2) => FlipLDefGroups(r1); FlipLDefGroups(r2);
    case Quantified(_, _, _, r1) => FlipLDefGroups(r1);
    case Group(_, r1) => FlipLDefGroups(r1);
    case LookaroundR(_, r1) => FlipLDefGroups(r1);
    case _ =>
  }

  // ===========================================================================
  // The relation: TreeMirrorRel + REAL LK/LKFail cases (kinds flip)
  // ===========================================================================

  /** Backward tree `t` and forward tree `tm` correspond under the FLIP: the
      look-free cases are `TM.TreeMirrorRel`'s verbatim; at a look node the
      kinds are `FlipLk`-related (original side lookbehind-flavoured — the v1
      `GroupOkLB` scope) and BOTH the inner sub-tree and the continuation
      recurse — the full mirror the kind-preserving relation provably cannot
      have. */
  ghost predicate TreeMirrorRelF(t: LT.Tree, tm: LT.Tree) {
    match (t, tm)
    case (Mismatch, Mismatch) => true
    case (Match, Match) => true
    case (Choice(a, b), Choice(am, bm)) => TreeMirrorRelF(a, am) && TreeMirrorRelF(b, bm)
    case (Read(c, a), Read(cm, am)) => c == cm && TreeMirrorRelF(a, am)
    case (Progress(a), Progress(am)) => TreeMirrorRelF(a, am)
    case (AnchorPass(x, a), AnchorPass(xm, am)) =>
      xm == SD.SwapAnchorL(x) && TreeMirrorRelF(a, am)
    case (GroupActionT(ga, a), GroupActionT(gam, am)) =>
      TM.GroupActionMirror(ga, gam) && TreeMirrorRelF(a, am)
    case (LK(lk, tlk, tc), LK(lkm, tlkm, tcm)) =>
      (lk.LookBehind? || lk.NegLookBehind?) && lkm == FR.FlipLk(lk)
      && TreeMirrorRelF(tlk, tlkm) && TreeMirrorRelF(tc, tcm)
    case (LKFail(lk, tlk), LKFail(lkm, tlkm)) =>
      (lk.LookBehind? || lk.NegLookBehind?) && lkm == FR.FlipLk(lk)
      && TreeMirrorRelF(tlk, tlkm)
    case _ => false
  }

  // ===========================================================================
  // The SOMENESS fold: success mirrors at ANY pair of group maps
  // ===========================================================================

  /** Relation-related trees succeed or fail TOGETHER, at ANY two (unrelated)
      group maps: success is gm-blind for backreference-free trees, and the
      relation has no `ReadBackRef` case. This is the gate-verdict fact the
      builder's look case needs — with the flip, the two look sub-walks are
      related TREES, so their verdicts agree structurally (no oracle, no
      close-discipline hypotheses). */
  lemma TreeResSomeMirrorF(t: LT.Tree, tm: LT.Tree, gm1: LG.GroupMap, gm2: LG.GroupMap,
                           inp: LC.Input)
    requires TreeMirrorRelF(t, tm)
    ensures LT.TreeRes(t, gm1, inp, WP.Backward).Some?
        <==> LT.TreeRes(tm, gm2, SD.SwapInput(inp), WP.Forward).Some?
    decreases t
  {
    var sinp := SD.SwapInput(inp);
    match t
    case Mismatch =>
    case Match =>
    case Choice(a, b) =>
      match tm {
        case Choice(am, bm) =>
          TreeResSomeMirrorF(a, am, gm1, gm2, inp);
          TreeResSomeMirrorF(b, bm, gm1, gm2, inp);
        case _ =>
      }
    case Read(c, a) =>
      match tm {
        case Read(cm, am) =>
          var inp' := LC.AdvanceInputP(inp, WP.Backward);
          TRM.AdvanceInputPSwap(inp);
          assert LC.AdvanceInputP(sinp, WP.Forward) == SD.SwapInput(inp');
          TreeResSomeMirrorF(a, am, gm1, gm2, inp');
        case _ =>
      }
    case Progress(a) =>
      match tm { case Progress(am) => TreeResSomeMirrorF(a, am, gm1, gm2, inp); case _ => }
    case AnchorPass(x, a) =>
      match tm { case AnchorPass(xm, am) => TreeResSomeMirrorF(a, am, gm1, gm2, inp); case _ => }
    case GroupActionT(ga, a) =>
      match tm {
        case GroupActionT(gam, am) =>
          TreeResSomeMirrorF(a, am, LG.GMUpdate(ga, LC.Idx(inp), gm1),
                             LG.GMUpdate(gam, LC.Idx(sinp), gm2), inp);
        case _ =>
      }
    case LK(lk, tlk, tc) =>
      match tm {
        case LK(lkm, tlkm, tcm) =>
          assert L.LkDir(lk) == WP.Backward && L.LkDir(lkm) == WP.Forward;
          assert L.Positivity(lkm) == L.Positivity(lk);
          TreeResSomeMirrorF(tlk, tlkm, gm1, gm2, inp);
          var sb := LT.TreeRes(tlk, gm1, inp, WP.Backward);
          var sf := LT.TreeRes(tlkm, gm2, sinp, WP.Forward);
          if L.Positivity(lk) {
            match sb {
              case Some(pair) =>
                TreeResSomeMirrorF(tc, tcm, pair.1, sf.value.1, inp);
              case None =>
            }
          } else {
            match sb {
              case None => TreeResSomeMirrorF(tc, tcm, gm1, gm2, inp);
              case Some(_) =>
            }
          }
        case _ =>
      }
    case LKFail(_, _) =>
    case ReadBackRef(_, _) =>
  }

  // ===========================================================================
  // Fuel transport: both sides burn fuel in lockstep
  // ===========================================================================

  /** The worst-case input commutes with the swap. */
  lemma WorstInputSwap(inp: LC.Input)
    ensures FS.WorstInput(SD.SwapInput(inp), WP.Forward)
         == SD.SwapInput(FS.WorstInput(inp, WP.Backward))
  {}

  /** `RegexFuel` is invariant under the flip reversal — including through
      look nodes, where the flipped `LkDir` re-orients the recursion exactly
      onto the swapped worst input. */
  lemma RegexFuelFlipRev(r: L.Regex, inp: LC.Input)
    requires SD.GroupOkLB(r)
    ensures FS.RegexFuel(FlipRevL(r), SD.SwapInput(inp), WP.Forward)
         == FS.RegexFuel(r, inp, WP.Backward)
    decreases r
  {
    match r
    case Disjunction(r1, r2) =>
      RegexFuelFlipRev(r1, inp); RegexFuelFlipRev(r2, inp);
    case Sequence(r1, r2) =>
      RegexFuelFlipRev(r1, inp); RegexFuelFlipRev(r2, inp);
      assert FlipRevL(r) == L.Sequence(FlipRevL(r2), FlipRevL(r1));
    case Quantified(b, min, delta, r1) =>
      RegexFuelFlipRev(r1, inp);
      SD.MaxIterSwap(inp);
    case Group(_, r1) => RegexFuelFlipRev(r1, inp);
    case LookaroundR(lk, r1) =>
      assert (lk.LookBehind? || lk.NegLookBehind?) && SD.GroupOkLB(r1);
      assert FlipRevL(r) == L.LookaroundR(FR.FlipLk(lk), FlipRevL(r1));
      assert L.LkDir(lk) == WP.Backward && L.LkDir(FR.FlipLk(lk)) == WP.Forward;
      var w := FS.WorstInput(inp, WP.Backward);
      WorstInputSwap(inp);
      RegexFuelFlipRev(r1, w);
    case _ =>
  }

  /** `ActionsFuel` is invariant under the flip reversal of the whole stack. */
  lemma ActionsFuelFlipRev(acts: LS.Actions, inp: LC.Input)
    requires GroupOkLBActs(acts)
    ensures FS.ActionsFuel(FlipRevActs(acts), SD.SwapInput(inp), WP.Forward)
         == FS.ActionsFuel(acts, inp, WP.Backward)
    decreases |acts|
  {
    if |acts| == 0 {
      assert FlipRevActs(acts) == [];
      return;
    }
    GroupOkLBActsTail(acts);
    FlipRevActsTail(acts);
    assert FlipRevActs(acts)[0] ==
      (match acts[0] case Areg(r) => LS.Areg(FlipRevL(r))
                     case Acheck(ip) => LS.Acheck(SD.SwapInput(ip))
                     case Aclose(g) => LS.Aclose(g));
    match acts[0]
    case Areg(r) =>
      RegexFuelFlipRev(r, inp);
      ActionsFuelFlipRev(acts[1..], inp);
    case Aclose(g) =>
      ActionsFuelFlipRev(acts[1..], inp);
    case Acheck(ip) =>
      SD.AdvanceInputSwap(ip);
      match LC.AdvanceInput(ip, WP.Backward) {
        case None =>
        case Some(ni) => ActionsFuelFlipRev(acts[1..], ni);
      }
  }

  // ===========================================================================
  // THE BUILDER
  // ===========================================================================

  /** The flip tree correspondence: a backward `ComputeTree` of a `GroupOkLB`
      stack and the forward `ComputeTree` of the FLIP-reversed stack over the
      swapped input run out of fuel together and — when they complete —
      produce `TreeMirrorRelF` trees, at ANY pair of (unrelated) group maps.
      The `LookaroundR` case is REAL: the two look sub-walks mirror by the
      same induction (both flavours), their verdicts agree by
      `TreeResSomeMirrorF`, and the continuations recurse at the (unrelated)
      post-gate maps. */
  lemma ComputeTreeReverseF(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                            gm1: LG.GroupMap, gm2: LG.GroupMap, fuel: nat)
    requires GroupOkLBActs(acts)
    ensures var b := FS.ComputeTree(rer, acts, inp, gm1, WP.Backward, fuel);
            var fw := FS.ComputeTree(rer, FlipRevActs(acts), SD.SwapInput(inp), gm2,
                                     WP.Forward, fuel);
            (b.None? <==> fw.None?)
            && (b.Some? && fw.Some? ==> TreeMirrorRelF(b.value, fw.value))
    decreases fuel
  {
    var racts := FlipRevActs(acts);
    var sinp := SD.SwapInput(inp);
    if fuel == 0 { return; }
    var f := fuel - 1;
    if |acts| == 0 {
      assert racts == [];
      return;
    }
    var cont := acts[1..];
    GroupOkLBActsTail(acts);
    FlipRevActsTail(acts);
    assert racts[1..] == FlipRevActs(cont);
    match acts[0]
    case Acheck(strcheck) =>
      assert racts[0] == LS.Acheck(SD.SwapInput(strcheck));
      SD.IsStrictSuffixSwap(inp, strcheck);
      if SSx.IsStrictSuffix(inp, strcheck, WP.Backward) {
        ComputeTreeReverseF(rer, cont, inp, gm1, gm2, f);
      }
    case Aclose(gid) =>
      assert racts[0] == LS.Aclose(gid);
      ComputeTreeReverseF(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm1),
                          LG.GMClose(LC.Idx(sinp), gid, gm2), f);
    case Areg(r) =>
      assert racts[0] == LS.Areg(FlipRevL(r));
      assert SD.GroupOkLB(r);
      match r
      case Epsilon =>
        ComputeTreeReverseF(rer, cont, inp, gm1, gm2, f);
      case Character(cd) =>
        SD.ReadCharSwap(rer, cd, inp);
        match LC.ReadChar(rer, cd, inp, WP.Backward) {
          case Some(pair) =>
            ComputeTreeReverseF(rer, cont, pair.1, gm1, gm2, f);
          case None =>
        }
      case Disjunction(r1, r2) =>
        assert FlipRevL(r) == L.Disjunction(FlipRevL(r1), FlipRevL(r2));
        GroupOkLBActsCons(LS.Areg(r1), cont);
        GroupOkLBActsCons(LS.Areg(r2), cont);
        FlipRevActsCons(LS.Areg(r1), cont);
        FlipRevActsCons(LS.Areg(r2), cont);
        ComputeTreeReverseF(rer, [LS.Areg(r1)] + cont, inp, gm1, gm2, f);
        ComputeTreeReverseF(rer, [LS.Areg(r2)] + cont, inp, gm1, gm2, f);
      case Sequence(r1, r2) =>
        assert FlipRevL(r) == L.Sequence(FlipRevL(r2), FlipRevL(r1));
        assert LS.SeqList(r1, r2, WP.Backward) == [LS.Areg(r2), LS.Areg(r1)];
        assert LS.SeqList(FlipRevL(r2), FlipRevL(r1), WP.Forward)
            == [LS.Areg(FlipRevL(r2)), LS.Areg(FlipRevL(r1))];
        assert FlipRevActs([LS.Areg(r2), LS.Areg(r1)])
            == [LS.Areg(FlipRevL(r2)), LS.Areg(FlipRevL(r1))];
        FlipRevActsAppend([LS.Areg(r2), LS.Areg(r1)], cont);
        GroupOkLBActsCons(LS.Areg(r1), cont);
        GroupOkLBActsCons(LS.Areg(r2), [LS.Areg(r1)] + cont);
        assert [LS.Areg(r2), LS.Areg(r1)] + cont == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
        ComputeTreeReverseF(rer, [LS.Areg(r2), LS.Areg(r1)] + cont, inp, gm1, gm2, f);
      case Quantified(greedy, min, delta, r1) =>
        assert FlipRevL(r) == L.Quantified(greedy, min, delta, FlipRevL(r1));
        var gidl := L.DefGroups(r1);
        var gidlm := L.DefGroups(FlipRevL(r1));
        FlipRevLDefGroupsSet(r1);
        if min > 0 {
          var q1 := L.Quantified(greedy, min - 1, delta, r1);
          assert FlipRevL(q1) == L.Quantified(greedy, min - 1, delta, FlipRevL(r1));
          GroupOkLBActsCons(LS.Areg(q1), cont);
          GroupOkLBActsCons(LS.Areg(r1), [LS.Areg(q1)] + cont);
          FlipRevActsAppend([LS.Areg(r1), LS.Areg(q1)], cont);
          assert FlipRevActs([LS.Areg(r1), LS.Areg(q1)])
              == [LS.Areg(FlipRevL(r1)), LS.Areg(FlipRevL(q1))];
          assert [LS.Areg(r1), LS.Areg(q1)] + cont == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
          ComputeTreeReverseF(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp,
                              LG.GMReset(gidl, gm1), LG.GMReset(gidlm, gm2), f);
          var bi := FS.ComputeTree(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp,
                                   LG.GMReset(gidl, gm1), WP.Backward, f);
          var fi := FS.ComputeTree(rer, FlipRevActs([LS.Areg(r1), LS.Areg(q1)] + cont), sinp,
                                   LG.GMReset(gidlm, gm2), WP.Forward, f);
          if bi.Some? && fi.Some? {
            assert TM.GroupActionMirror(LG.Reset(gidl), LG.Reset(gidlm));
            assert TreeMirrorRelF(LT.GroupActionT(LG.Reset(gidl), bi.value),
                                  LT.GroupActionT(LG.Reset(gidlm), fi.value));
          }
        } else if delta == LN.NN(0) {
          ComputeTreeReverseF(rer, cont, inp, gm1, gm2, f);
        } else {
          var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          assert FlipRevL(q0) == L.Quantified(greedy, 0, FS.NoiPred(delta), FlipRevL(r1));
          GroupOkLBActsCons(LS.Areg(q0), cont);
          GroupOkLBActsCons(LS.Acheck(inp), [LS.Areg(q0)] + cont);
          GroupOkLBActsCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
          FlipRevActsAppend([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)], cont);
          assert FlipRevActs([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)])
              == [LS.Areg(FlipRevL(r1)), LS.Acheck(sinp), LS.Areg(FlipRevL(q0))];
          assert [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont
              == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
          ComputeTreeReverseF(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, inp,
                              LG.GMReset(gidl, gm1), LG.GMReset(gidlm, gm2), f);
          ComputeTreeReverseF(rer, cont, inp, gm1, gm2, f);
          var bi := FS.ComputeTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont,
                                   inp, LG.GMReset(gidl, gm1), WP.Backward, f);
          var fi := FS.ComputeTree(rer, FlipRevActs([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont),
                                   sinp, LG.GMReset(gidlm, gm2), WP.Forward, f);
          var bs := FS.ComputeTree(rer, cont, inp, gm1, WP.Backward, f);
          var fs := FS.ComputeTree(rer, FlipRevActs(cont), sinp, gm2, WP.Forward, f);
          if bi.Some? && bs.Some? && fi.Some? && fs.Some? {
            assert TM.GroupActionMirror(LG.Reset(gidl), LG.Reset(gidlm));
            assert TreeMirrorRelF(LT.GroupActionT(LG.Reset(gidl), bi.value),
                                  LT.GroupActionT(LG.Reset(gidlm), fi.value));
            assert TreeMirrorRelF(bs.value, fs.value);
          }
        }
      case Group(gid, r1) =>
        assert FlipRevL(r) == L.Group(gid, FlipRevL(r1));
        GroupOkLBActsCons(LS.Aclose(gid), cont);
        GroupOkLBActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        FlipRevActsAppend([LS.Areg(r1), LS.Aclose(gid)], cont);
        assert FlipRevActs([LS.Areg(r1), LS.Aclose(gid)])
            == [LS.Areg(FlipRevL(r1)), LS.Aclose(gid)];
        assert [LS.Areg(r1), LS.Aclose(gid)] + cont
            == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
        ComputeTreeReverseF(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp,
                            LG.GMOpen(LC.Idx(inp), gid, gm1),
                            LG.GMOpen(LC.Idx(sinp), gid, gm2), f);
      case LookaroundR(lk, r1) =>
        // THE REAL CASE — the one the kind-preserving mirror provably lacks.
        assert (lk.LookBehind? || lk.NegLookBehind?) && SD.GroupOkLB(r1);
        assert FlipRevL(r) == L.LookaroundR(FR.FlipLk(lk), FlipRevL(r1));
        assert L.LkDir(lk) == WP.Backward && L.LkDir(FR.FlipLk(lk)) == WP.Forward;
        assert L.Positivity(FR.FlipLk(lk)) == L.Positivity(lk);
        // the two look sub-walks mirror (same induction, one fuel down)
        assert GroupOkLBActs([LS.Areg(r1)]);
        assert FlipRevActs([LS.Areg(r1)]) == [LS.Areg(FlipRevL(r1))];
        ComputeTreeReverseF(rer, [LS.Areg(r1)], inp, gm1, gm2, f);
        var bl := FS.ComputeTree(rer, [LS.Areg(r1)], inp, gm1, WP.Backward, f);
        var fl := FS.ComputeTree(rer, [LS.Areg(FlipRevL(r1))], sinp, gm2, WP.Forward, f);
        if bl.Some? {
          assert fl.Some? && TreeMirrorRelF(bl.value, fl.value);
          // the gate verdicts agree: success of related trees is gm-blind
          TreeResSomeMirrorF(bl.value, fl.value, gm1, gm2, inp);
          var vb := LS.LkResult(lk, bl.value, gm1, inp);
          var vf := LS.LkResult(FR.FlipLk(lk), fl.value, gm2, sinp);
          assert vb.Some? <==> vf.Some?;
          match vb {
            case Some(gmlk) =>
              var gmlk2 := vf.value;
              ComputeTreeReverseF(rer, cont, inp, gmlk, gmlk2, f);
              var bc := FS.ComputeTree(rer, cont, inp, gmlk, WP.Backward, f);
              var fc := FS.ComputeTree(rer, FlipRevActs(cont), sinp, gmlk2, WP.Forward, f);
              if bc.Some? && fc.Some? {
                assert TreeMirrorRelF(LT.LK(lk, bl.value, bc.value),
                                      LT.LK(FR.FlipLk(lk), fl.value, fc.value));
              }
            case None =>
              assert TreeMirrorRelF(LT.LKFail(lk, bl.value),
                                    LT.LKFail(FR.FlipLk(lk), fl.value));
          }
        }
      case AnchorR(a) =>
        assert FlipRevL(r) == L.AnchorR(SD.SwapAnchorL(a));
        SD.AnchorSatisfiedSwap(rer, a, inp);
        if LS.AnchorSatisfied(rer, a, inp) {
          ComputeTreeReverseF(rer, cont, inp, gm1, gm2, f);
        }
      case Backreference(gid) =>
        assert SD.GroupOkLB(r);
        assert false;
  }

  // ===========================================================================
  // The fuel-free corollary
  // ===========================================================================

  /** `ComputeTr`-level form: the backward tree of a `GroupOkLB` stack mirrors
      the forward tree of the FLIP-reversed stack over the swapped input, at
      ANY pair of group maps. */
  lemma ComputeTrReverseF(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                          gm1: LG.GroupMap, gm2: LG.GroupMap)
    requires GroupOkLBActs(acts)
    ensures TreeMirrorRelF(FU.ComputeTr(rer, acts, inp, gm1, WP.Backward),
                           FU.ComputeTr(rer, FlipRevActs(acts), SD.SwapInput(inp), gm2,
                                        WP.Forward))
  {
    var fb := FS.ActionsFuel(acts, inp, WP.Backward) + 1;
    var ff := FS.ActionsFuel(FlipRevActs(acts), SD.SwapInput(inp), WP.Forward) + 1;
    ActionsFuelFlipRev(acts, inp);
    assert fb == ff;
    FS.FunctionalTerminates(rer, acts, inp, gm1, WP.Backward, fb);
    FS.FunctionalTerminates(rer, FlipRevActs(acts), SD.SwapInput(inp), gm2, WP.Forward, ff);
    ComputeTreeReverseF(rer, acts, inp, gm1, gm2, fb);
  }

  // ===========================================================================
  // ANTI-VACUITY WITNESS: the mirror APPLIES to nested-look stacks
  // ===========================================================================

  /** The hypotheses are satisfiable exactly where the kind-preserving mirror's
      were not: a stack whose regex CONTAINS a capturing nested lookbehind is
      `GroupOkLBActs`, and the builder applies to it outright. (Contrast
      `GateAgreeIsFalse`: the old route's gate hypothesis is UNSATISFIABLE on
      this very shape.) */
  lemma FlipMirrorSatisfiableNested(rer: LW.RegExpRecord, cd: LC.CharDescr, inp: LC.Input,
                                    gm1: LG.GroupMap, gm2: LG.GroupMap)
    ensures var r := L.Sequence(L.LookaroundR(L.LookBehind, L.Group(0, L.Character(cd))),
                                L.Character(cd));
            TreeMirrorRelF(FU.ComputeTr(rer, [LS.Areg(r)], inp, gm1, WP.Backward),
                           FU.ComputeTr(rer, FlipRevActs([LS.Areg(r)]), SD.SwapInput(inp), gm2,
                                        WP.Forward))
  {
    var r := L.Sequence(L.LookaroundR(L.LookBehind, L.Group(0, L.Character(cd))),
                        L.Character(cd));
    assert SD.GroupOkLB(r);
    assert GroupOkLBActs([LS.Areg(r)]);
    ComputeTrReverseF(rer, [LS.Areg(r)], inp, gm1, gm2);
  }
}
