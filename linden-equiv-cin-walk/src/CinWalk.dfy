// §2.5b rung F-c: the ENGINE-SHAPED spec walk tree machine B pairs with.
//
// Machine B (the lift-sim band) runs the code-canonical `TreeRepLkRE` trees
// and keeps, per thread, a raw spec walk tree erasure-equal to its canonical
// one. At a CIN-greedy plus (`r1+`, `r1` CI-nullable) the code forks at the
// head — loop or skip-to-the-stamp — while the spec tree is
// `Reset(gidl); [r1, r1*] + cont`: no erasure relates the two. So the raw
// walk becomes ENGINE-SHAPED (`BoolTreeLkX`): at a CIN-greedy plus with
// `min == 1` it is `Choice(Reset(gidl); ti, Reset(gidl); tc)` — the star's
// iteration and the continuation, the skip arm carrying the stamp's `Reset`
// and NO virtual chain (machine B's stamp is a plain `Reset`; the chain lives
// only in machine A and in the engine's `FReconstructPlus`).
//
// The glue `CinWalkX` builds that tree from the spec tree and proves the two
// agree at the first result OUTSIDE any `G` holding every CIN body's groups
// (rung A at `S = {}` — the CIN bodies' positive looks capture nothing — then
// the chain is invisible outside `G`). The lift's `S` (look groups) is
// disjoint from such a `G`, so machine B's best leaf is the spec's first
// leaf INSIDE `S`; outside `S` the final theorem reads machine A.
/** The engine-shaped walk tree `BoolTreeLkX` and its first-result agreement
    with the spec walk tree (`CinWalkX`). */
module LindenElkCinWalk {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LN = WarblreNumeric
  import LS = Semantics
  import LT = Tree
  import BS = BooleanSemantics
  import FS = FunctionalSemantics
  import FU = FunctionalUtils
  import NUL = LindenElkNullable
  import EL = LindenElkEntryLk
  import CE = LindenElkCheckErase
  import LL = LindenElkLookLeaves
  import NP = LindenElkNulledPlus
  import NB = LindenElkNulledPlusBool

  // ===========================================================================
  // The engine-shaped walk tree
  // ===========================================================================

  /** The CIN-greedy unbounded quantifier: the engine's end-fork scheme with the
      nulled-exit stamp. OPAQUE — `NUL.CINullableL`'s definitional axioms put
      z3 4.14 into a matching loop wherever they are visible. */
  opaque ghost predicate CinGreedyL(greedy: bool, delta: LN.NoI, r1: L.Regex) {
    greedy && delta == LN.Inf && NUL.CINullableL(r1)
  }

  /** The guard's three shapes, for callers that keep `CinGreedyL` opaque. */
  lemma CinGreedyIntro(r1: L.Regex)
    requires NUL.CINullableL(r1)
    ensures CinGreedyL(true, LN.Inf, r1)
  { reveal CinGreedyL; }

  lemma NotCinGreedy(greedy: bool, delta: LN.NoI, r1: L.Regex)
    requires !greedy || delta != LN.Inf || NUL.NonNullableL(r1)
    ensures !CinGreedyL(greedy, delta, r1)
  {
    reveal CinGreedyL;
    if NUL.CINullableL(r1) && NUL.NonNullableL(r1) { NUL.CINotNonNullableL(r1); }
  }

  lemma NotCinGreedyNonNullable(greedy: bool, delta: LN.NoI, r1: L.Regex)
    requires NUL.NonNullableL(r1)
    ensures !CinGreedyL(greedy, delta, r1)
  {
    reveal CinGreedyL;
    if NUL.CINullableL(r1) { NUL.CINotNonNullableL(r1); }
  }

  lemma NotCinGreedyLazy(delta: LN.NoI, r1: L.Regex)
    ensures !CinGreedyL(false, delta, r1)
  { reveal CinGreedyL; }

  lemma NotCinGreedyNN(greedy: bool, k: nat, r1: L.Regex)
    ensures !CinGreedyL(greedy, LN.NN(k), r1)
  { reveal CinGreedyL; }

  /** `EL.BoolTreeLk` with the CIN-greedy plus at `min == 1` in the ENGINE'S
      shape: the head fork's loop arm (the star's iteration at `CannotExit`,
      under `Reset(gidl)`) and its skip arm (the stamp's `Reset(gidl)` over the
      continuation). Every other shape is `BoolTreeLk`'s, verbatim. */
  least predicate BoolTreeLkX(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                              b: BS.LoopBool, t: LT.Tree)
  {
    if |acts| == 0 then t == LT.Match
    else
      var cont := acts[1..];
      match acts[0]
      case Acheck(strcheck) =>
        if b == BS.CanExit then
          (match t case Progress(tc) => BoolTreeLkX(rer, cont, inp, BS.CanExit, tc) case _ => false)
        else
          t == LT.Mismatch
      case Aclose(gid) =>
        (match t case GroupActionT(g, tc) => g == LG.Close(gid) && BoolTreeLkX(rer, cont, inp, b, tc) case _ => false)
      case Areg(r) =>
        match r
        case Epsilon => BoolTreeLkX(rer, cont, inp, b, t)
        case Character(cd) =>
          (match LC.ReadChar(rer, cd, inp, WP.Forward)
           case None => t == LT.Mismatch
           case Some(pair) => (match t case Read(c, tc) => c == pair.0 && BoolTreeLkX(rer, cont, pair.1, BS.CanExit, tc) case _ => false))
        case Disjunction(r1, r2) =>
          (match t case Choice(ta, tb) => BoolTreeLkX(rer, [LS.Areg(r1)] + cont, inp, b, ta) && BoolTreeLkX(rer, [LS.Areg(r2)] + cont, inp, b, tb) case _ => false)
        case Sequence(r1, r2) =>
          BoolTreeLkX(rer, [LS.Areg(r1), LS.Areg(r2)] + cont, inp, b, t)
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min == 1 && CinGreedyL(greedy, delta, r1) then
            // the CIN head fork: loop arm | stamp arm
            (match t
             case Choice(ta, tb) =>
               (match ta
                case GroupActionT(g, ti) =>
                  g == LG.Reset(gidl)
                  && BoolTreeLkX(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont, inp, BS.CannotExit, ti)
                case _ => false)
               && (match tb
                   case GroupActionT(g, tc) => g == LG.Reset(gidl) && BoolTreeLkX(rer, cont, inp, b, tc)
                   case _ => false)
             case _ => false)
          else if min > 0 then
            (match t case GroupActionT(g, tc) => g == LG.Reset(gidl) && BoolTreeLkX(rer, [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont, inp, b, tc) case _ => false)
          else if delta == LN.NN(0) then
            BoolTreeLkX(rer, cont, inp, b, t)
          else
            (match t
             case Choice(ta, tb) =>
               var itert := if greedy then ta else tb;
               var skipt := if greedy then tb else ta;
               (match itert
                case GroupActionT(g, ti) =>
                  g == LG.Reset(gidl)
                  && BoolTreeLkX(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, FS.NoiPred(delta), r1))] + cont, inp, BS.CannotExit, ti)
                  && BoolTreeLkX(rer, cont, inp, b, skipt)
                case _ => false)
             case _ => false)
        case Group(gid, r1) =>
          (match t case GroupActionT(g, tc) => g == LG.Open(gid) && BoolTreeLkX(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, b, tc) case _ => false)
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) then
            (match t case AnchorPass(a2, tc) => a2 == a && BoolTreeLkX(rer, cont, inp, b, tc) case _ => false)
          else
            t == LT.Mismatch
        case LookaroundR(lk, r1) =>
          (match t
           case LK(lk2, tlk, tc) =>
             lk2 == lk && EL.LkGateOk(rer, lk, r1, inp, tlk, true) && BoolTreeLkX(rer, cont, inp, b, tc)
           case LKFail(lk2, tlk) =>
             lk2 == lk && EL.LkGateOk(rer, lk, r1, inp, tlk, false)
           case _ => false)
        case Backreference(_) => false
  }

  /** Functional determinism: `BoolTreeLkX` is a function of `(acts, inp, b)`
      (mirror of the lift's `BoolTreeLkDeterm`; the CIN arm recurses on both
      arms). */
  least lemma BoolTreeLkXDeterm(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                                b: BS.LoopBool, t1: LT.Tree, t2: LT.Tree)
    requires BoolTreeLkX(rer, acts, inp, b, t1)
    requires BoolTreeLkX(rer, acts, inp, b, t2)
    ensures t1 == t2
  {
    if |acts| == 0 {
    } else {
      var cont := acts[1..];
      match acts[0]
      case Acheck(strcheck) =>
        if b == BS.CanExit {
          match t1 { case Progress(c1) => match t2 { case Progress(c2) =>
                BoolTreeLkXDeterm(rer, cont, inp, BS.CanExit, c1, c2); case _ => } case _ => }
        }
      case Aclose(gid) =>
        match t1 { case GroupActionT(g1, c1) => match t2 { case GroupActionT(g2, c2) =>
              BoolTreeLkXDeterm(rer, cont, inp, b, c1, c2); case _ => } case _ => }
      case Areg(r) =>
        match r
        case Epsilon => BoolTreeLkXDeterm(rer, cont, inp, b, t1, t2);
        case Character(cd) =>
          match LC.ReadChar(rer, cd, inp, WP.Forward) {
            case None =>
            case Some(pair) =>
              match t1 { case Read(cc1, c1) => match t2 { case Read(cc2, c2) =>
                    BoolTreeLkXDeterm(rer, cont, pair.1, BS.CanExit, c1, c2); case _ => } case _ => }
          }
        case Disjunction(r1, r2) =>
          match t1 { case Choice(a1, b1t) => match t2 { case Choice(a2, b2t) =>
                BoolTreeLkXDeterm(rer, [LS.Areg(r1)] + cont, inp, b, a1, a2);
                BoolTreeLkXDeterm(rer, [LS.Areg(r2)] + cont, inp, b, b1t, b2t); case _ => } case _ => }
        case Sequence(r1, r2) =>
          BoolTreeLkXDeterm(rer, [LS.Areg(r1), LS.Areg(r2)] + cont, inp, b, t1, t2);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min == 1 && CinGreedyL(greedy, delta, r1) {
            var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont;
            match t1 { case Choice(a1, s1) => match t2 { case Choice(a2, s2) =>
              match a1 { case GroupActionT(g1, i1) => match a2 { case GroupActionT(g2, i2) =>
                match s1 { case GroupActionT(h1, c1) => match s2 { case GroupActionT(h2, c2) =>
                  BoolTreeLkXDeterm(rer, ia, inp, BS.CannotExit, i1, i2);
                  BoolTreeLkXDeterm(rer, cont, inp, b, c1, c2);
                case _ => } case _ => }
              case _ => } case _ => }
            case _ => } case _ => }
          } else if min > 0 {
            var q1 := L.Quantified(greedy, min - 1, delta, r1);
            match t1 { case GroupActionT(g1, c1) => match t2 { case GroupActionT(g2, c2) =>
                  BoolTreeLkXDeterm(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp, b, c1, c2); case _ => } case _ => }
          } else if delta == LN.NN(0) {
            BoolTreeLkXDeterm(rer, cont, inp, b, t1, t2);
          } else {
            var qn := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
            var iacts := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(qn)] + cont;
            match t1 {
              case Choice(a1, b1t) =>
                match t2 {
                  case Choice(a2, b2t) =>
                    var it1 := if greedy then a1 else b1t;  var sk1 := if greedy then b1t else a1;
                    var it2 := if greedy then a2 else b2t;  var sk2 := if greedy then b2t else a2;
                    match it1 {
                      case GroupActionT(g1, ti1) =>
                        match it2 {
                          case GroupActionT(g2, ti2) =>
                            BoolTreeLkXDeterm(rer, iacts, inp, BS.CannotExit, ti1, ti2);
                            BoolTreeLkXDeterm(rer, cont, inp, b, sk1, sk2);
                          case _ =>
                        }
                      case _ =>
                    }
                  case _ =>
                }
              case _ =>
            }
          }
        case Group(gid, r1) =>
          match t1 { case GroupActionT(g1, c1) => match t2 { case GroupActionT(g2, c2) =>
                BoolTreeLkXDeterm(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, b, c1, c2); case _ => } case _ => }
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) {
            match t1 { case AnchorPass(a1, c1) => match t2 { case AnchorPass(a2, c2) =>
                  BoolTreeLkXDeterm(rer, cont, inp, b, c1, c2); case _ => } case _ => }
          }
        case LookaroundR(lk, r1) =>
          var tlkc := FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
          match t1 {
            case LK(l1, k1, c1) =>
              assert k1 == tlkc;
              match t2 {
                case LK(l2, k2, c2) =>
                  assert k2 == tlkc;
                  BoolTreeLkXDeterm(rer, cont, inp, b, c1, c2);
                case LKFail(l2, k2) =>
                  assert k2 == tlkc;
                  assert false;
                case _ =>
              }
            case LKFail(l1, k1) =>
              assert k1 == tlkc;
              match t2 {
                case LK(l2, k2, c2) => assert k2 == tlkc; assert false;
                case LKFail(l2, k2) => assert k2 == tlkc;
                case _ =>
              }
            case _ =>
          }
        case Backreference(_) =>
    }
  }

  /** `CE.BoolFlagLiftRec` for the engine-shaped tree: on a shielded stack the
      `CannotExit` tree is also the `CanExit` one (the do-while's lift). */
  lemma BoolFlagLiftRecX(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input, t: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires CE.ShieldedActs(acts)
    requires BoolTreeLkX(rer, acts, inp, BS.CannotExit, t)
    ensures BoolTreeLkX(rer, acts, inp, BS.CanExit, t)
    decreases LS.TreeSize(t), LS.ActionsRegexSize(acts)
  {
    if |acts| == 0 { return; }
    var cont := acts[1..];
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + cont;
    match acts[0]
    case Acheck(strcheck) =>
      // a shielded list cannot have an Acheck at its head
      var j :| 0 <= j < 0 && acts[j].Areg? && NUL.NonNullableL(acts[j].r);
    case Aclose(gid) =>
      match t {
        case GroupActionT(g, tc) =>
          CE.ShieldedTail(acts);
          BoolFlagLiftRecX(rer, cont, inp, tc);
        case _ =>
      }
    case Areg(r) =>
      assert EL.PikeLkRegexRec(r);
      match r
      case Epsilon =>
        CE.ShieldedTail(acts);
        assert LS.ActionsRegexSize(cont) < LS.ActionsRegexSize(acts);
        BoolFlagLiftRecX(rer, cont, inp, t);
      case Character(cd) =>
        // the flags converge at the read: the sub-derivation is shared
        match LC.ReadChar(rer, cd, inp, WP.Forward) {
          case None =>
          case Some(pair) =>
        }
      case Disjunction(r1, r2) =>
        match t {
          case Choice(ta, tb) =>
            var la := [LS.Areg(r1)] + cont;
            var lb := [LS.Areg(r2)] + cont;
            EL.PikeLkActionsRecConsIff(LS.Areg(r1), cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
            assert NUL.NonNullableL(r) ==> NUL.NonNullableL(r1) && NUL.NonNullableL(r2);
            CE.ShieldedCons([LS.Areg(r1)], acts);
            CE.ShieldedCons([LS.Areg(r2)], acts);
            BoolFlagLiftRecX(rer, la, inp, ta);
            BoolFlagLiftRecX(rer, lb, inp, tb);
          case _ =>
        }
      case Sequence(r1, r2) =>
        var ln := [LS.Areg(r1), LS.Areg(r2)] + cont;
        EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
        EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        assert ln == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        var sparts := [LS.Areg(r1), LS.Areg(r2)];
        if NUL.NonNullableL(r) {
          if NUL.NonNullableL(r1) {
            assert sparts[0].Areg? && NUL.NonNullableL(sparts[0].r);
          } else {
            assert NUL.NonNullableL(r2);
            assert sparts[1].Areg? && NUL.NonNullableL(sparts[1].r);
          }
        }
        CE.ShieldedCons(sparts, acts);
        assert LS.ActionsRegexSize(ln) < LS.ActionsRegexSize(acts);
        BoolFlagLiftRecX(rer, ln, inp, t);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        if min == 1 && CinGreedyL(greedy, delta, r1) {
          // the CIN head: the loop arm is pushed at CannotExit by both
          // derivations (shared); the stamp arm lifts with the continuation
          match t {
            case Choice(ta, tb) =>
              match tb {
                case GroupActionT(h, tc) =>
                  assert !NUL.NonNullableL(r) by {
                    reveal CinGreedyL;
                    NUL.CINotNonNullableL(r1);
                  }
                  CE.ShieldedTail(acts);
                  assert LS.TreeSize(tc) < LS.TreeSize(t);
                  BoolFlagLiftRecX(rer, cont, inp, tc);
                case _ =>
              }
            case _ =>
          }
        } else if min > 0 {
          match t {
            case GroupActionT(g, tc) =>
              var q1 := L.Quantified(greedy, min - 1, delta, r1);
              var ln := [LS.Areg(r1), LS.Areg(q1)] + cont;
              EL.PikeLkActionsRecConsIff(LS.Areg(q1), cont);
              EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(q1)] + cont);
              assert ln == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
              assert NUL.NonNullableL(r) ==> NUL.NonNullableL(r1);
              CE.ShieldedCons([LS.Areg(r1), LS.Areg(q1)], acts);
              assert LS.TreeSize(tc) < LS.TreeSize(t);
              BoolFlagLiftRecX(rer, ln, inp, tc);
            case _ =>
          }
        } else if delta == LN.NN(0) {
          CE.ShieldedTail(acts);
          assert LS.ActionsRegexSize(cont) < LS.ActionsRegexSize(acts);
          BoolFlagLiftRecX(rer, cont, inp, t);
        } else {
          match t {
            case Choice(ta, tb) =>
              var itert := if greedy then ta else tb;
              var skipt := if greedy then tb else ta;
              match itert {
                case GroupActionT(g, ti) =>
                  // iteration subtree: pushed at CannotExit by both
                  // derivations â€” shared verbatim, no recursion.
                  CE.ShieldedTail(acts);
                  assert LS.TreeSize(skipt) < LS.TreeSize(t);
                  BoolFlagLiftRecX(rer, cont, inp, skipt);
                case _ =>
              }
            case _ =>
          }
        }
      case Group(gid, r1) =>
        match t {
          case GroupActionT(g, tc) =>
            var ln := [LS.Areg(r1), LS.Aclose(gid)] + cont;
            EL.PikeLkActionsRecConsIff(LS.Aclose(gid), cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
            assert ln == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
            assert NUL.NonNullableL(r) ==> NUL.NonNullableL(r1);
            CE.ShieldedCons([LS.Areg(r1), LS.Aclose(gid)], acts);
            assert LS.TreeSize(tc) < LS.TreeSize(t);
            BoolFlagLiftRecX(rer, ln, inp, tc);
          case _ =>
        }
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) {
          match t {
            case AnchorPass(a2, tc) =>
              CE.ShieldedTail(acts);
              BoolFlagLiftRecX(rer, cont, inp, tc);
            case _ =>
          }
        }
      case LookaroundR(lk, r1) =>
        // the gate does not read the loop flag; lift under it
        match t {
          case LK(lk2, tlk, tc) =>
            CE.ShieldedTail(acts);
            BoolFlagLiftRecX(rer, cont, inp, tc);
          case _ =>
        }
      case Backreference(_) =>
  }

  /** `CE.BoolCheckInsertK` for the engine-shaped tree (the do-while seam's
      check insertion): the tree with the check inserted after `pre` exists,
      has the same size, and erases to the same tree. */
  lemma BoolCheckInsertKX(rer: LW.RegExpRecord, pre: LS.Actions, chk: LC.Input, rest: LS.Actions,
                       inp: LC.Input, b: BS.LoopBool, t: LT.Tree) returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(pre)
    requires CE.ConsumesBeforeAreg(pre) || CE.AcheckIn(pre) || b == BS.CanExit
    requires BoolTreeLkX(rer, pre + rest, inp, b, t)
    ensures BoolTreeLkX(rer, pre + [LS.Acheck(chk)] + rest, inp, b, tstar)
    ensures CE.PSize(tstar) == CE.PSize(t)
    ensures CE.ProgErase(tstar) == CE.ProgErase(t)
    decreases LS.TreeSize(t), LS.ActionsRegexSize(pre)
  {
    if |pre| == 0 {
      assert !CE.ConsumesBeforeAreg(pre) && !CE.AcheckIn(pre);
      assert b == BS.CanExit;
      assert pre + rest == rest;
      assert pre + [LS.Acheck(chk)] + rest == [LS.Acheck(chk)] + rest;
      assert ([LS.Acheck(chk)] + rest)[0] == LS.Acheck(chk)
          && ([LS.Acheck(chk)] + rest)[1..] == rest;
      tstar := LT.Progress(t);
    } else {
      assert (pre + rest)[0] == pre[0] && (pre + rest)[1..] == pre[1..] + rest;
      assert (pre + [LS.Acheck(chk)] + rest)[0] == pre[0]
          && (pre + [LS.Acheck(chk)] + rest)[1..] == pre[1..] + [LS.Acheck(chk)] + rest;
      assert EL.PikeLkActionRec(pre[0]);
      assert EL.PikeLkActionsRec(pre[1..]) by {
        forall i | 0 <= i < |pre[1..]| ensures EL.PikeLkActionRec(pre[1..][i]) {
          assert pre[1..][i] == pre[i + 1];
        }
      }
      match pre[0]
      case Acheck(c2) =>
        if b == BS.CanExit {
          match t {
            case Progress(tc) =>
              var sub := BoolCheckInsertKX(rer, pre[1..], chk, rest, inp, BS.CanExit, tc);
              tstar := LT.Progress(sub);
            case _ =>
          }
        } else {
          // check fails on both sides identically
          tstar := LT.Mismatch;
        }
      case Aclose(gid) =>
        match t {
          case GroupActionT(g, tc) =>
            if CE.ConsumesBeforeAreg(pre) { CE.ConsumesTailC(pre); }
            if CE.AcheckIn(pre) && !(CE.ConsumesBeforeAreg(pre[1..]) || b == BS.CanExit) { CE.AcheckInTail(pre); }
            var sub := BoolCheckInsertKX(rer, pre[1..], chk, rest, inp, b, tc);
            tstar := LT.GroupActionT(g, sub);
          case _ =>
        }
      case Areg(r) =>
        assert EL.PikeLkRegexRec(r);
        match r
        case Epsilon =>
          if CE.ConsumesBeforeAreg(pre) { CE.ConsumesTailC(pre); }
          if CE.AcheckIn(pre) && !(CE.ConsumesBeforeAreg(pre[1..]) || b == BS.CanExit) { CE.AcheckInTail(pre); }
          tstar := BoolCheckInsertKX(rer, pre[1..], chk, rest, inp, b, t);
        case Character(cd) =>
          match LC.ReadChar(rer, cd, inp, WP.Forward) {
            case Some(pair) =>
              match t {
                case Read(c, tc) =>
                  var sub := BoolCheckInsertKX(rer, pre[1..], chk, rest, pair.1, BS.CanExit, tc);
                  tstar := LT.Read(c, sub);
                case _ =>
              }
            case None =>
              tstar := LT.Mismatch;
          }
        case Disjunction(r1, r2) =>
          match t {
            case Choice(ta, tb) =>
              var pa := [LS.Areg(r1)] + pre[1..];
              var pb := [LS.Areg(r2)] + pre[1..];
              assert pa + rest == [LS.Areg(r1)] + (pre[1..] + rest);
              assert pb + rest == [LS.Areg(r2)] + (pre[1..] + rest);
              assert pa + [LS.Acheck(chk)] + rest == [LS.Areg(r1)] + (pre[1..] + [LS.Acheck(chk)] + rest);
              assert pb + [LS.Acheck(chk)] + rest == [LS.Areg(r2)] + (pre[1..] + [LS.Acheck(chk)] + rest);
              assert EL.PikeLkActionsRec(pa) by {
                forall i | 0 <= i < |pa| ensures EL.PikeLkActionRec(pa[i]) { if i > 0 { assert pa[i] == pre[i]; } }
              }
              assert EL.PikeLkActionsRec(pb) by {
                forall i | 0 <= i < |pb| ensures EL.PikeLkActionRec(pb[i]) { if i > 0 { assert pb[i] == pre[i]; } }
              }
              if CE.ConsumesBeforeAreg(pre) && !(pre[0].Areg? && NUL.NonNullableL(pre[0].r)) {
                CE.ConsumesTailC(pre);
                CE.ConsumesPrepend([LS.Areg(r1)], pre[1..]);
                CE.ConsumesPrepend([LS.Areg(r2)], pre[1..]);
              }
              if CE.ConsumesBeforeAreg(pre) && pre[0].Areg? && NUL.NonNullableL(pre[0].r) {
                assert CE.ConsumesBeforeAreg(pa) by { assert pa[0] == LS.Areg(r1); }
                assert CE.ConsumesBeforeAreg(pb) by { assert pb[0] == LS.Areg(r2); }
              }
              if CE.AcheckIn(pre) && !(CE.ConsumesBeforeAreg(pre) || b == BS.CanExit) {
                CE.AcheckInTail(pre);
                CE.AcheckInPrepend([LS.Areg(r1)], pre[1..]);
                CE.AcheckInPrepend([LS.Areg(r2)], pre[1..]);
              }
              var sa := BoolCheckInsertKX(rer, pa, chk, rest, inp, b, ta);
              var sb := BoolCheckInsertKX(rer, pb, chk, rest, inp, b, tb);
              tstar := LT.Choice(sa, sb);
            case _ =>
          }
        case Sequence(r1, r2) =>
          var pn := [LS.Areg(r1), LS.Areg(r2)] + pre[1..];
          assert pn + rest == [LS.Areg(r1), LS.Areg(r2)] + (pre[1..] + rest);
          assert pn + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Areg(r2)] + (pre[1..] + [LS.Acheck(chk)] + rest);
          assert EL.PikeLkActionsRec(pn) by {
            forall i | 0 <= i < |pn| ensures EL.PikeLkActionRec(pn[i]) {
              if i >= 2 { assert pn[i] == pre[i - 1]; }
            }
          }
          if CE.ConsumesBeforeAreg(pre) && !(pre[0].Areg? && NUL.NonNullableL(pre[0].r)) {
            CE.ConsumesTailC(pre);
            CE.ConsumesPrepend([LS.Areg(r1), LS.Areg(r2)], pre[1..]);
          }
          if CE.ConsumesBeforeAreg(pre) && pre[0].Areg? && NUL.NonNullableL(pre[0].r) {
            if NUL.NonNullableL(r1) {
              assert CE.ConsumesBeforeAreg(pn) by { assert pn[0] == LS.Areg(r1); }
            } else {
              assert CE.ConsumesBeforeAreg(pn) by { assert pn[1] == LS.Areg(r2); }
            }
          }
          if CE.AcheckIn(pre) && !(CE.ConsumesBeforeAreg(pre) || b == BS.CanExit) {
            CE.AcheckInTail(pre);
            CE.AcheckInPrepend([LS.Areg(r1), LS.Areg(r2)], pre[1..]);
          }
          assert pre == [pre[0]] + pre[1..];
          assert LS.ActionsRegexSize(pn) < LS.ActionsRegexSize(pre);
          tstar := BoolCheckInsertKX(rer, pn, chk, rest, inp, b, t);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min == 1 && CinGreedyL(greedy, delta, r1) {
            // the CIN head: the loop arm is the star's iteration (a check of its
            // own), the stamp arm the plain continuation
            match t {
              case Choice(ta, tb) =>
                match ta {
                  case GroupActionT(g, ti) =>
                    match tb {
                      case GroupActionT(h, tc) =>
                        var q0 := L.Quantified(true, 0, LN.Inf, r1);
                        var pi := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + pre[1..];
                        assert pi + rest == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + (pre[1..] + rest);
                        assert pi + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + (pre[1..] + [LS.Acheck(chk)] + rest);
                        assert EL.PikeLkActionsRec(pi) by {
                          forall i | 0 <= i < |pi| ensures EL.PikeLkActionRec(pi[i]) {
                            if i >= 3 { assert pi[i] == pre[i - 2]; }
                          }
                        }
                        assert CE.AcheckIn(pi) by { assert pi[1].Acheck?; }
                        assert LS.TreeSize(ti) < LS.TreeSize(t);
                        var si := BoolCheckInsertKX(rer, pi, chk, rest, inp, BS.CannotExit, ti);
                        assert !NUL.NonNullableL(r) by { reveal CinGreedyL; NUL.CINotNonNullableL(r1); }
                        if CE.ConsumesBeforeAreg(pre) { CE.ConsumesTailC(pre); }
                        if CE.AcheckIn(pre) && !(CE.ConsumesBeforeAreg(pre[1..]) || b == BS.CanExit) { CE.AcheckInTail(pre); }
                        assert LS.TreeSize(tc) < LS.TreeSize(t);
                        var ss := BoolCheckInsertKX(rer, pre[1..], chk, rest, inp, b, tc);
                        tstar := LT.Choice(LT.GroupActionT(g, si), LT.GroupActionT(h, ss));
                      case _ =>
                    }
                  case _ =>
                }
              case _ =>
            }
          } else if min > 0 {
            match t {
              case GroupActionT(g, tc) =>
                var q1 := L.Quantified(greedy, min - 1, delta, r1);
                var pn := [LS.Areg(r1), LS.Areg(q1)] + pre[1..];
                assert pn + rest == [LS.Areg(r1), LS.Areg(q1)] + (pre[1..] + rest);
                assert pn + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Areg(q1)] + (pre[1..] + [LS.Acheck(chk)] + rest);
                assert EL.PikeLkActionsRec(pn) by {
                  forall i | 0 <= i < |pn| ensures EL.PikeLkActionRec(pn[i]) {
                    if i >= 2 { assert pn[i] == pre[i - 1]; }
                  }
                }
                if CE.ConsumesBeforeAreg(pre) && !(pre[0].Areg? && NUL.NonNullableL(pre[0].r)) {
                  CE.ConsumesTailC(pre);
                  CE.ConsumesPrepend([LS.Areg(r1), LS.Areg(q1)], pre[1..]);
                }
                if CE.ConsumesBeforeAreg(pre) && pre[0].Areg? && NUL.NonNullableL(pre[0].r) {
                  assert CE.ConsumesBeforeAreg(pn) by { assert pn[0] == LS.Areg(r1); }
                }
                if CE.AcheckIn(pre) && !(CE.ConsumesBeforeAreg(pre) || b == BS.CanExit) {
                  CE.AcheckInTail(pre);
                  CE.AcheckInPrepend([LS.Areg(r1), LS.Areg(q1)], pre[1..]);
                }
                var sub := BoolCheckInsertKX(rer, pn, chk, rest, inp, b, tc);
                tstar := LT.GroupActionT(g, sub);
              case _ =>
            }
          } else if delta == LN.NN(0) {
            if CE.ConsumesBeforeAreg(pre) { CE.ConsumesTailC(pre); }
            if CE.AcheckIn(pre) && !(CE.ConsumesBeforeAreg(pre[1..]) || b == BS.CanExit) { CE.AcheckInTail(pre); }
            tstar := BoolCheckInsertKX(rer, pre[1..], chk, rest, inp, b, t);
          } else {
            match t {
              case Choice(ta, tb) =>
                var itert := if greedy then ta else tb;
                var skipt := if greedy then tb else ta;
                match itert {
                  case GroupActionT(g, ti) =>
                    var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
                    var pi := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + pre[1..];
                    assert pi + rest == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + (pre[1..] + rest);
                    assert pi + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + (pre[1..] + [LS.Acheck(chk)] + rest);
                    assert EL.PikeLkActionsRec(pi) by {
                      forall i | 0 <= i < |pi| ensures EL.PikeLkActionRec(pi[i]) {
                        if i >= 3 { assert pi[i] == pre[i - 2]; }
                      }
                    }
                    assert CE.AcheckIn(pi) by { assert pi[1].Acheck?; }
                    assert LS.TreeSize(ti) < LS.TreeSize(t);
                    var si := BoolCheckInsertKX(rer, pi, chk, rest, inp, BS.CannotExit, ti);
                    // skip branch
                    if CE.ConsumesBeforeAreg(pre) { CE.ConsumesTailC(pre); }
                    if CE.AcheckIn(pre) && !(CE.ConsumesBeforeAreg(pre[1..]) || b == BS.CanExit) { CE.AcheckInTail(pre); }
                    assert LS.TreeSize(skipt) < LS.TreeSize(t);
                    var ss := BoolCheckInsertKX(rer, pre[1..], chk, rest, inp, b, skipt);
                    var istar := LT.GroupActionT(g, si);
                    if greedy {
                      tstar := LT.Choice(istar, ss);
                    } else {
                      tstar := LT.Choice(ss, istar);
                    }
                  case _ =>
                }
              case _ =>
            }
          }
        case Group(gid, r1) =>
          match t {
            case GroupActionT(g, tc) =>
              var pn := [LS.Areg(r1), LS.Aclose(gid)] + pre[1..];
              assert pn + rest == [LS.Areg(r1), LS.Aclose(gid)] + (pre[1..] + rest);
              assert pn + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Aclose(gid)] + (pre[1..] + [LS.Acheck(chk)] + rest);
              assert EL.PikeLkActionsRec(pn) by {
                forall i | 0 <= i < |pn| ensures EL.PikeLkActionRec(pn[i]) {
                  if i >= 2 { assert pn[i] == pre[i - 1]; }
                }
              }
              if CE.ConsumesBeforeAreg(pre) && !(pre[0].Areg? && NUL.NonNullableL(pre[0].r)) {
                CE.ConsumesTailC(pre);
                CE.ConsumesPrepend([LS.Areg(r1), LS.Aclose(gid)], pre[1..]);
              }
              if CE.ConsumesBeforeAreg(pre) && pre[0].Areg? && NUL.NonNullableL(pre[0].r) {
                assert CE.ConsumesBeforeAreg(pn) by { assert pn[0] == LS.Areg(r1); }
              }
              if CE.AcheckIn(pre) && !(CE.ConsumesBeforeAreg(pre) || b == BS.CanExit) {
                CE.AcheckInTail(pre);
                CE.AcheckInPrepend([LS.Areg(r1), LS.Aclose(gid)], pre[1..]);
              }
              var sub := BoolCheckInsertKX(rer, pn, chk, rest, inp, b, tc);
              tstar := LT.GroupActionT(g, sub);
            case _ =>
          }
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) {
            match t {
              case AnchorPass(a2, tc) =>
                if CE.ConsumesBeforeAreg(pre) { CE.ConsumesTailC(pre); }
                if CE.AcheckIn(pre) && !(CE.ConsumesBeforeAreg(pre[1..]) || b == BS.CanExit) { CE.AcheckInTail(pre); }
                var sub := BoolCheckInsertKX(rer, pre[1..], chk, rest, inp, b, tc);
                tstar := LT.AnchorPass(a2, sub);
              case _ =>
            }
          } else {
            tstar := LT.Mismatch;
          }
        case LookaroundR(lk, r1) =>
          // the gate is zero-width: rebuild it around the continuation's
          // inserted-check tree. Both sides carry the SAME body subtree, so
          // LACongLK gives the leaf agreement.
          match t {
            case LK(lk2, tlk, tc) =>
              if CE.ConsumesBeforeAreg(pre) { CE.ConsumesTailC(pre); }
              if CE.AcheckIn(pre) && !(CE.ConsumesBeforeAreg(pre[1..]) || b == BS.CanExit) { CE.AcheckInTail(pre); }
              var sub := BoolCheckInsertKX(rer, pre[1..], chk, rest, inp, b, tc);
              tstar := LT.LK(lk2, tlk, sub);
            case LKFail(lk2, tlk) =>
              tstar := t;
            case _ =>
          }
        case Backreference(_) =>
          assert false;   // not pike
    }
  }

  /** The gate node of the engine-shaped walk (`M.GateNodeAtInp`'s twin). */
  lemma GateNodeAtInpX(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                       b: BS.LoopBool, t: LT.Tree, lk: L.Lookaround, r1: L.Regex)
    requires |acts| > 0 && acts[0] == LS.Areg(L.LookaroundR(lk, r1))
    requires BoolTreeLkX(rer, acts, inp, b, t)
    ensures (t.LK? && t.lk == lk
             && EL.LkGateOk(rer, lk, r1, inp, t.tlk, true)
             && BoolTreeLkX(rer, acts[1..], inp, b, t.t))
            || (t.LKFail? && t.lk == lk && EL.LkGateOk(rer, lk, r1, inp, t.tlk, false))
  {}

  // ===========================================================================
  // The glue's side condition: every CIN body's groups lie in `G`, and its
  // positive looks capture nothing (rung A then runs at `S = {}`)
  // ===========================================================================

  ghost predicate CinOk(r: L.Regex, G: set<LG.GroupId>)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => CinOk(r1, G) && CinOk(r2, G)
    case Sequence(r1, r2) => CinOk(r1, G) && CinOk(r2, G)
    case Quantified(greedy, min, delta, r1) =>
      CinOk(r1, G)
      && (min > 0 && CinGreedyL(greedy, delta, r1) ==>
            LL.LkBodiesInS(r1, {}) && forall g :: g in L.DefGroups(r1) ==> g in G)
    case Group(_, r1) => CinOk(r1, G)
    case LookaroundR(_, r1) => CinOk(r1, G)
    case _ => true
  }

  ghost predicate CinActsIn(acts: LS.Actions, G: set<LG.GroupId>) {
    forall i :: 0 <= i < |acts| ==> (acts[i].Areg? ==> CinOk(acts[i].r, G))
  }

  lemma CinActsInTail(acts: LS.Actions, G: set<LG.GroupId>)
    requires |acts| > 0 && CinActsIn(acts, G)
    ensures CinActsIn(acts[1..], G)
  {
    forall i | 0 <= i < |acts[1..]| ensures acts[1..][i].Areg? ==> CinOk(acts[1..][i].r, G) {
      assert acts[1..][i] == acts[i + 1];
    }
  }

  lemma CinActsInCons(x: LS.Action, cont: LS.Actions, G: set<LG.GroupId>)
    requires (x.Areg? ==> CinOk(x.r, G)) && CinActsIn(cont, G)
    ensures CinActsIn([x] + cont, G)
  {
    forall i | 0 <= i < |[x] + cont| ensures ([x] + cont)[i].Areg? ==> CinOk(([x] + cont)[i].r, G) {
      if i > 0 { assert ([x] + cont)[i] == cont[i - 1]; }
    }
  }

  /** A regex without a nulled plus satisfies the side condition vacuously. */
  lemma NoNulledPlusCinOk(r: L.Regex, G: set<LG.GroupId>)
    requires NUL.NoNulledPlusL(r)
    ensures CinOk(r, G)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => NoNulledPlusCinOk(r1, G); NoNulledPlusCinOk(r2, G);
    case Sequence(r1, r2) => NoNulledPlusCinOk(r1, G); NoNulledPlusCinOk(r2, G);
    case Quantified(greedy, min, delta, r1) =>
      NoNulledPlusCinOk(r1, G);
      if min > 0 && delta.Inf? && greedy { NotCinGreedyNonNullable(greedy, delta, r1); }
      else if min > 0 { NotCinGreedy(greedy, delta, r1); }
    case Group(_, r1) => NoNulledPlusCinOk(r1, G);
    case LookaroundR(_, r1) => NoNulledPlusCinOk(r1, G);
    case _ =>
  }

  lemma CinActsInSingle(r: L.Regex, G: set<LG.GroupId>)
    requires CinOk(r, G)
    ensures CinActsIn([LS.Areg(r)], G)
  {}

  // ===========================================================================
  // First-result toolkit outside a set (beyond rung A's congruences)
  // ===========================================================================

  /** `TreeRes` is a frame: maps agreeing outside `G` give results at the same
      position agreeing outside `G`. */
  lemma TreeResFrameOutside(t: LT.Tree, gm1: LG.GroupMap, gm2: LG.GroupMap, inp: LC.Input,
                            dir: WP.Direction, G: set<LG.GroupId>)
    requires LL.GmAgreeOutside(gm1, gm2, G)
    ensures var r1 := LT.TreeRes(t, gm1, inp, dir);
            var r2 := LT.TreeRes(t, gm2, inp, dir);
            (r1.Some? <==> r2.Some?)
            && (r1.Some? ==> r1.value.0 == r2.value.0 && LL.GmAgreeOutside(r1.value.1, r2.value.1, G))
  {
    LL.TreeLeavesFrameOutside(t, gm1, gm2, inp, dir, G);
    LT.FirstTreeLeaf(t, gm1, inp, dir);
    LT.FirstTreeLeaf(t, gm2, inp, dir);
    var l1 := LT.TreeLeaves(t, gm1, inp, dir);
    var l2 := LT.TreeLeaves(t, gm2, inp, dir);
    if |l1| > 0 {
      assert l1[0].0 == l2[0].0 && LL.GmAgreeOutside(l1[0].1, l2[0].1, G);
    }
  }

  lemma ChainRes(p: seq<LG.GroupAction>, t: LT.Tree, gm: LG.GroupMap, inp: LC.Input)
    ensures LT.TreeRes(NP.Chain(p, t), gm, inp, WP.Forward)
         == LT.TreeRes(t, NP.ApplyPath(p, LC.Idx(inp), gm), inp, WP.Forward)
  {
    NP.ChainLeaves(p, t, gm, inp);
    LT.FirstTreeLeaf(NP.Chain(p, t), gm, inp, WP.Forward);
    LT.FirstTreeLeaf(t, NP.ApplyPath(p, LC.Idx(inp), gm), inp, WP.Forward);
  }

  /** A path whose actions all touch `G` is invisible outside `G`. */
  lemma RAChainDropOutside(p: seq<LG.GroupAction>, t: LT.Tree, inp: LC.Input, G: set<LG.GroupId>)
    requires NP.PathIn(p, G)
    ensures NP.ResAgreeAtOutside(t, NP.Chain(p, t), inp, G)
  {
    forall gm: LG.GroupMap
      ensures var r1 := LT.TreeRes(t, gm, inp, WP.Forward);
              var r2 := LT.TreeRes(NP.Chain(p, t), gm, inp, WP.Forward);
              (r1.Some? <==> r2.Some?)
              && (r1.Some? ==> r1.value.0 == r2.value.0 && LL.GmAgreeOutside(r1.value.1, r2.value.1, G))
    {
      ChainRes(p, t, gm, inp);
      var gmP := NP.ApplyPath(p, LC.Idx(inp), gm);
      NP.ApplyPathOutside(p, LC.Idx(inp), gm, G);
      LL.GmAgreeOutsideSym(gmP, gm, G);
      TreeResFrameOutside(t, gm, gmP, inp, WP.Forward, G);
    }
  }

  lemma RAMonoOutside(t1: LT.Tree, t2: LT.Tree, inp: LC.Input, S: set<LG.GroupId>, G: set<LG.GroupId>)
    requires S <= G
    requires NP.ResAgreeAtOutside(t1, t2, inp, S)
    ensures NP.ResAgreeAtOutside(t1, t2, inp, G)
  {
    forall gm: LG.GroupMap
      ensures var r1 := LT.TreeRes(t1, gm, inp, WP.Forward);
              var r2 := LT.TreeRes(t2, gm, inp, WP.Forward);
              (r1.Some? <==> r2.Some?)
              && (r1.Some? ==> r1.value.0 == r2.value.0 && LL.GmAgreeOutside(r1.value.1, r2.value.1, G))
    {
      var r1 := LT.TreeRes(t1, gm, inp, WP.Forward);
      var r2 := LT.TreeRes(t2, gm, inp, WP.Forward);
      if r1.Some? {
        assert LL.GmAgreeOutside(r1.value.1, r2.value.1, S);
      }
    }
  }

  /** A gate node with the SAME body tree is a congruence (the verdict and the
      continuation's incoming map are shared). */
  lemma RACongLKOutside(lk: L.Lookaround, tlk: LT.Tree, a: LT.Tree, b: LT.Tree, inp: LC.Input, G: set<LG.GroupId>)
    requires NP.ResAgreeAtOutside(a, b, inp, G)
    ensures NP.ResAgreeAtOutside(LT.LK(lk, tlk, a), LT.LK(lk, tlk, b), inp, G)
  {
    forall gm: LG.GroupMap
      ensures var r1 := LT.TreeRes(LT.LK(lk, tlk, a), gm, inp, WP.Forward);
              var r2 := LT.TreeRes(LT.LK(lk, tlk, b), gm, inp, WP.Forward);
              (r1.Some? <==> r2.Some?)
              && (r1.Some? ==> r1.value.0 == r2.value.0 && LL.GmAgreeOutside(r1.value.1, r2.value.1, G))
    {
      var sub := LT.TreeRes(tlk, gm, inp, L.LkDir(lk));
      if L.Positivity(lk) && sub.Some? {
        assert LT.TreeRes(LT.LK(lk, tlk, a), gm, inp, WP.Forward) == LT.TreeRes(a, sub.value.1, inp, WP.Forward);
        assert LT.TreeRes(LT.LK(lk, tlk, b), gm, inp, WP.Forward) == LT.TreeRes(b, sub.value.1, inp, WP.Forward);
      }
    }
  }

  // ===========================================================================
  // THE GLUE
  // ===========================================================================

  function MsizeX(acts: LS.Actions): nat {
    2 * LS.ActionsRegexSize(acts) + |acts|
  }

  /** From the spec walk tree `t` of a fragment stack, BUILD its engine-shaped
      twin and relate the two at the first result outside `G`. */
  lemma CinWalkX(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input, b: BS.LoopBool,
                 t: LT.Tree, G: set<LG.GroupId>)
    returns (tX: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires NB.EncOk(acts, inp, b)
    requires CinActsIn(acts, G)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    ensures BoolTreeLkX(rer, acts, inp, b, tX)
    ensures NP.ResAgreeAtOutside(tX, t, inp, G)
    decreases CE.PSize(t), MsizeX(acts), 3
  {
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL;
    if |acts| == 0 {
      tX := t;
      NP.RAReflOutside(t, inp, G);
      return;
    }
    var cont := acts[1..];
    assert acts == [acts[0]] + cont;
    EL.PikeLkActionsRecTail(acts);
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    CinActsInTail(acts, G);
    match acts[0]
    case Acheck(strcheck) =>
      assert MsizeX(cont) < MsizeX(acts);
      if b == BS.CanExit {
        match t {
          case Progress(tc) =>
            NB.EncOkTailCheck(acts, inp);
            var sub := CinWalkX(rer, cont, inp, BS.CanExit, tc, G);
            tX := LT.Progress(sub);
            NP.RACongProgressOutside(sub, tc, inp, G);
          case _ =>
        }
      } else {
        tX := t;
        NP.RAReflOutside(t, inp, G);
      }
    case Aclose(gid) =>
      match t {
        case GroupActionT(g, tc) =>
          NB.EncOkTailReg(acts, inp, b);
          var sub := CinWalkX(rer, cont, inp, b, tc, G);
          tX := LT.GroupActionT(g, sub);
          NP.RACongGroupOutside(g, sub, tc, inp, G);
        case _ =>
      }
    case Areg(r) =>
      tX := CinWalkReg(rer, acts, cont, r, inp, b, t, G);
  }

  /** The `Areg` shapes. */
  lemma CinWalkReg(rer: LW.RegExpRecord, acts: LS.Actions, cont: LS.Actions, r: L.Regex,
                   inp: LC.Input, b: BS.LoopBool, t: LT.Tree, G: set<LG.GroupId>)
    returns (tX: LT.Tree)
    requires |acts| > 0 && acts[0] == LS.Areg(r) && cont == acts[1..]
    requires EL.PikeLkActionsRec(acts) && EL.PikeLkActionsRec(cont) && EL.PikeLkRegexRec(r)
    requires NB.EncOk(acts, inp, b)
    requires CinActsIn(acts, G) && CinActsIn(cont, G) && CinOk(r, G)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    ensures BoolTreeLkX(rer, acts, inp, b, tX)
    ensures NP.ResAgreeAtOutside(tX, t, inp, G)
    decreases CE.PSize(t), MsizeX(acts), 2
  {
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL;
    assert acts == [acts[0]] + cont;
    match r
    case Epsilon =>
      assert MsizeX(cont) < MsizeX(acts);
      NB.EncOkTailReg(acts, inp, b);
      tX := CinWalkX(rer, cont, inp, b, t, G);
    case Character(cd) =>
      match LC.ReadChar(rer, cd, inp, WP.Forward) {
        case None =>
          tX := t;
          NP.RAReflOutside(t, inp, G);
        case Some(pair) =>
          match t {
            case Read(c, tc) =>
              assert |inp.next| > 0 && pair.1 == LC.Input(inp.next[1..], [inp.next[0]] + inp.pref);
              NB.EncOkRead(acts, inp, b, pair.1);
              var sub := CinWalkX(rer, cont, pair.1, BS.CanExit, tc, G);
              tX := LT.Read(c, sub);
              assert LC.AdvanceInputP(inp, WP.Forward) == pair.1;
              NP.RACongReadOutside(c, sub, tc, inp, G);
            case _ =>
          }
      }
    case Disjunction(r1, r2) =>
      match t {
        case Choice(ta, tb) =>
          var la := [LS.Areg(r1)] + cont;
          var lb := [LS.Areg(r2)] + cont;
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          CinActsInCons(LS.Areg(r1), cont, G);
          CinActsInCons(LS.Areg(r2), cont, G);
          assert NB.EncOk(la, inp, b) by {
            var parts := [LS.Areg(r1)];
            assert parts + cont == la;
            if NUL.NonNullableL(acts[0].r) { reveal NUL.NonNullableL; assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
            NB.EncOkExpand(acts, parts, inp, b);
          }
          assert NB.EncOk(lb, inp, b) by {
            var parts := [LS.Areg(r2)];
            assert parts + cont == lb;
            if NUL.NonNullableL(acts[0].r) { reveal NUL.NonNullableL; assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
            NB.EncOkExpand(acts, parts, inp, b);
          }
          var sa := CinWalkX(rer, la, inp, b, ta, G);
          var sb := CinWalkX(rer, lb, inp, b, tb, G);
          tX := LT.Choice(sa, sb);
          NP.RACongChoiceOutside(sa, ta, sb, tb, inp, G);
        case _ =>
      }
    case Sequence(r1, r2) =>
      var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
      assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
      EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
      EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
      CinActsInCons(LS.Areg(r2), cont, G);
      CinActsInCons(LS.Areg(r1), [LS.Areg(r2)] + cont, G);
      assert LS.ActionsRegexSize(na) < LS.ActionsRegexSize(acts);
      assert MsizeX(na) < MsizeX(acts);
      assert NB.EncOk(na, inp, b) by {
        var parts := [LS.Areg(r1), LS.Areg(r2)];
        assert parts + cont == na;
        if NUL.NonNullableL(acts[0].r) {
          reveal NUL.NonNullableL;
          if NUL.NonNullableL(r1) { assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
          else { assert parts[1].Areg? && NUL.NonNullableL(parts[1].r); }
        }
        NB.EncOkExpand(acts, parts, inp, b);
      }
      tX := CinWalkX(rer, na, inp, b, t, G);
    case Quantified(greedy, min, delta, r1) =>
      tX := CinWalkQuant(rer, acts, cont, greedy, min, delta, r1, inp, b, t, G);
    case Group(gid, r1) =>
      match t {
        case GroupActionT(g, tc) =>
          var ga := [LS.Areg(r1), LS.Aclose(gid)] + cont;
          assert ga == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
          EL.PikeLkActionsRecConsIff(LS.Aclose(gid), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
          CinActsInCons(LS.Aclose(gid), cont, G);
          CinActsInCons(LS.Areg(r1), [LS.Aclose(gid)] + cont, G);
          assert NB.EncOk(ga, inp, b) by {
            var parts := [LS.Areg(r1), LS.Aclose(gid)];
            assert parts + cont == ga;
            if NUL.NonNullableL(acts[0].r) { reveal NUL.NonNullableL; assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
            NB.EncOkExpand(acts, parts, inp, b);
          }
          var sub := CinWalkX(rer, ga, inp, b, tc, G);
          tX := LT.GroupActionT(g, sub);
          NP.RACongGroupOutside(g, sub, tc, inp, G);
        case _ =>
      }
    case AnchorR(a) =>
      if LS.AnchorSatisfied(rer, a, inp) {
        match t {
          case AnchorPass(a2, tc) =>
            NB.EncOkTailReg(acts, inp, b);
            var sub := CinWalkX(rer, cont, inp, b, tc, G);
            tX := LT.AnchorPass(a2, sub);
            NP.RACongAnchorOutside(a2, sub, tc, inp, G);
          case _ =>
        }
      } else {
        tX := t;
        NP.RAReflOutside(t, inp, G);
      }
    case LookaroundR(lk, r1) =>
      match t {
        case LK(lk2, tlk, tc) =>
          NB.EncOkTailReg(acts, inp, b);
          var sub := CinWalkX(rer, cont, inp, b, tc, G);
          tX := LT.LK(lk2, tlk, sub);
          RACongLKOutside(lk2, tlk, sub, tc, inp, G);
        case LKFail(lk2, tlk) =>
          tX := t;
          NP.RAReflOutside(t, inp, G);
        case _ =>
      }
  }

  /** The quantifier shapes: the CIN head (rung A + congruences), the forced
      copy, the empty-bounded skip, and the free loop. */
  lemma CinWalkQuant(rer: LW.RegExpRecord, acts: LS.Actions, cont: LS.Actions,
                     greedy: bool, min: nat, delta: LN.NoI, r1: L.Regex,
                     inp: LC.Input, b: BS.LoopBool, t: LT.Tree, G: set<LG.GroupId>)
    returns (tX: LT.Tree)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1)) && cont == acts[1..]
    requires EL.PikeLkActionsRec(acts) && EL.PikeLkActionsRec(cont)
    requires EL.PikeLkRegexRec(L.Quantified(greedy, min, delta, r1))
    requires NB.EncOk(acts, inp, b)
    requires CinActsIn(acts, G) && CinActsIn(cont, G) && CinOk(L.Quantified(greedy, min, delta, r1), G)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    ensures BoolTreeLkX(rer, acts, inp, b, tX)
    ensures NP.ResAgreeAtOutside(tX, t, inp, G)
    decreases CE.PSize(t), MsizeX(acts), 1
  {
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL;
    assert acts == [acts[0]] + cont;
    var gidl := L.DefGroups(r1);
    assert EL.PikeLkRegexRec(r1);
    assert CinOk(r1, G);
    if min == 1 && CinGreedyL(greedy, delta, r1) {
      tX := CinWalkHead(rer, acts, cont, r1, inp, b, t, G);
    } else if min > 0 {
      match t {
        case GroupActionT(g, tc) =>
          var q1 := L.Quantified(greedy, min - 1, delta, r1);
          var ia := [LS.Areg(r1), LS.Areg(q1)] + cont;
          assert ia == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
          assert EL.PikeLkRegexRec(q1);
          EL.PikeLkActionsRecConsIff(LS.Areg(q1), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(q1)] + cont);
          assert CinOk(q1, G);
          CinActsInCons(LS.Areg(q1), cont, G);
          CinActsInCons(LS.Areg(r1), [LS.Areg(q1)] + cont, G);
          assert NB.EncOk(ia, inp, b) by {
            var parts := [LS.Areg(r1), LS.Areg(q1)];
            assert parts + cont == ia;
            if NUL.NonNullableL(acts[0].r) { reveal NUL.NonNullableL; assert parts[0].Areg? && NUL.NonNullableL(parts[0].r); }
            NB.EncOkExpand(acts, parts, inp, b);
          }
          var sub := CinWalkX(rer, ia, inp, b, tc, G);
          tX := LT.GroupActionT(g, sub);
          NP.RACongGroupOutside(g, sub, tc, inp, G);
        case _ =>
      }
    } else if delta == LN.NN(0) {
      assert MsizeX(cont) < MsizeX(acts);
      assert !NUL.NonNullableL(acts[0].r) by { reveal NUL.NonNullableL; }
      NB.EncOkTailReg(acts, inp, b);
      tX := CinWalkX(rer, cont, inp, b, t, G);
    } else {
      var qn := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
      var il := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(qn)] + cont;
      match t {
        case Choice(ta, tb) =>
          var itert := if greedy then ta else tb;
          var skipt := if greedy then tb else ta;
          match itert {
            case GroupActionT(g, ti) =>
              assert il == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(qn)] + cont));
              assert EL.PikeLkRegexRec(qn);
              EL.PikeLkActionsRecConsIff(LS.Areg(qn), cont);
              EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(qn)] + cont);
              EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(qn)] + cont));
              assert CinOk(qn, G);
              CinActsInCons(LS.Areg(qn), cont, G);
              CinActsInCons(LS.Acheck(inp), [LS.Areg(qn)] + cont, G);
              CinActsInCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(qn)] + cont), G);
              assert !NUL.NonNullableL(acts[0].r) by { reveal NUL.NonNullableL; }
              NB.EncOkTailReg(acts, inp, b);
              NB.EncodableTail(acts, inp, b);
              NB.EncOkIter(r1, qn, cont, inp);
              assert CE.PSize(ti) < CE.PSize(t) && CE.PSize(skipt) < CE.PSize(t);
              var si := CinWalkX(rer, il, inp, BS.CannotExit, ti, G);
              var sk := CinWalkX(rer, cont, inp, b, skipt, G);
              var ix := LT.GroupActionT(g, si);
              NP.RACongGroupOutside(g, si, ti, inp, G);
              if greedy {
                tX := LT.Choice(ix, sk);
                NP.RACongChoiceOutside(ix, ta, sk, tb, inp, G);
              } else {
                tX := LT.Choice(sk, ix);
                NP.RACongChoiceOutside(sk, ta, ix, tb, inp, G);
              }
            case _ =>
          }
        case _ =>
      }
    }
  }

  /** THE CIN HEAD: the spec's forced iteration `Reset(gidl); [r1, r1*] + cont`
      against the engine's head fork `Choice(Reset(gidl); ti, Reset(gidl); tc)`.
      Rung A (`NB.CinPlusPriorityBool` at `S = {}`) relates the spec tree to
      the chained shape; dropping the chain is invisible outside `G`. */
  lemma CinWalkHead(rer: LW.RegExpRecord, acts: LS.Actions, cont: LS.Actions, r1: L.Regex,
                    inp: LC.Input, b: BS.LoopBool, t: LT.Tree, G: set<LG.GroupId>)
    returns (tX: LT.Tree)
    requires |acts| > 0 && cont == acts[1..]
    requires exists greedy: bool, delta: LN.NoI :: acts[0] == LS.Areg(L.Quantified(greedy, 1, delta, r1)) && CinGreedyL(greedy, delta, r1)
    requires EL.PikeLkActionsRec(acts) && EL.PikeLkActionsRec(cont) && EL.PikeLkRegexRec(r1)
    requires NB.EncOk(acts, inp, b)
    requires CinActsIn(acts, G) && CinActsIn(cont, G) && CinOk(r1, G)
    requires LL.LkBodiesInS(r1, {}) && forall g :: g in L.DefGroups(r1) ==> g in G
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    ensures BoolTreeLkX(rer, acts, inp, b, tX)
    ensures NP.ResAgreeAtOutside(tX, t, inp, G)
    decreases CE.PSize(t), MsizeX(acts), 0
  {
    hide NUL.NonNullableL, NUL.NoNulledPlusL;
    var greedy: bool, delta: LN.NoI :| acts[0] == LS.Areg(L.Quantified(greedy, 1, delta, r1)) && CinGreedyL(greedy, delta, r1);
    assert greedy && delta == LN.Inf && NUL.CINullableL(r1) by { reveal CinGreedyL; }
    var gidl := L.DefGroups(r1);
    var q0 := L.Quantified(true, 0, LN.Inf, r1);
    assert acts == [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont;
    var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
    assert ia == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
    match t {
      case GroupActionT(g, tc) =>
        assert g == LG.Reset(gidl);
        assert EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Areg(q0)] + cont, inp, b, tc);
        // fragment facts of the two sub-stacks
        assert EL.PikeLkRegexRec(q0);
        EL.PikeLkActionsRecConsIff(LS.Areg(q0), cont);
        EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(q0)] + cont);
        EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
        assert CinOk(q0, G);
        CinActsInCons(LS.Areg(q0), cont, G);
        CinActsInCons(LS.Acheck(inp), [LS.Areg(q0)] + cont, G);
        CinActsInCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont), G);
        NUL.CINotNonNullableL(r1);
        assert !NUL.NonNullableL(acts[0].r) by { reveal NUL.NonNullableL; }
        NB.EncOkTailReg(acts, inp, b);
        NB.EncodableTail(acts, inp, b);
        NB.EncOkIter(r1, q0, cont, inp);
        // the iteration's and the continuation's spec trees live INSIDE `tc`
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
            match ta {
              case GroupActionT(g2, ti) =>
                assert g2 == LG.Reset(gidl);
                var tcont := tb;
                assert EL.BoolTreeLk(rer, ia, inp, BS.CannotExit, ti);
                assert EL.BoolTreeLk(rer, cont, inp, b, tcont);
                assert CE.PSize(ti) < CE.PSize(t) && CE.PSize(tcont) < CE.PSize(t);
                var si := CinWalkX(rer, ia, inp, BS.CannotExit, ti, G);
                var sc := CinWalkX(rer, cont, inp, b, tcont, G);
                var tloop := LT.GroupActionT(LG.Reset(gidl), si);
                var tskip := LT.GroupActionT(LG.Reset(gidl), sc);
                tX := LT.Choice(tloop, tskip);
                assert BoolTreeLkX(rer, acts, inp, b, tX);
                // (1) ours vs the chain-free spec-built shape: congruences
                var tfree := LT.Choice(LT.GroupActionT(LG.Reset(gidl), ti), LT.GroupActionT(LG.Reset(gidl), tcont));
                NP.RACongGroupOutside(LG.Reset(gidl), si, ti, inp, G);
                NP.RACongGroupOutside(LG.Reset(gidl), sc, tcont, inp, G);
                NP.RACongChoiceOutside(tloop, LT.GroupActionT(LG.Reset(gidl), ti),
                                       tskip, LT.GroupActionT(LG.Reset(gidl), tcont), inp, G);
                // (2) the chain is invisible outside G
                var p := NP.FirstEmptyPathL(rer, r1, inp).value;
                assert NP.PathIn(p, G) by {
                  assert NP.ActsGroupsIn([LS.Areg(r1)], G) by {
                    forall i | 0 <= i < |[LS.Areg(r1)]|
                      ensures ([LS.Areg(r1)][i].Areg? ==> forall g :: g in L.DefGroups([LS.Areg(r1)][i].r) ==> g in G)
                           && ([LS.Areg(r1)][i].Aclose? ==> [LS.Areg(r1)][i].gid in G)
                    {}
                  }
                  NP.PathActionsIn(rer, [LS.Areg(r1)], inp, G);
                }
                var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), ti),
                                      LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont)));
                RAChainDropOutside(p, tcont, inp, G);
                NP.RACongGroupOutside(LG.Reset(gidl), tcont, NP.Chain(p, tcont), inp, G);
                NP.RAReflOutside(LT.GroupActionT(LG.Reset(gidl), ti), inp, G);
                NP.RACongChoiceOutside(LT.GroupActionT(LG.Reset(gidl), ti), LT.GroupActionT(LG.Reset(gidl), ti),
                                       LT.GroupActionT(LG.Reset(gidl), tcont),
                                       LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont)), inp, G);
                // (3) rung A at S = {}: the chained shape vs the spec tree
                NB.CinPlusPriorityBool(rer, r1, cont, inp, b, {}, t, ti, tcont);
                RAMonoOutside(tcin, t, inp, {}, G);
                NP.RATransOutside(tfree, tcin, t, inp, G);
                NP.RATransOutside(tX, tfree, t, inp, G);
              case _ =>
            }
          case _ =>
        }
      case _ =>
    }
  }
}
