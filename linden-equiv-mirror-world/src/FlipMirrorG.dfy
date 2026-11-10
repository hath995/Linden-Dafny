// G1(b): the DIRECTION-GENERIC flip tree mirror (package linden-equiv-mirror-world;
// first proved by the W3 endgame subagent, see linden-equiv/endgame/W3-G1b.md).
//
// `FM.ComputeTreeReverseF` relates a BACKWARD walk of a `GroupOkLBActs` stack
// to the FORWARD walk of `FlipRevActs(acts)` over the swapped input, with the
// original side pinned to lookbehind-flavoured looks. Here: a walk of `acts`
// in an ARBITRARY direction `dir` relates to the walk of `FlipRevActs(acts)` in
// `OppDir(dir)` over `SwapInput(inp)`, for ANY backreference-free stack (mixed
// look kinds allowed). The look case is the same induction at `LkDir(lk)`:
// `LkDir(FlipLk(lk)) == OppDir(LkDir(lk))`.
//
// First verified against flip-mirror's deps + flip-mirror's own .doo (see W3-G1b.md).
module LindenElkFlipMirrorG {
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
  import FM = LindenElkFlipMirror

  // ===========================================================================
  // Direction flip and the direction-generic swap primitives
  // ===========================================================================

  function OppDir(dir: WP.Direction): WP.Direction {
    match dir
    case Forward => WP.Backward
    case Backward => WP.Forward
  }

  lemma OppDirInvolution(dir: WP.Direction)
    ensures OppDir(OppDir(dir)) == dir
  {}

  /** The flip re-orients a look and keeps its polarity. */
  lemma FlipLkDirPos(lk: L.Lookaround)
    ensures L.LkDir(FR.FlipLk(lk)) == OppDir(L.LkDir(lk))
    ensures L.Positivity(FR.FlipLk(lk)) == L.Positivity(lk)
  {}

  lemma ReadCharSwapG(rer: LW.RegExpRecord, cd: LC.CharDescr, inp: LC.Input, dir: WP.Direction)
    ensures match LC.ReadChar(rer, cd, inp, dir)
            case None => LC.ReadChar(rer, cd, SD.SwapInput(inp), OppDir(dir)).None?
            case Some(pair) =>
              LC.ReadChar(rer, cd, SD.SwapInput(inp), OppDir(dir))
                == Some((pair.0, SD.SwapInput(pair.1)))
  {
    match dir {
      case Backward => SD.ReadCharSwap(rer, cd, inp);
      case Forward =>
    }
  }

  lemma IsStrictSuffixSwapG(inp1: LC.Input, inp2: LC.Input, dir: WP.Direction)
    ensures SSx.IsStrictSuffix(inp1, inp2, dir)
        <==> SSx.IsStrictSuffix(SD.SwapInput(inp1), SD.SwapInput(inp2), OppDir(dir))
  {
    match dir {
      case Backward => SD.IsStrictSuffixSwap(inp1, inp2);
      case Forward =>
        SD.IsStrictSuffixSwap(SD.SwapInput(inp1), SD.SwapInput(inp2));
        SD.SwapInputInvolution(inp1);
        SD.SwapInputInvolution(inp2);
    }
  }

  lemma AdvanceInputSwapG(inp: LC.Input, dir: WP.Direction)
    ensures match LC.AdvanceInput(inp, dir)
            case None => LC.AdvanceInput(SD.SwapInput(inp), OppDir(dir)).None?
            case Some(ni) =>
              LC.AdvanceInput(SD.SwapInput(inp), OppDir(dir)) == Some(SD.SwapInput(ni))
  {}

  lemma AdvanceInputPSwapG(inp: LC.Input, dir: WP.Direction)
    ensures LC.AdvanceInputP(SD.SwapInput(inp), OppDir(dir))
         == SD.SwapInput(LC.AdvanceInputP(inp, dir))
  {
    AdvanceInputSwapG(inp, dir);
  }

  lemma MaxIterSwapG(inp: LC.Input, dir: WP.Direction)
    ensures FS.MaxIter(SD.SwapInput(inp), OppDir(dir)) == FS.MaxIter(inp, dir)
  {}

  lemma WorstInputSwapG(inp: LC.Input, dir: WP.Direction)
    ensures FS.WorstInput(SD.SwapInput(inp), OppDir(dir)) == SD.SwapInput(FS.WorstInput(inp, dir))
  {}

  // ===========================================================================
  // The relation: kinds related by FlipLk, ANY kind
  // ===========================================================================

  /** `TreeMirrorRelF` with the lookbehind pin dropped. Orientation-free: the
      relation never mentions a direction; `TreeRes` supplies `dir` on one
      side and `OppDir(dir)` on the other. */
  ghost predicate TreeMirrorRelG(t: LT.Tree, tm: LT.Tree) {
    match (t, tm)
    case (Mismatch, Mismatch) => true
    case (Match, Match) => true
    case (Choice(a, b), Choice(am, bm)) => TreeMirrorRelG(a, am) && TreeMirrorRelG(b, bm)
    case (Read(c, a), Read(cm, am)) => c == cm && TreeMirrorRelG(a, am)
    case (Progress(a), Progress(am)) => TreeMirrorRelG(a, am)
    case (AnchorPass(x, a), AnchorPass(xm, am)) =>
      xm == SD.SwapAnchorL(x) && TreeMirrorRelG(a, am)
    case (GroupActionT(ga, a), GroupActionT(gam, am)) =>
      TM.GroupActionMirror(ga, gam) && TreeMirrorRelG(a, am)
    case (LK(lk, tlk, tc), LK(lkm, tlkm, tcm)) =>
      lkm == FR.FlipLk(lk) && TreeMirrorRelG(tlk, tlkm) && TreeMirrorRelG(tc, tcm)
    case (LKFail(lk, tlk), LKFail(lkm, tlkm)) =>
      lkm == FR.FlipLk(lk) && TreeMirrorRelG(tlk, tlkm)
    case _ => false
  }

  /** The relation is symmetric (every component map is an involution). */
  lemma TreeMirrorRelGSym(t: LT.Tree, tm: LT.Tree)
    requires TreeMirrorRelG(t, tm)
    ensures TreeMirrorRelG(tm, t)
    decreases t
  {
    match (t, tm)
    case (Choice(a, b), Choice(am, bm)) => TreeMirrorRelGSym(a, am); TreeMirrorRelGSym(b, bm);
    case (Read(c, a), Read(cm, am)) => TreeMirrorRelGSym(a, am);
    case (Progress(a), Progress(am)) => TreeMirrorRelGSym(a, am);
    case (AnchorPass(x, a), AnchorPass(xm, am)) => TreeMirrorRelGSym(a, am);
    case (GroupActionT(ga, a), GroupActionT(gam, am)) => TreeMirrorRelGSym(a, am);
    case (LK(lk, tlk, tc), LK(lkm, tlkm, tcm)) =>
      FR.FlipLkLaws(lk);
      TreeMirrorRelGSym(tlk, tlkm); TreeMirrorRelGSym(tc, tcm);
    case (LKFail(lk, tlk), LKFail(lkm, tlkm)) =>
      FR.FlipLkLaws(lk);
      TreeMirrorRelGSym(tlk, tlkm);
    case _ =>
  }

  // ===========================================================================
  // The SOMENESS fold, any direction
  // ===========================================================================

  lemma TreeResSomeMirrorG(t: LT.Tree, tm: LT.Tree, gm1: LG.GroupMap, gm2: LG.GroupMap,
                           inp: LC.Input, dir: WP.Direction)
    requires TreeMirrorRelG(t, tm)
    ensures LT.TreeRes(t, gm1, inp, dir).Some?
        <==> LT.TreeRes(tm, gm2, SD.SwapInput(inp), OppDir(dir)).Some?
    decreases t
  {
    var sinp := SD.SwapInput(inp);
    match t
    case Mismatch =>
    case Match =>
    case Choice(a, b) =>
      match tm {
        case Choice(am, bm) =>
          TreeResSomeMirrorG(a, am, gm1, gm2, inp, dir);
          TreeResSomeMirrorG(b, bm, gm1, gm2, inp, dir);
        case _ =>
      }
    case Read(c, a) =>
      match tm {
        case Read(cm, am) =>
          var inp' := LC.AdvanceInputP(inp, dir);
          AdvanceInputPSwapG(inp, dir);
          TreeResSomeMirrorG(a, am, gm1, gm2, inp', dir);
        case _ =>
      }
    case Progress(a) =>
      match tm { case Progress(am) => TreeResSomeMirrorG(a, am, gm1, gm2, inp, dir); case _ => }
    case AnchorPass(x, a) =>
      match tm { case AnchorPass(xm, am) => TreeResSomeMirrorG(a, am, gm1, gm2, inp, dir); case _ => }
    case GroupActionT(ga, a) =>
      match tm {
        case GroupActionT(gam, am) =>
          TreeResSomeMirrorG(a, am, LG.GMUpdate(ga, LC.Idx(inp), gm1),
                             LG.GMUpdate(gam, LC.Idx(sinp), gm2), inp, dir);
        case _ =>
      }
    case LK(lk, tlk, tc) =>
      match tm {
        case LK(lkm, tlkm, tcm) =>
          FlipLkDirPos(lk);
          var ld := L.LkDir(lk);
          assert L.LkDir(lkm) == OppDir(ld);
          TreeResSomeMirrorG(tlk, tlkm, gm1, gm2, inp, ld);
          var sb := LT.TreeRes(tlk, gm1, inp, ld);
          var sf := LT.TreeRes(tlkm, gm2, sinp, OppDir(ld));
          if L.Positivity(lk) {
            match sb {
              case Some(pair) =>
                TreeResSomeMirrorG(tc, tcm, pair.1, sf.value.1, inp, dir);
              case None =>
            }
          } else {
            match sb {
              case None => TreeResSomeMirrorG(tc, tcm, gm1, gm2, inp, dir);
              case Some(_) =>
            }
          }
        case _ =>
      }
    case LKFail(_, _) =>
    case ReadBackRef(_, _) =>
  }

  // ===========================================================================
  // Fuel transport, any direction, NO fragment premise
  // ===========================================================================

  lemma RegexFuelFlipRevG(r: L.Regex, inp: LC.Input, dir: WP.Direction)
    ensures FS.RegexFuel(FM.FlipRevL(r), SD.SwapInput(inp), OppDir(dir))
         == FS.RegexFuel(r, inp, dir)
    decreases r
  {
    match r
    case Disjunction(r1, r2) =>
      RegexFuelFlipRevG(r1, inp, dir); RegexFuelFlipRevG(r2, inp, dir);
    case Sequence(r1, r2) =>
      RegexFuelFlipRevG(r1, inp, dir); RegexFuelFlipRevG(r2, inp, dir);
      assert FM.FlipRevL(r) == L.Sequence(FM.FlipRevL(r2), FM.FlipRevL(r1));
    case Quantified(b, min, delta, r1) =>
      RegexFuelFlipRevG(r1, inp, dir);
      MaxIterSwapG(inp, dir);
      assert FM.FlipRevL(r) == L.Quantified(b, min, delta, FM.FlipRevL(r1));
    case Group(_, r1) => RegexFuelFlipRevG(r1, inp, dir);
    case LookaroundR(lk, r1) =>
      assert FM.FlipRevL(r) == L.LookaroundR(FR.FlipLk(lk), FM.FlipRevL(r1));
      FlipLkDirPos(lk);
      var ld := L.LkDir(lk);
      var w := FS.WorstInput(inp, ld);
      WorstInputSwapG(inp, ld);
      RegexFuelFlipRevG(r1, w, ld);
    case _ =>
  }

  lemma ActionsFuelFlipRevG(acts: LS.Actions, inp: LC.Input, dir: WP.Direction)
    ensures FS.ActionsFuel(FM.FlipRevActs(acts), SD.SwapInput(inp), OppDir(dir))
         == FS.ActionsFuel(acts, inp, dir)
    decreases |acts|
  {
    if |acts| == 0 {
      assert FM.FlipRevActs(acts) == [];
      return;
    }
    FM.FlipRevActsTail(acts);
    assert FM.FlipRevActs(acts)[0] ==
      (match acts[0] case Areg(r) => LS.Areg(FM.FlipRevL(r))
                     case Acheck(ip) => LS.Acheck(SD.SwapInput(ip))
                     case Aclose(g) => LS.Aclose(g));
    match acts[0]
    case Areg(r) =>
      RegexFuelFlipRevG(r, inp, dir);
      ActionsFuelFlipRevG(acts[1..], inp, dir);
    case Aclose(g) =>
      ActionsFuelFlipRevG(acts[1..], inp, dir);
    case Acheck(ip) =>
      AdvanceInputSwapG(ip, dir);
      match LC.AdvanceInput(ip, dir) {
        case None =>
        case Some(ni) => ActionsFuelFlipRevG(acts[1..], ni, dir);
      }
  }

  // ===========================================================================
  // THE BUILDER, any direction, NoBackrefActs only
  // ===========================================================================

  lemma ComputeTreeReverseG(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                            gm1: LG.GroupMap, gm2: LG.GroupMap, dir: WP.Direction, fuel: nat)
    requires SD.NoBackrefActs(acts)
    ensures var b := FS.ComputeTree(rer, acts, inp, gm1, dir, fuel);
            var fw := FS.ComputeTree(rer, FM.FlipRevActs(acts), SD.SwapInput(inp), gm2,
                                     OppDir(dir), fuel);
            (b.None? <==> fw.None?)
            && (b.Some? && fw.Some? ==> TreeMirrorRelG(b.value, fw.value))
    decreases fuel
  {
    var racts := FM.FlipRevActs(acts);
    var sinp := SD.SwapInput(inp);
    var odir := OppDir(dir);
    if fuel == 0 { return; }
    var f := fuel - 1;
    if |acts| == 0 {
      assert racts == [];
      return;
    }
    var cont := acts[1..];
    SD.NoBackrefActsTail(acts);
    FM.FlipRevActsTail(acts);
    assert racts[1..] == FM.FlipRevActs(cont);
    match acts[0]
    case Acheck(strcheck) =>
      assert racts[0] == LS.Acheck(SD.SwapInput(strcheck));
      IsStrictSuffixSwapG(inp, strcheck, dir);
      if SSx.IsStrictSuffix(inp, strcheck, dir) {
        ComputeTreeReverseG(rer, cont, inp, gm1, gm2, dir, f);
      }
    case Aclose(gid) =>
      assert racts[0] == LS.Aclose(gid);
      ComputeTreeReverseG(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm1),
                          LG.GMClose(LC.Idx(sinp), gid, gm2), dir, f);
    case Areg(r) =>
      assert racts[0] == LS.Areg(FM.FlipRevL(r));
      assert SD.NoBackrefL(r);
      match r
      case Epsilon =>
        ComputeTreeReverseG(rer, cont, inp, gm1, gm2, dir, f);
      case Character(cd) =>
        ReadCharSwapG(rer, cd, inp, dir);
        match LC.ReadChar(rer, cd, inp, dir) {
          case Some(pair) =>
            ComputeTreeReverseG(rer, cont, pair.1, gm1, gm2, dir, f);
          case None =>
        }
      case Disjunction(r1, r2) =>
        assert FM.FlipRevL(r) == L.Disjunction(FM.FlipRevL(r1), FM.FlipRevL(r2));
        SD.NoBackrefActsCons(LS.Areg(r1), cont);
        SD.NoBackrefActsCons(LS.Areg(r2), cont);
        FM.FlipRevActsCons(LS.Areg(r1), cont);
        FM.FlipRevActsCons(LS.Areg(r2), cont);
        ComputeTreeReverseG(rer, [LS.Areg(r1)] + cont, inp, gm1, gm2, dir, f);
        ComputeTreeReverseG(rer, [LS.Areg(r2)] + cont, inp, gm1, gm2, dir, f);
      case Sequence(r1, r2) =>
        assert FM.FlipRevL(r) == L.Sequence(FM.FlipRevL(r2), FM.FlipRevL(r1));
        var sl := LS.SeqList(r1, r2, dir);
        var slm := LS.SeqList(FM.FlipRevL(r2), FM.FlipRevL(r1), odir);
        // the concatenation-order step, both orientations
        assert FM.FlipRevActs(sl) == slm by {
          match dir {
            case Forward =>
              assert sl == [LS.Areg(r1), LS.Areg(r2)];
              assert slm == [LS.Areg(FM.FlipRevL(r1)), LS.Areg(FM.FlipRevL(r2))];
              assert FM.FlipRevActs([LS.Areg(r1), LS.Areg(r2)])
                  == [LS.Areg(FM.FlipRevL(r1)), LS.Areg(FM.FlipRevL(r2))];
            case Backward =>
              assert sl == [LS.Areg(r2), LS.Areg(r1)];
              assert slm == [LS.Areg(FM.FlipRevL(r2)), LS.Areg(FM.FlipRevL(r1))];
              assert FM.FlipRevActs([LS.Areg(r2), LS.Areg(r1)])
                  == [LS.Areg(FM.FlipRevL(r2)), LS.Areg(FM.FlipRevL(r1))];
          }
        }
        FM.FlipRevActsAppend(sl, cont);
        assert SD.NoBackrefActs(sl + cont) by {
          assert |sl| == 2 && sl[0].Areg? && sl[1].Areg?;
          assert SD.NoBackrefL(sl[0].r) && SD.NoBackrefL(sl[1].r);
          SD.NoBackrefActsCons(sl[1], cont);
          SD.NoBackrefActsCons(sl[0], [sl[1]] + cont);
          assert sl + cont == [sl[0]] + ([sl[1]] + cont);
        }
        ComputeTreeReverseG(rer, sl + cont, inp, gm1, gm2, dir, f);
      case Quantified(greedy, min, delta, r1) =>
        assert FM.FlipRevL(r) == L.Quantified(greedy, min, delta, FM.FlipRevL(r1));
        var gidl := L.DefGroups(r1);
        var gidlm := L.DefGroups(FM.FlipRevL(r1));
        FM.FlipRevLDefGroupsSet(r1);
        if min > 0 {
          var q1 := L.Quantified(greedy, min - 1, delta, r1);
          assert FM.FlipRevL(q1) == L.Quantified(greedy, min - 1, delta, FM.FlipRevL(r1));
          SD.NoBackrefActsCons(LS.Areg(q1), cont);
          SD.NoBackrefActsCons(LS.Areg(r1), [LS.Areg(q1)] + cont);
          FM.FlipRevActsAppend([LS.Areg(r1), LS.Areg(q1)], cont);
          assert FM.FlipRevActs([LS.Areg(r1), LS.Areg(q1)])
              == [LS.Areg(FM.FlipRevL(r1)), LS.Areg(FM.FlipRevL(q1))];
          assert [LS.Areg(r1), LS.Areg(q1)] + cont == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
          ComputeTreeReverseG(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp,
                              LG.GMReset(gidl, gm1), LG.GMReset(gidlm, gm2), dir, f);
          var bi := FS.ComputeTree(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp,
                                   LG.GMReset(gidl, gm1), dir, f);
          var fi := FS.ComputeTree(rer, FM.FlipRevActs([LS.Areg(r1), LS.Areg(q1)] + cont), sinp,
                                   LG.GMReset(gidlm, gm2), odir, f);
          if bi.Some? && fi.Some? {
            assert TM.GroupActionMirror(LG.Reset(gidl), LG.Reset(gidlm));
            assert TreeMirrorRelG(LT.GroupActionT(LG.Reset(gidl), bi.value),
                                  LT.GroupActionT(LG.Reset(gidlm), fi.value));
          }
        } else if delta == LN.NN(0) {
          ComputeTreeReverseG(rer, cont, inp, gm1, gm2, dir, f);
        } else {
          var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          assert FM.FlipRevL(q0) == L.Quantified(greedy, 0, FS.NoiPred(delta), FM.FlipRevL(r1));
          SD.NoBackrefActsCons(LS.Areg(q0), cont);
          SD.NoBackrefActsCons(LS.Acheck(inp), [LS.Areg(q0)] + cont);
          SD.NoBackrefActsCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
          FM.FlipRevActsAppend([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)], cont);
          assert FM.FlipRevActs([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)])
              == [LS.Areg(FM.FlipRevL(r1)), LS.Acheck(sinp), LS.Areg(FM.FlipRevL(q0))];
          assert [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont
              == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
          ComputeTreeReverseG(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, inp,
                              LG.GMReset(gidl, gm1), LG.GMReset(gidlm, gm2), dir, f);
          ComputeTreeReverseG(rer, cont, inp, gm1, gm2, dir, f);
          var bi := FS.ComputeTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont,
                                   inp, LG.GMReset(gidl, gm1), dir, f);
          var fi := FS.ComputeTree(rer, FM.FlipRevActs([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont),
                                   sinp, LG.GMReset(gidlm, gm2), odir, f);
          var bs := FS.ComputeTree(rer, cont, inp, gm1, dir, f);
          var fs := FS.ComputeTree(rer, FM.FlipRevActs(cont), sinp, gm2, odir, f);
          if bi.Some? && bs.Some? && fi.Some? && fs.Some? {
            assert TM.GroupActionMirror(LG.Reset(gidl), LG.Reset(gidlm));
            assert TreeMirrorRelG(LT.GroupActionT(LG.Reset(gidl), bi.value),
                                  LT.GroupActionT(LG.Reset(gidlm), fi.value));
            assert TreeMirrorRelG(bs.value, fs.value);
          }
        }
      case Group(gid, r1) =>
        assert FM.FlipRevL(r) == L.Group(gid, FM.FlipRevL(r1));
        SD.NoBackrefActsCons(LS.Aclose(gid), cont);
        SD.NoBackrefActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        FM.FlipRevActsAppend([LS.Areg(r1), LS.Aclose(gid)], cont);
        assert FM.FlipRevActs([LS.Areg(r1), LS.Aclose(gid)])
            == [LS.Areg(FM.FlipRevL(r1)), LS.Aclose(gid)];
        assert [LS.Areg(r1), LS.Aclose(gid)] + cont
            == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
        ComputeTreeReverseG(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp,
                            LG.GMOpen(LC.Idx(inp), gid, gm1),
                            LG.GMOpen(LC.Idx(sinp), gid, gm2), dir, f);
      case LookaroundR(lk, r1) =>
        // ANY kind: the inner walk runs in LkDir(lk); its flip in OppDir of it.
        assert FM.FlipRevL(r) == L.LookaroundR(FR.FlipLk(lk), FM.FlipRevL(r1));
        FlipLkDirPos(lk);
        var ld := L.LkDir(lk);
        assert L.LkDir(FR.FlipLk(lk)) == OppDir(ld);
        assert SD.NoBackrefActs([LS.Areg(r1)]);
        assert FM.FlipRevActs([LS.Areg(r1)]) == [LS.Areg(FM.FlipRevL(r1))];
        ComputeTreeReverseG(rer, [LS.Areg(r1)], inp, gm1, gm2, ld, f);
        var bl := FS.ComputeTree(rer, [LS.Areg(r1)], inp, gm1, ld, f);
        var fl := FS.ComputeTree(rer, [LS.Areg(FM.FlipRevL(r1))], sinp, gm2, OppDir(ld), f);
        if bl.Some? {
          assert fl.Some? && TreeMirrorRelG(bl.value, fl.value);
          TreeResSomeMirrorG(bl.value, fl.value, gm1, gm2, inp, ld);
          var vb := LS.LkResult(lk, bl.value, gm1, inp);
          var vf := LS.LkResult(FR.FlipLk(lk), fl.value, gm2, sinp);
          assert vb.Some? <==> vf.Some?;
          match vb {
            case Some(gmlk) =>
              var gmlk2 := vf.value;
              ComputeTreeReverseG(rer, cont, inp, gmlk, gmlk2, dir, f);
              var bc := FS.ComputeTree(rer, cont, inp, gmlk, dir, f);
              var fc := FS.ComputeTree(rer, FM.FlipRevActs(cont), sinp, gmlk2, odir, f);
              if bc.Some? && fc.Some? {
                assert TreeMirrorRelG(LT.LK(lk, bl.value, bc.value),
                                      LT.LK(FR.FlipLk(lk), fl.value, fc.value));
              }
            case None =>
              assert TreeMirrorRelG(LT.LKFail(lk, bl.value),
                                    LT.LKFail(FR.FlipLk(lk), fl.value));
          }
        }
      case AnchorR(a) =>
        assert FM.FlipRevL(r) == L.AnchorR(SD.SwapAnchorL(a));
        SD.AnchorSatisfiedSwap(rer, a, inp);
        if LS.AnchorSatisfied(rer, a, inp) {
          ComputeTreeReverseG(rer, cont, inp, gm1, gm2, dir, f);
        }
      case Backreference(gid) =>
        assert SD.NoBackrefL(r);
        assert false;
  }

  /** Fuel-free corollary, any direction. */
  lemma ComputeTrReverseG(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                          gm1: LG.GroupMap, gm2: LG.GroupMap, dir: WP.Direction)
    requires SD.NoBackrefActs(acts)
    ensures TreeMirrorRelG(FU.ComputeTr(rer, acts, inp, gm1, dir),
                           FU.ComputeTr(rer, FM.FlipRevActs(acts), SD.SwapInput(inp), gm2,
                                        OppDir(dir)))
  {
    var fb := FS.ActionsFuel(acts, inp, dir) + 1;
    var ff := FS.ActionsFuel(FM.FlipRevActs(acts), SD.SwapInput(inp), OppDir(dir)) + 1;
    ActionsFuelFlipRevG(acts, inp, dir);
    assert fb == ff;
    FS.FunctionalTerminates(rer, acts, inp, gm1, dir, fb);
    FS.FunctionalTerminates(rer, FM.FlipRevActs(acts), SD.SwapInput(inp), gm2, OppDir(dir), ff);
    ComputeTreeReverseG(rer, acts, inp, gm1, gm2, dir, fb);
  }

  // ===========================================================================
  // THE VALUE FOLD, any direction
  // ===========================================================================

  lemma TreeResMirrorG(t: LT.Tree, tm: LT.Tree, gm1: LG.GroupMap, inp: LC.Input,
                       dir: WP.Direction, n: nat, O: set<LG.GroupId>)
    requires TreeMirrorRelG(t, tm)
    requires n == |inp.pref| + |inp.next|
    requires TRM.GmInBounds(gm1, n)
    requires FM.CloseDiscF(t, O)
    requires TRM.OpenSubset(gm1, O)
    ensures var rb := LT.TreeRes(t, gm1, inp, dir);
            var rf := LT.TreeRes(tm, TRM.MirrorGm(gm1, n), SD.SwapInput(inp), OppDir(dir));
            && (rb.None? <==> rf.None?)
            && (rb.Some? ==>
                  && rf.Some?
                  && rf.value.0 == SD.SwapInput(rb.value.0)
                  && TRM.GmInBounds(rb.value.1, n)
                  && rf.value.1 == TRM.MirrorGm(rb.value.1, n))
    decreases t
  {
    var gm2 := TRM.MirrorGm(gm1, n);
    var sinp := SD.SwapInput(inp);
    assert LC.Idx(sinp) == n - LC.Idx(inp);
    match t
    case Mismatch =>
    case Match =>
    case Choice(a, b) =>
      match tm {
        case Choice(am, bm) =>
          TreeResMirrorG(a, am, gm1, inp, dir, n, O);
          TreeResMirrorG(b, bm, gm1, inp, dir, n, O);
        case _ =>
      }
    case Read(c, a) =>
      match tm {
        case Read(cm, am) =>
          var inp' := LC.AdvanceInputP(inp, dir);
          AdvanceInputPSwapG(inp, dir);
          TRM.AdvanceInputPLen(inp, dir);
          TreeResMirrorG(a, am, gm1, inp', dir, n, O);
        case _ =>
      }
    case Progress(a) =>
      match tm {
        case Progress(am) => TreeResMirrorG(a, am, gm1, inp, dir, n, O);
        case _ =>
      }
    case AnchorPass(x, a) =>
      match tm {
        case AnchorPass(xm, am) => TreeResMirrorG(a, am, gm1, inp, dir, n, O);
        case _ =>
      }
    case GroupActionT(ga, a) =>
      match tm {
        case GroupActionT(gam, am) =>
          match ga {
            case Open(g) =>
              assert gam == LG.Open(g);
              TRM.GMOpenMirror(gm1, g, LC.Idx(inp), n);
              var gm1' := LG.GMOpen(LC.Idx(inp), g, gm1);
              assert LG.GMUpdate(gam, LC.Idx(sinp), gm2)
                  == LG.GMOpen(n - LC.Idx(inp), g, gm2);
              assert TRM.OpenSubset(gm1', O + {g}) by {
                forall h | h in O + {g} ensures h in gm1' && gm1'[h].endIdx.None? {}
              }
              TreeResMirrorG(a, am, gm1', inp, dir, n, O + {g});
            case Close(g) =>
              assert gam == LG.Close(g);
              assert g in O;
              assert g in gm1 && gm1[g].endIdx.None?;
              TRM.GMCloseMirror(gm1, g, LC.Idx(inp), n);
              var gm1' := LG.GMClose(LC.Idx(inp), g, gm1);
              assert LG.GMUpdate(gam, LC.Idx(sinp), gm2)
                  == LG.GMClose(n - LC.Idx(inp), g, gm2);
              assert TRM.OpenSubset(gm1', O - {g}) by {
                forall h | h in O - {g} ensures h in gm1' && gm1'[h].endIdx.None? {}
              }
              TreeResMirrorG(a, am, gm1', inp, dir, n, O - {g});
            case Reset(gl) =>
              assert gam.Reset?;
              TRM.GMResetMirror(gm1, gl, gam.gl, n);
              var gm1' := LG.GMReset(gl, gm1);
              assert LG.GMUpdate(gam, LC.Idx(sinp), gm2) == LG.GMReset(gam.gl, gm2);
              assert TRM.OpenSubset(gm1', O - (set x | x in gl)) by {
                forall h | h in O - (set x | x in gl)
                  ensures h in gm1' && gm1'[h].endIdx.None? {}
              }
              TreeResMirrorG(a, am, gm1', inp, dir, n, O - (set x | x in gl));
          }
        case _ =>
      }
    case LK(lk, tlk, tc) =>
      match tm {
        case LK(lkm, tlkm, tcm) =>
          FlipLkDirPos(lk);
          var ld := L.LkDir(lk);
          assert L.LkDir(lkm) == OppDir(ld);
          TreeResMirrorG(tlk, tlkm, gm1, inp, ld, n, O);
          var sb := LT.TreeRes(tlk, gm1, inp, ld);
          var sf := LT.TreeRes(tlkm, gm2, sinp, OppDir(ld));
          if L.Positivity(lk) {
            match sb {
              case Some(pair) =>
                FM.TreeResPreservesOpen(tlk, gm1, inp, ld, O);
                TreeResMirrorG(tc, tcm, pair.1, inp, dir, n, O);
              case None =>
            }
          } else {
            match sb {
              case None => TreeResMirrorG(tc, tcm, gm1, inp, dir, n, O);
              case Some(_) =>
            }
          }
        case _ =>
      }
    case LKFail(_, _) =>
    case ReadBackRef(_, _) =>
  }

  // ===========================================================================
  // The one-way originals are instances
  // ===========================================================================

  lemma GroupOkLBActsNoBackref(acts: LS.Actions)
    requires FM.GroupOkLBActs(acts)
    ensures SD.NoBackrefActs(acts)
  {
    forall i | 0 <= i < |acts| && acts[i].Areg?
      ensures SD.NoBackrefL(acts[i].r)
    { SD.GroupOkLBIsNoBackref(acts[i].r); }
  }

  /** F ⊆ G: every one-way-related pair is generically related. */
  lemma TreeMirrorRelFIsG(t: LT.Tree, tm: LT.Tree)
    requires FM.TreeMirrorRelF(t, tm)
    ensures TreeMirrorRelG(t, tm)
    decreases t
  {
    match (t, tm)
    case (Choice(a, b), Choice(am, bm)) => TreeMirrorRelFIsG(a, am); TreeMirrorRelFIsG(b, bm);
    case (Read(c, a), Read(cm, am)) => TreeMirrorRelFIsG(a, am);
    case (Progress(a), Progress(am)) => TreeMirrorRelFIsG(a, am);
    case (AnchorPass(x, a), AnchorPass(xm, am)) => TreeMirrorRelFIsG(a, am);
    case (GroupActionT(ga, a), GroupActionT(gam, am)) => TreeMirrorRelFIsG(a, am);
    case (LK(lk, tlk, tc), LK(lkm, tlkm, tcm)) => TreeMirrorRelFIsG(tlk, tlkm); TreeMirrorRelFIsG(tc, tcm);
    case (LKFail(lk, tlk), LKFail(lkm, tlkm)) => TreeMirrorRelFIsG(tlk, tlkm);
    case _ =>
  }

  /** Every look node (inner sub-trees included) is lookbehind-flavoured. */
  ghost predicate TreeLooksLB(t: LT.Tree)
    decreases t
  {
    match t
    case Mismatch => true
    case Match => true
    case Choice(a, b) => TreeLooksLB(a) && TreeLooksLB(b)
    case Read(_, a) => TreeLooksLB(a)
    case ReadBackRef(_, a) => TreeLooksLB(a)
    case Progress(a) => TreeLooksLB(a)
    case AnchorPass(_, a) => TreeLooksLB(a)
    case GroupActionT(_, a) => TreeLooksLB(a)
    case LK(lk, tlk, tc) => (lk.LookBehind? || lk.NegLookBehind?) && TreeLooksLB(tlk) && TreeLooksLB(tc)
    case LKFail(lk, tlk) => (lk.LookBehind? || lk.NegLookBehind?) && TreeLooksLB(tlk)
  }

  /** G + an LB-only original side = F. */
  lemma TreeMirrorRelGLBIsF(t: LT.Tree, tm: LT.Tree)
    requires TreeMirrorRelG(t, tm) && TreeLooksLB(t)
    ensures FM.TreeMirrorRelF(t, tm)
    decreases t
  {
    match (t, tm)
    case (Choice(a, b), Choice(am, bm)) => TreeMirrorRelGLBIsF(a, am); TreeMirrorRelGLBIsF(b, bm);
    case (Read(c, a), Read(cm, am)) => TreeMirrorRelGLBIsF(a, am);
    case (Progress(a), Progress(am)) => TreeMirrorRelGLBIsF(a, am);
    case (AnchorPass(x, a), AnchorPass(xm, am)) => TreeMirrorRelGLBIsF(a, am);
    case (GroupActionT(ga, a), GroupActionT(gam, am)) => TreeMirrorRelGLBIsF(a, am);
    case (LK(lk, tlk, tc), LK(lkm, tlkm, tcm)) => TreeMirrorRelGLBIsF(tlk, tlkm); TreeMirrorRelGLBIsF(tc, tcm);
    case (LKFail(lk, tlk), LKFail(lkm, tlkm)) => TreeMirrorRelGLBIsF(tlk, tlkm);
    case _ =>
  }

  /** A `GroupOkLBActs` stack computes LB-only trees (any direction). */
  lemma ComputeTreeLooksLB(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                           gm: LG.GroupMap, dir: WP.Direction, fuel: nat)
    requires FM.GroupOkLBActs(acts)
    ensures var o := FS.ComputeTree(rer, acts, inp, gm, dir, fuel);
            o.Some? ==> TreeLooksLB(o.value)
    decreases fuel
  {
    if fuel == 0 { return; }
    var f := fuel - 1;
    if |acts| == 0 { return; }
    var cont := acts[1..];
    FM.GroupOkLBActsTail(acts);
    match acts[0]
    case Acheck(strcheck) =>
      if SSx.IsStrictSuffix(inp, strcheck, dir) { ComputeTreeLooksLB(rer, cont, inp, gm, dir, f); }
    case Aclose(gid) =>
      ComputeTreeLooksLB(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm), dir, f);
    case Areg(r) =>
      assert SD.GroupOkLB(r);
      match r
      case Epsilon => ComputeTreeLooksLB(rer, cont, inp, gm, dir, f);
      case Character(cd) =>
        match LC.ReadChar(rer, cd, inp, dir) {
          case Some(pair) => ComputeTreeLooksLB(rer, cont, pair.1, gm, dir, f);
          case None =>
        }
      case Disjunction(r1, r2) =>
        FM.GroupOkLBActsCons(LS.Areg(r1), cont);
        FM.GroupOkLBActsCons(LS.Areg(r2), cont);
        ComputeTreeLooksLB(rer, [LS.Areg(r1)] + cont, inp, gm, dir, f);
        ComputeTreeLooksLB(rer, [LS.Areg(r2)] + cont, inp, gm, dir, f);
      case Sequence(r1, r2) =>
        var sl := LS.SeqList(r1, r2, dir);
        assert FM.GroupOkLBActs(sl + cont) by {
          assert |sl| == 2 && sl[0].Areg? && sl[1].Areg?;
          assert SD.GroupOkLB(sl[0].r) && SD.GroupOkLB(sl[1].r);
          FM.GroupOkLBActsCons(sl[1], cont);
          FM.GroupOkLBActsCons(sl[0], [sl[1]] + cont);
          assert sl + cont == [sl[0]] + ([sl[1]] + cont);
        }
        ComputeTreeLooksLB(rer, sl + cont, inp, gm, dir, f);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        if min > 0 {
          var q1 := L.Quantified(greedy, min - 1, delta, r1);
          FM.GroupOkLBActsCons(LS.Areg(q1), cont);
          FM.GroupOkLBActsCons(LS.Areg(r1), [LS.Areg(q1)] + cont);
          assert [LS.Areg(r1), LS.Areg(q1)] + cont == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
          ComputeTreeLooksLB(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp, LG.GMReset(gidl, gm), dir, f);
        } else if delta == LN.NN(0) {
          ComputeTreeLooksLB(rer, cont, inp, gm, dir, f);
        } else {
          var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          FM.GroupOkLBActsCons(LS.Areg(q0), cont);
          FM.GroupOkLBActsCons(LS.Acheck(inp), [LS.Areg(q0)] + cont);
          FM.GroupOkLBActsCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
          assert [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont
              == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
          ComputeTreeLooksLB(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, inp,
                             LG.GMReset(gidl, gm), dir, f);
          ComputeTreeLooksLB(rer, cont, inp, gm, dir, f);
        }
      case Group(gid, r1) =>
        FM.GroupOkLBActsCons(LS.Aclose(gid), cont);
        FM.GroupOkLBActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        assert [LS.Areg(r1), LS.Aclose(gid)] + cont == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
        ComputeTreeLooksLB(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp,
                           LG.GMOpen(LC.Idx(inp), gid, gm), dir, f);
      case LookaroundR(lk, r1) =>
        assert FM.GroupOkLBActs([LS.Areg(r1)]);
        ComputeTreeLooksLB(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), f);
        var bl := FS.ComputeTree(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), f);
        if bl.Some? {
          match LS.LkResult(lk, bl.value, gm, inp) {
            case Some(gmlk) => ComputeTreeLooksLB(rer, cont, inp, gmlk, dir, f);
            case None =>
          }
        }
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) { ComputeTreeLooksLB(rer, cont, inp, gm, dir, f); }
      case Backreference(_) =>
  }

  /** INSTANCE: the one-way original's exact postcondition, re-derived from the
      generic builder at `dir == Backward`. */
  lemma ComputeTreeReverseFViaG(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                                gm1: LG.GroupMap, gm2: LG.GroupMap, fuel: nat)
    requires FM.GroupOkLBActs(acts)
    ensures var b := FS.ComputeTree(rer, acts, inp, gm1, WP.Backward, fuel);
            var fw := FS.ComputeTree(rer, FM.FlipRevActs(acts), SD.SwapInput(inp), gm2,
                                     WP.Forward, fuel);
            (b.None? <==> fw.None?)
            && (b.Some? && fw.Some? ==> FM.TreeMirrorRelF(b.value, fw.value))
  {
    GroupOkLBActsNoBackref(acts);
    ComputeTreeReverseG(rer, acts, inp, gm1, gm2, WP.Backward, fuel);
    ComputeTreeLooksLB(rer, acts, inp, gm1, WP.Backward, fuel);
    var b := FS.ComputeTree(rer, acts, inp, gm1, WP.Backward, fuel);
    var fw := FS.ComputeTree(rer, FM.FlipRevActs(acts), SD.SwapInput(inp), gm2, WP.Forward, fuel);
    if b.Some? && fw.Some? { TreeMirrorRelGLBIsF(b.value, fw.value); }
  }

  /** INSTANCE: the one-way value fold from the generic one (F ⊆ G, dir = Backward). */
  lemma TreeResMirrorFViaG(t: LT.Tree, tm: LT.Tree, gm1: LG.GroupMap,
                           inp: LC.Input, n: nat, O: set<LG.GroupId>)
    requires FM.TreeMirrorRelF(t, tm)
    requires n == |inp.pref| + |inp.next|
    requires TRM.GmInBounds(gm1, n)
    requires FM.CloseDiscF(t, O)
    requires TRM.OpenSubset(gm1, O)
    ensures var rb := LT.TreeRes(t, gm1, inp, WP.Backward);
            var rf := LT.TreeRes(tm, TRM.MirrorGm(gm1, n), SD.SwapInput(inp), WP.Forward);
            && (rb.None? <==> rf.None?)
            && (rb.Some? ==>
                  && rf.Some?
                  && rf.value.0 == SD.SwapInput(rb.value.0)
                  && TRM.GmInBounds(rb.value.1, n)
                  && rf.value.1 == TRM.MirrorGm(rb.value.1, n))
  {
    TreeMirrorRelFIsG(t, tm);
    TreeResMirrorG(t, tm, gm1, inp, WP.Backward, n, O);
  }

  /** ANTI-VACUITY: the generic builder applies to a LOOKAHEAD inside a
      LOOKBEHIND (`(?<=a(?=b))`-shaped), walked FORWARD — a shape the one-way
      original cannot even state. */
  lemma FlipMirrorGSatisfiableMixed(rer: LW.RegExpRecord, ca: LC.CharDescr, cb: LC.CharDescr,
                                    inp: LC.Input, gm1: LG.GroupMap, gm2: LG.GroupMap)
    ensures var r := L.LookaroundR(L.LookBehind,
                       L.Sequence(L.Character(ca),
                                  L.LookaroundR(L.LookAhead, L.Group(0, L.Character(cb)))));
            TreeMirrorRelG(FU.ComputeTr(rer, [LS.Areg(r)], inp, gm1, WP.Forward),
                           FU.ComputeTr(rer, FM.FlipRevActs([LS.Areg(r)]), SD.SwapInput(inp), gm2,
                                        WP.Backward))
  {
    var r := L.LookaroundR(L.LookBehind,
               L.Sequence(L.Character(ca),
                          L.LookaroundR(L.LookAhead, L.Group(0, L.Character(cb)))));
    var g := L.Group(0, L.Character(cb));
    assert SD.NoBackrefL(L.Character(ca)) && SD.NoBackrefL(L.Character(cb));
    assert SD.NoBackrefL(g);
    assert SD.NoBackrefL(L.LookaroundR(L.LookAhead, g));
    assert SD.NoBackrefL(L.Sequence(L.Character(ca), L.LookaroundR(L.LookAhead, g)));
    assert SD.NoBackrefL(r);
    assert SD.NoBackrefActs([LS.Areg(r)]);
    assert OppDir(WP.Forward) == WP.Backward;
    ComputeTrReverseG(rer, [LS.Areg(r)], inp, gm1, gm2, WP.Forward);
  }
}
