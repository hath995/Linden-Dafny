// L3b (linden-equiv LOOKAROUND_CAMPAIGN.md §4.5.1 item 4, the leaf-fold half):
// the leaf-VALUE mirror. TreeMirror.dfy relates the backward backtracking
// tree of a group-OK stack to the forward tree of the reversed stack,
// preserving priority (TreeMirrorRel). This file folds those trees to
// leaves: TreeRes of the backward tree at a group map gm1 and TreeRes of the
// forward tree at the MIRRORED group map correspond — None iff None, and on
// a match the winning leaf's input/captures mirror.
//
// THE DECIDED RANGE MIRROR (LOOKAROUND_CAMPAIGN §L3b item 0 finding). Under
// the position map v |-> n - v (n = total input length), a group's captured
// span mirrors as:
//   OPEN   Range(s, None)      |->  Range(n - s, None)
//   CLOSED Range(s, Some(e))   |->  Range(n - e, Some(n - s))
// This is an involution and — crucially — it is EXACTLY what GMClose's own
// min/max endpoint normalization (Groups.dfy:65) produces on both sides of
// the reversal, PROVIDED every Close fires on a currently-open group. That
// proviso is the `CloseDisc` invariant (a Close on an already-closed group
// would let GMClose drop the stale end and break the mirror). `CloseDisc`
// holds for real ComputeTree trees under group-id uniqueness (the Reset at
// each quantifier iteration re-opens the discipline) — established
// separately; here it is a hypothesis.

include "TreeMirror.dfy"

module LindenTreeResMirror {
  import opened Std.Wrappers
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import LT = Tree
  import SD = LindenSpanDuality
  import TM = LindenTreeMirror

  // ===========================================================================
  // The decided range mirror
  // ===========================================================================

  /** Every range in `gm` has both endpoints within `[0, n]` — needed for the
      nat subtraction `n - .` in `MirrorRange` to be well-defined. */
  ghost predicate GmInBounds(gm: LG.GroupMap, n: nat) {
    forall g :: g in gm ==>
      gm[g].startIdx <= n && (gm[g].endIdx.Some? ==> gm[g].endIdx.value <= n)
  }

  /** The decided range mirror of one range under `v |-> n - v`. Open stays
      open; closed swaps and reflects its endpoints. */
  function MirrorRange(rg: LG.Range, n: nat): LG.Range
    requires rg.startIdx <= n
    requires rg.endIdx.Some? ==> rg.endIdx.value <= n
  {
    match rg.endIdx
    case None => LG.Range(n - rg.startIdx, None)
    case Some(e) => LG.Range(n - e, Some(n - rg.startIdx))
  }

  /** The decided mirror of a whole group map: same domain, each range
      mirrored. */
  function MirrorGm(gm: LG.GroupMap, n: nat): LG.GroupMap
    requires GmInBounds(gm, n)
  {
    map g | g in gm :: MirrorRange(gm[g], n)
  }

  lemma MirrorGmAt(gm: LG.GroupMap, n: nat)
    requires GmInBounds(gm, n)
    ensures forall g :: g in MirrorGm(gm, n) <==> g in gm
    ensures forall g :: g in gm ==> MirrorGm(gm, n)[g] == MirrorRange(gm[g], n)
  {}

  /** Openness is preserved by the mirror (None <-> None). */
  lemma MirrorGmOpen(gm: LG.GroupMap, n: nat, g: LG.GroupId)
    requires GmInBounds(gm, n)
    ensures g in MirrorGm(gm, n) <==> g in gm
    ensures g in gm ==> (MirrorGm(gm, n)[g].endIdx.None? <==> gm[g].endIdx.None?)
  {}

  // ===========================================================================
  // The Close discipline
  // ===========================================================================

  /** `O` under-approximates the currently-open groups of `gm`. */
  ghost predicate OpenSubset(gm: LG.GroupMap, O: set<LG.GroupId>) {
    forall g :: g in O ==> g in gm && gm[g].endIdx.None?
  }

  /** Every `Close(g)` in `t` fires on a group that is open at that point in
      the walk (`O` = the set of gids opened-but-not-closed so far). Purely
      structural; `LK`/`LKFail`/`ReadBackRef` are outside the group-OK
      fragment. */
  ghost predicate CloseDisc(t: LT.Tree, O: set<LG.GroupId>)
    decreases t
  {
    match t
    case Mismatch => true
    case Match => true
    case Choice(a, b) => CloseDisc(a, O) && CloseDisc(b, O)
    case Read(_, a) => CloseDisc(a, O)
    case Progress(a) => CloseDisc(a, O)
    case AnchorPass(_, a) => CloseDisc(a, O)
    case GroupActionT(ga, a) =>
      match ga {
        case Open(g) => CloseDisc(a, O + {g})
        case Close(g) => g in O && CloseDisc(a, O - {g})
        case Reset(gl) => CloseDisc(a, O - (set g | g in gl))
      }
    case LK(_, _, _) => false
    case LKFail(_, _) => false
    case ReadBackRef(_, _) => false
  }

  // ===========================================================================
  // Input plumbing
  // ===========================================================================

  /** The total-version advance commutes with the swap (from `AdvanceInputSwap`). */
  lemma AdvanceInputPSwap(inp: LC.Input)
    ensures LC.AdvanceInputP(SD.SwapInput(inp), WP.Forward)
         == SD.SwapInput(LC.AdvanceInputP(inp, WP.Backward))
  {
    SD.AdvanceInputSwap(inp);
    match LC.AdvanceInput(inp, WP.Backward)
    case None =>
    case Some(ni) =>
  }

  /** Advancing preserves the total input length. */
  lemma AdvanceInputPLen(inp: LC.Input, dir: WP.Direction)
    ensures |LC.AdvanceInputP(inp, dir).pref| + |LC.AdvanceInputP(inp, dir).next|
         == |inp.pref| + |inp.next|
  {}

  // ===========================================================================
  // Group-map update mirror lemmas
  // ===========================================================================

  /** Opening `g` commutes with the mirror: opening at `c` on the backward
      side matches opening at `n - c` on the mirrored side. */
  lemma GMOpenMirror(gm1: LG.GroupMap, g: LG.GroupId, c: nat, n: nat)
    requires c <= n
    requires GmInBounds(gm1, n)
    ensures GmInBounds(LG.GMOpen(c, g, gm1), n)
    ensures MirrorGm(LG.GMOpen(c, g, gm1), n)
         == LG.GMOpen(n - c, g, MirrorGm(gm1, n))
  {
    var gm2 := MirrorGm(gm1, n);
    var lhs := LG.GMOpen(c, g, gm1);
    var rhs := LG.GMOpen(n - c, g, gm2);
    assert lhs[g] == LG.Range(c, None);
    assert GmInBounds(lhs, n);
    forall h | h in MirrorGm(lhs, n)
      ensures h in rhs && MirrorGm(lhs, n)[h] == rhs[h]
    {
      if h == g {
        assert MirrorGm(lhs, n)[g] == MirrorRange(LG.Range(c, None), n);
        assert MirrorRange(LG.Range(c, None), n) == LG.Range(n - c, None);
        assert rhs[g] == LG.Range(n - c, None);
      } else {
        assert lhs[h] == gm1[h];
      }
    }
    assert MirrorGm(lhs, n).Keys == rhs.Keys;
  }

  /** Closing an OPEN `g` commutes with the mirror. GMClose's min/max
      normalization on each side is precisely `MirrorRange`. */
  lemma GMCloseMirror(gm1: LG.GroupMap, g: LG.GroupId, c: nat, n: nat)
    requires c <= n
    requires GmInBounds(gm1, n)
    requires g in gm1 && gm1[g].endIdx.None?
    ensures GmInBounds(LG.GMClose(c, g, gm1), n)
    ensures MirrorGm(LG.GMClose(c, g, gm1), n)
         == LG.GMClose(n - c, g, MirrorGm(gm1, n))
  {
    var s := gm1[g].startIdx;
    var gm2 := MirrorGm(gm1, n);
    assert gm2[g] == LG.Range(n - s, None);
    var lhs := LG.GMClose(c, g, gm1);
    var rhs := LG.GMClose(n - c, g, gm2);
    // lhs[g] and rhs[g], by the s<=c / s>c case split.
    if s <= c {
      assert lhs[g] == LG.Range(s, Some(c));
      if s < c {
        assert !(n - s <= n - c);
        assert rhs[g] == LG.Range(n - c, Some(n - s));
      } else {
        assert rhs[g] == LG.Range(n - s, Some(n - c));
      }
      assert MirrorRange(lhs[g], n) == LG.Range(n - c, Some(n - s));
      assert rhs[g] == MirrorRange(lhs[g], n);
    } else {
      assert lhs[g] == LG.Range(c, Some(s));
      assert n - s <= n - c;
      assert rhs[g] == LG.Range(n - s, Some(n - c));
      assert MirrorRange(lhs[g], n) == LG.Range(n - s, Some(n - c));
      assert rhs[g] == MirrorRange(lhs[g], n);
    }
    assert GmInBounds(lhs, n);
    forall h | h in MirrorGm(lhs, n)
      ensures h in rhs && MirrorGm(lhs, n)[h] == rhs[h]
    {
      if h == g {
        assert MirrorGm(lhs, n)[g] == MirrorRange(lhs[g], n);
      } else {
        assert lhs[h] == gm1[h];
      }
    }
    assert MirrorGm(lhs, n).Keys == rhs.Keys;
  }

  /** Resetting commutes with the mirror; the two reset sets need only agree
      as sets (`GroupActionMirror`). */
  lemma GMResetMirror(gm1: LG.GroupMap, gl: LG.GroupSet, gl2: LG.GroupSet, n: nat)
    requires GmInBounds(gm1, n)
    requires forall g :: g in gl <==> g in gl2
    ensures GmInBounds(LG.GMReset(gl, gm1), n)
    ensures MirrorGm(LG.GMReset(gl, gm1), n)
         == LG.GMReset(gl2, MirrorGm(gm1, n))
  {
    var gm2 := MirrorGm(gm1, n);
    var lhs := LG.GMReset(gl, gm1);
    var rhs := LG.GMReset(gl2, gm2);
    assert (set g | g in gl) == (set g | g in gl2);
    assert GmInBounds(lhs, n);
    forall h | h in MirrorGm(lhs, n)
      ensures h in rhs && MirrorGm(lhs, n)[h] == rhs[h]
    {
      assert lhs[h] == gm1[h];
    }
    assert MirrorGm(lhs, n).Keys == rhs.Keys;
  }

  // ===========================================================================
  // THE LEAF-FOLD MIRROR
  // ===========================================================================

  /** The payoff: folding the backward tree `t` (at `gm1`, backward) and the
      forward mirror tree `tm` (at `MirrorGm(gm1)`, forward over the swapped
      input) yields corresponding results — same match/no-match, and on a
      match the winning leaf's input is `SwapInput`-related and its captures
      are `MirrorGm`-related. */
  lemma TreeResMirror(t: LT.Tree, tm: LT.Tree, gm1: LG.GroupMap,
                      inp: LC.Input, n: nat, O: set<LG.GroupId>)
    requires TM.TreeMirrorRel(t, tm)
    requires n == |inp.pref| + |inp.next|
    requires GmInBounds(gm1, n)
    requires CloseDisc(t, O)
    requires OpenSubset(gm1, O)
    ensures var rb := LT.TreeRes(t, gm1, inp, WP.Backward);
            var rf := LT.TreeRes(tm, MirrorGm(gm1, n), SD.SwapInput(inp), WP.Forward);
            && (rb.None? <==> rf.None?)
            && (rb.Some? ==>
                  && rf.Some?
                  && rf.value.0 == SD.SwapInput(rb.value.0)
                  && GmInBounds(rb.value.1, n)
                  && rf.value.1 == MirrorGm(rb.value.1, n))
    decreases t
  {
    var gm2 := MirrorGm(gm1, n);
    var sinp := SD.SwapInput(inp);
    assert LC.Idx(sinp) == n - LC.Idx(inp);
    match t
    case Mismatch =>
    case Match =>
    case Choice(a, b) =>
      match tm {
        case Choice(am, bm) =>
          TreeResMirror(a, am, gm1, inp, n, O);
          TreeResMirror(b, bm, gm1, inp, n, O);
        case _ =>
      }
    case Read(c, a) =>
      match tm {
        case Read(cm, am) =>
          var inp' := LC.AdvanceInputP(inp, WP.Backward);
          AdvanceInputPSwap(inp);
          AdvanceInputPLen(inp, WP.Backward);
          assert LC.AdvanceInputP(sinp, WP.Forward) == SD.SwapInput(inp');
          TreeResMirror(a, am, gm1, inp', n, O);
        case _ =>
      }
    case Progress(a) =>
      match tm {
        case Progress(am) => TreeResMirror(a, am, gm1, inp, n, O);
        case _ =>
      }
    case AnchorPass(x, a) =>
      match tm {
        case AnchorPass(xm, am) => TreeResMirror(a, am, gm1, inp, n, O);
        case _ =>
      }
    case GroupActionT(ga, a) =>
      match tm {
        case GroupActionT(gam, am) =>
          match ga {
            case Open(g) =>
              assert gam == LG.Open(g);
              GMOpenMirror(gm1, g, LC.Idx(inp), n);
              var gm1' := LG.GMOpen(LC.Idx(inp), g, gm1);
              assert LG.GMUpdate(gam, LC.Idx(sinp), gm2)
                  == LG.GMOpen(n - LC.Idx(inp), g, gm2);
              assert OpenSubset(gm1', O + {g}) by {
                forall h | h in O + {g} ensures h in gm1' && gm1'[h].endIdx.None? {}
              }
              TreeResMirror(a, am, gm1', inp, n, O + {g});
            case Close(g) =>
              assert gam == LG.Close(g);
              assert g in O;
              assert g in gm1 && gm1[g].endIdx.None?;
              GMCloseMirror(gm1, g, LC.Idx(inp), n);
              var gm1' := LG.GMClose(LC.Idx(inp), g, gm1);
              assert LG.GMUpdate(gam, LC.Idx(sinp), gm2)
                  == LG.GMClose(n - LC.Idx(inp), g, gm2);
              assert OpenSubset(gm1', O - {g}) by {
                forall h | h in O - {g} ensures h in gm1' && gm1'[h].endIdx.None? {}
              }
              TreeResMirror(a, am, gm1', inp, n, O - {g});
            case Reset(gl) =>
              assert gam.Reset?;
              GMResetMirror(gm1, gl, gam.gl, n);
              var gm1' := LG.GMReset(gl, gm1);
              assert LG.GMUpdate(gam, LC.Idx(sinp), gm2) == LG.GMReset(gam.gl, gm2);
              assert OpenSubset(gm1', O - (set x | x in gl)) by {
                forall h | h in O - (set x | x in gl)
                  ensures h in gm1' && gm1'[h].endIdx.None? {}
              }
              TreeResMirror(a, am, gm1', inp, n, O - (set x | x in gl));
          }
        case _ =>
      }
    case LK(_, _, _) =>
    case LKFail(_, _) =>
    case ReadBackRef(_, _) =>
  }
}
