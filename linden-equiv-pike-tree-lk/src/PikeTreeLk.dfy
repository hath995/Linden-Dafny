// The LK-AWARE PikeTree machine ("machine B") and its FirstLeaf correctness.
//
// L3a §2 needs the winning thread's reconstructed inside-look captures tied to
// FirstLeaf(t) of the SPEC tree t — but the simulation runs on the checked tree
// tstar, which is GATE-TRANSPARENT: LK nodes are dissolved, so no state the
// simulation holds ever contains one, and the per-thread inside-look values
// have nothing spec-side to be equal TO. This file supplies the missing spec
// side: a PikeTree machine that steps LK nodes DIRECTLY — a positive gate is a
// zero-width group-map update via LkResult (exactly like GroupActionT), a
// failed gate is a dead branch — together with the mirror of the machine's
// correctness invariant, so a full trace of THIS machine on t pins its best to
// FirstLeaf(t, inp).
//
// The eventual parallel simulation (VM ↔ this machine) then makes the winning
// thread's trace a machine-B trace whose per-gate gm merges are keystone-tied
// to the just-written a_cp[l] — closing the position gate without ever naming
// "the position of the LK node" as a separate theorem.
//
// Everything here is a faithful mirror of linden-engine's PikeTree.dfy
// invariant layer (Piketreeinv / PtsPreservation / InitPiketreeInv), with two
// new head shapes:
//   LK(lk, tlk, tc):  LkResult(lk, tlk, gm, inp).Some?  → step to (tc, merged)
//                     LkResult(...).None?               → dead
//   LKFail(_, _):                                         dead
// TreeRes's own LK case has exactly this shape (Tree.dfy:148-157), so the
// grounding lemmas extend case-by-case. PT.Size does not count the body tlk,
// so the LK descent (into tc) is size-decreasing for AddParentTreeLk, and the
// machine state datatype is REUSED from PT (only the step relation differs).
/** The LK-aware PikeTree machine and its correctness invariant: `PikeTreeStepLk`
    steps lookaround nodes as zero-width `LkResult` group-map updates, and
    `PiketreeinvLk`/`PtsPreservationLk`/`InitPiketreeinvLk` mirror the engine
    machine's proof that a completed trace's `best` is `FirstLeaf(t, inp)`. */
module LindenElkPikeTreeLk {
  import opened Std.Wrappers
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import LT = Tree
  import L = Regex
  import LS = Semantics
  import PT = PikeTree
  import SS = SeenSets

  // ==========================================================================
  // The machine. State shape reused from PT; only the step differs.
  // ==========================================================================

  /** One step of LK-aware tree exploration at input `inp` (the full input, not
      just its index: `LkResult` reads the position). Identical to
      `PT.TreeBfsStep` on every gate-free shape. */
  function TreeBfsStepLk(t: LT.Tree, gm: LG.GroupMap, inp: LC.Input): PT.StepResult {
    match t
    case Mismatch => PT.StepDead()
    case ReadBackRef(_, _) => PT.StepDead()
    case AnchorPass(_, t1) => PT.StepActive([(t1, gm)])
    case LK(lk, tlk, t1) =>
      (match LS.LkResult(lk, tlk, gm, inp)
       case None => PT.StepDead()
       case Some(gm1) => PT.StepActive([(t1, gm1)]))
    case LKFail(_, _) => PT.StepDead()
    case Match => PT.StepMatch
    case Choice(t1, t2) => PT.StepActive([(t1, gm), (t2, gm)])
    case Read(c, t1) => PT.StepBlocked(t1)
    case Progress(t1) => PT.StepActive([(t1, gm)])
    case GroupActionT(a, t1) => PT.StepActive([(t1, LG.GMUpdate(a, LC.Idx(inp), gm))])
  }

  /** The LK-aware step relation — `PT.PikeTreeStep` with `TreeBfsStepLk`. */
  ghost predicate PikeTreeStepLk(s1: PT.PikeTreeState, s2: PT.PikeTreeState) {
    match s1
    case PTS_final(_) => false
    case PTS(inp, active, best, blocked, seen) =>
      // pts_skip
      (|active| > 0 && SS.Inseen(seen, active[0].0) && s2 == PT.PTS(inp, active[1..], best, blocked, seen))
      // pts_final
      || (|active| == 0 && |blocked| == 0 && s2 == PT.PTS_final(best))
      // pts_nextchar
      || (|active| == 0 && |blocked| > 0 && s2 == PT.PTS(PT.NextInp(inp), blocked, best, [], SS.InitialSeenTrees))
      // pts_active
      || (|active| > 0 &&
          (match TreeBfsStepLk(active[0].0, active[0].1, inp)
           case StepActive(na) => s2 == PT.PTS(inp, na + active[1..], best, blocked, SS.AddSeenTrees(seen, active[0].0))
           case _ => false))
      // pts_match
      || (|active| > 0 &&
          (match TreeBfsStepLk(active[0].0, active[0].1, inp)
           case StepMatch => s2 == PT.PTS(inp, [], Some((inp, active[0].1)), blocked, SS.AddSeenTrees(seen, active[0].0))
           case _ => false))
      // pts_blocked
      || (|active| > 0 &&
          (match TreeBfsStepLk(active[0].0, active[0].1, inp)
           case StepBlocked(newt) => s2 == PT.PTS(inp, active[1..], best, blocked + [(newt, active[0].1)], SS.AddSeenTrees(seen, active[0].0))
           case _ => false))
  }

  /** Trees the LK-aware machine explores: `PT`'s pike subset plus LK/LKFail
      heads. The BODY `tlk` is unconstrained — the machine never explores it
      (`LkResult` evaluates it as a function). */
  predicate PikeSubtreeLk(t: LT.Tree)
    decreases t
  {
    match t
    case Mismatch => true
    case Match => true
    case Choice(t1, t2) => PikeSubtreeLk(t1) && PikeSubtreeLk(t2)
    case Read(_, t1) => PikeSubtreeLk(t1)
    case Progress(t1) => PikeSubtreeLk(t1)
    case GroupActionT(_, t1) => PikeSubtreeLk(t1)
    case ReadBackRef(_, _) => false
    case AnchorPass(_, t1) => PikeSubtreeLk(t1)
    case LK(_, _, t1) => PikeSubtreeLk(t1)
    case LKFail(_, _) => true
  }

  /** Every tree in the worklist is `PikeSubtreeLk`. */
  ghost predicate PikeListLk(l: seq<(LT.Tree, LG.GroupMap)>) {
    forall i :: 0 <= i < |l| ==> PikeSubtreeLk(l[i].0)
  }

  /** Head/tail split of `PikeListLk`. */
  lemma PikeListLkCons(t: LT.Tree, gm: LG.GroupMap, l: seq<(LT.Tree, LG.GroupMap)>)
    requires PikeListLk([(t, gm)] + l)
    ensures PikeSubtreeLk(t) && PikeListLk(l)
  {
    assert ([(t, gm)] + l)[0].0 == t;
    forall i | 0 <= i < |l| ensures PikeSubtreeLk(l[i].0) {
      assert ([(t, gm)] + l)[i + 1] == l[i];
    }
  }

  /** `PikeListLk` distributes over append. */
  lemma PikeListLkApp(l1: seq<(LT.Tree, LG.GroupMap)>, l2: seq<(LT.Tree, LG.GroupMap)>)
    requires PikeListLk(l1) && PikeListLk(l2)
    ensures PikeListLk(l1 + l2)
  {
    forall i | 0 <= i < |l1 + l2| ensures PikeSubtreeLk((l1 + l2)[i].0) {
      if i < |l1| { assert (l1 + l2)[i] == l1[i]; } else { assert (l1 + l2)[i] == l2[i - |l1|]; }
    }
  }

  // ==========================================================================
  // The TreeRes ↔ LkResult unfolding: TreeRes's own LK case IS the step rule.
  // ==========================================================================

  /** `TreeRes` at an `LK` node is: dead if the gate's `LkResult` is `None`,
      else the continuation at the merged map — definitionally, in both
      polarities (`LkResult` and `TreeRes.LK` match on the same scrutinee). */
  lemma TreeResLkUnfold(lk: L.Lookaround, tlk: LT.Tree, t1: LT.Tree, gm: LG.GroupMap, inp: LC.Input)
    ensures LT.TreeRes(LT.LK(lk, tlk, t1), gm, inp, WP.Forward)
         == (match LS.LkResult(lk, tlk, gm, inp)
             case None => None
             case Some(gm1) => LT.TreeRes(t1, gm1, inp, WP.Forward))
  {
  }

  // ==========================================================================
  // The nondeterministic (memoization-tolerant) result relation — the mirror
  // of PT.TreeNd with the two new head shapes.
  // ==========================================================================

  /** LK-aware `PT.TreeNd`: every outcome obtainable by walking `t`, optionally
      skipping seen subtrees; an `LK` head threads `LkResult`'s merged map (or
      dies), `LKFail` dies. */
  ghost predicate TreeNdLk(t: LT.Tree, gm: LG.GroupMap, inp: LC.Input, seen: SS.SeenTrees, res: Option<LT.Leaf>)
    decreases t
  {
    (SS.Inseen(seen, t) && res == None)  // tr_skip
    || (match t
        case Mismatch => res == None
        case Match => res == Some((inp, gm))
        case Choice(t1, t2) =>
          exists l1, l2 :: TreeNdLk(t1, gm, inp, seen, l1) && TreeNdLk(t2, gm, inp, seen, l2) && res == LT.Seqop(l1, l2)
        case Read(c, t1) => TreeNdLk(t1, gm, PT.NextInp(inp), seen, res)
        case Progress(t1) => TreeNdLk(t1, gm, inp, seen, res)
        case AnchorPass(_, t1) => TreeNdLk(t1, gm, inp, seen, res)
        case GroupActionT(act, t1) => TreeNdLk(t1, LG.GMUpdate(act, LC.Idx(inp), gm), inp, seen, res)
        case LK(lk, tlk, t1) =>
          (match LS.LkResult(lk, tlk, gm, inp)
           case None => res == None
           case Some(gm1) => TreeNdLk(t1, gm1, inp, seen, res))
        case LKFail(_, _) => res == None
        case ReadBackRef(_, _) => false)
  }

  /** List version of `TreeNdLk` (mirror of `PT.ListNd`). */
  ghost predicate ListNdLk(l: seq<(LT.Tree, LG.GroupMap)>, inp: LC.Input, seen: SS.SeenTrees, res: Option<LT.Leaf>)
    decreases l
  {
    if |l| == 0 then res == None
    else exists l1, l2 :: TreeNdLk(l[0].0, l[0].1, inp, seen, l1) && ListNdLk(l[1..], inp, seen, l2) && res == LT.Seqop(l1, l2)
  }

  /** The possible final results of a whole machine state (mirror of `PT.StateNd`). */
  ghost predicate StateNdLk(inp: LC.Input, active: seq<(LT.Tree, LG.GroupMap)>, best: Option<LT.Leaf>,
                            blocked: seq<(LT.Tree, LG.GroupMap)>, seen: SS.SeenTrees, rseq: Option<LT.Leaf>) {
    exists r2 :: ListNdLk(active, inp, seen, r2)
                 && rseq == LT.Seqop(PT.ListResult(blocked, PT.NextInp(inp)), LT.Seqop(r2, best))
  }

  /** The central correctness invariant (mirror of `PT.Piketreeinv`). */
  ghost predicate PiketreeinvLk(s: PT.PikeTreeState, result: Option<LT.Leaf>) {
    match s
    case PTS_final(best) => best == result
    case PTS(inp, active, best, blocked, seen) =>
      (forall res :: StateNdLk(inp, active, best, blocked, seen, res) ==> res == result)
      && PikeListLk(active) && PikeListLk(blocked)
  }

  // ==========================================================================
  // Grounding: TreeRes is a valid Nd outcome; with nothing seen it is the ONLY
  // one. Mirrors of PT.TreeResNd / TreeNdInitial (+ list versions).
  // ==========================================================================

  /** `TreeRes` is a valid `TreeNdLk` outcome (never skip). */
  lemma TreeResNdLk(t: LT.Tree, gm: LG.GroupMap, inp: LC.Input, seen: SS.SeenTrees)
    requires PikeSubtreeLk(t)
    ensures TreeNdLk(t, gm, inp, seen, LT.TreeRes(t, gm, inp, WP.Forward))
    decreases t
  {
    match t
    case Mismatch =>
    case Match =>
    case Choice(t1, t2) =>
      TreeResNdLk(t1, gm, inp, seen);
      TreeResNdLk(t2, gm, inp, seen);
      assert TreeNdLk(t1, gm, inp, seen, LT.TreeRes(t1, gm, inp, WP.Forward));
      assert TreeNdLk(t2, gm, inp, seen, LT.TreeRes(t2, gm, inp, WP.Forward));
    case Read(c, t1) =>
      TreeResNdLk(t1, gm, PT.NextInp(inp), seen);
    case Progress(t1) =>
      TreeResNdLk(t1, gm, inp, seen);
    case GroupActionT(a, t1) =>
      TreeResNdLk(t1, LG.GMUpdate(a, LC.Idx(inp), gm), inp, seen);
    case ReadBackRef(_, _) =>
    case AnchorPass(_, t1) =>
      TreeResNdLk(t1, gm, inp, seen);
    case LK(lk, tlk, t1) =>
      TreeResLkUnfold(lk, tlk, t1, gm, inp);
      match LS.LkResult(lk, tlk, gm, inp) {
        case None =>
        case Some(gm1) => TreeResNdLk(t1, gm1, inp, seen);
      }
    case LKFail(_, _) =>
  }

  /** With the empty seen set, `TreeNdLk` collapses to exactly `TreeRes`. */
  lemma TreeNdInitialLk(t: LT.Tree, gm: LG.GroupMap, inp: LC.Input, res: Option<LT.Leaf>)
    requires PikeSubtreeLk(t)
    requires TreeNdLk(t, gm, inp, SS.InitialSeenTrees, res)
    ensures res == LT.TreeRes(t, gm, inp, WP.Forward)
    decreases t
  {
    SS.InitialNothing(t);
    match t
    case Mismatch =>
    case Match =>
    case Choice(t1, t2) =>
      var l1, l2 :| TreeNdLk(t1, gm, inp, SS.InitialSeenTrees, l1) && TreeNdLk(t2, gm, inp, SS.InitialSeenTrees, l2) && res == LT.Seqop(l1, l2);
      TreeNdInitialLk(t1, gm, inp, l1);
      TreeNdInitialLk(t2, gm, inp, l2);
    case Read(c, t1) =>
      TreeNdInitialLk(t1, gm, PT.NextInp(inp), res);
    case Progress(t1) =>
      TreeNdInitialLk(t1, gm, inp, res);
    case GroupActionT(a, t1) =>
      TreeNdInitialLk(t1, LG.GMUpdate(a, LC.Idx(inp), gm), inp, res);
    case ReadBackRef(_, _) =>
    case AnchorPass(_, t1) =>
      TreeNdInitialLk(t1, gm, inp, res);
    case LK(lk, tlk, t1) =>
      TreeResLkUnfold(lk, tlk, t1, gm, inp);
      match LS.LkResult(lk, tlk, gm, inp) {
        case None =>
        case Some(gm1) => TreeNdInitialLk(t1, gm1, inp, res);
      }
    case LKFail(_, _) =>
  }

  /** List version of `TreeResNdLk`. */
  lemma ListResultNdLk(active: seq<(LT.Tree, LG.GroupMap)>, inp: LC.Input, seen: SS.SeenTrees)
    requires PikeListLk(active)
    ensures ListNdLk(active, inp, seen, PT.ListResult(active, inp))
    decreases active
  {
    if |active| == 0 {
      assert PT.ListResult(active, inp) == None;
    } else {
      var t := active[0].0;
      var gm := active[0].1;
      assert active == [(t, gm)] + active[1..];
      assert PikeSubtreeLk(t);
      assert PikeListLk(active[1..]) by {
        forall i | 0 <= i < |active[1..]| ensures PikeSubtreeLk(active[1..][i].0) { assert active[1..][i] == active[i + 1]; }
      }
      TreeResNdLk(t, gm, inp, seen);
      ListResultNdLk(active[1..], inp, seen);
      PT.ListResultCons(t, gm, active[1..], inp);
    }
  }

  /** List version of `TreeNdInitialLk`. */
  lemma ListNdInitialLk(l: seq<(LT.Tree, LG.GroupMap)>, inp: LC.Input, res: Option<LT.Leaf>)
    requires PikeListLk(l)
    requires ListNdLk(l, inp, SS.InitialSeenTrees, res)
    ensures res == PT.ListResult(l, inp)
    decreases l
  {
    if |l| == 0 {
      assert PT.ListResult(l, inp) == None;
    } else {
      var t := l[0].0;
      var gm := l[0].1;
      var l1, l2 :| TreeNdLk(t, gm, inp, SS.InitialSeenTrees, l1) && ListNdLk(l[1..], inp, SS.InitialSeenTrees, l2) && res == LT.Seqop(l1, l2);
      assert l == [(t, gm)] + l[1..];
      assert PikeSubtreeLk(t);
      assert PikeListLk(l[1..]) by {
        forall i | 0 <= i < |l[1..]| ensures PikeSubtreeLk(l[1..][i].0) { assert l[1..][i] == l[i + 1]; }
      }
      TreeNdInitialLk(t, gm, inp, l1);
      ListNdInitialLk(l[1..], inp, l2);
      PT.ListResultCons(t, gm, l[1..], inp);
    }
  }

  /** `TreeNdLk` yielding `None` transfers to any other `(gm, inp)` — the gate
      verdict is gm/inp-independent (`ResGroupMapIndep`), so the LK branch taken
      is the same on both sides. */
  lemma NoTreeResultNdLk(t: LT.Tree, seen: SS.SeenTrees, gm1: LG.GroupMap, gm2: LG.GroupMap, inp1: LC.Input, inp2: LC.Input)
    requires TreeNdLk(t, gm1, inp1, seen, None)
    ensures TreeNdLk(t, gm2, inp2, seen, None)
    decreases t
  {
    if SS.Inseen(seen, t) {
    } else {
      match t
      case Mismatch =>
      case Match =>
      case Choice(t1, t2) =>
        var l1, l2 :| TreeNdLk(t1, gm1, inp1, seen, l1) && TreeNdLk(t2, gm1, inp1, seen, l2) && None == LT.Seqop(l1, l2);
        assert l1 == None && l2 == None;
        NoTreeResultNdLk(t1, seen, gm1, gm2, inp1, inp2);
        NoTreeResultNdLk(t2, seen, gm1, gm2, inp1, inp2);
        assert TreeNdLk(t1, gm2, inp2, seen, None) && TreeNdLk(t2, gm2, inp2, seen, None);
      case Read(c, t1) =>
        NoTreeResultNdLk(t1, seen, gm1, gm2, PT.NextInp(inp1), PT.NextInp(inp2));
      case Progress(t1) =>
        NoTreeResultNdLk(t1, seen, gm1, gm2, inp1, inp2);
      case GroupActionT(a, t1) =>
        NoTreeResultNdLk(t1, seen, LG.GMUpdate(a, LC.Idx(inp1), gm1), LG.GMUpdate(a, LC.Idx(inp2), gm2), inp1, inp2);
      case ReadBackRef(_, _) =>
      case AnchorPass(_, t1) =>
        NoTreeResultNdLk(t1, seen, gm1, gm2, inp1, inp2);
      case LK(lk, tlk, t1) =>
        // the verdict agrees across (gm, inp): a None TreeRes on one side is
        // None on the other (ResGroupMapIndep), in both polarities
        match LS.LkResult(lk, tlk, gm1, inp1) {
          case None =>
            assert LS.LkResult(lk, tlk, gm2, inp2).None? by {
              if L.Positivity(lk) {
                assert LT.TreeRes(tlk, gm1, inp1, L.LkDir(lk)) == None;
                LT.ResGroupMapIndep(tlk, gm1, gm2, inp1, inp2, L.LkDir(lk), L.LkDir(lk));
              } else {
                assert LT.TreeRes(tlk, gm1, inp1, L.LkDir(lk)).Some?;
                if LT.TreeRes(tlk, gm2, inp2, L.LkDir(lk)) == None {
                  LT.ResGroupMapIndep(tlk, gm2, gm1, inp2, inp1, L.LkDir(lk), L.LkDir(lk));
                }
              }
            }
          case Some(gm1') =>
            assert LS.LkResult(lk, tlk, gm2, inp2).Some? by {
              if L.Positivity(lk) {
                assert LT.TreeRes(tlk, gm1, inp1, L.LkDir(lk)).Some?;
                if LT.TreeRes(tlk, gm2, inp2, L.LkDir(lk)) == None {
                  LT.ResGroupMapIndep(tlk, gm2, gm1, inp2, inp1, L.LkDir(lk), L.LkDir(lk));
                }
              } else {
                assert LT.TreeRes(tlk, gm1, inp1, L.LkDir(lk)) == None;
                LT.ResGroupMapIndep(tlk, gm1, gm2, inp1, inp2, L.LkDir(lk), L.LkDir(lk));
              }
            }
            var gm2' := LS.LkResult(lk, tlk, gm2, inp2).value;
            NoTreeResultNdLk(t1, seen, gm1', gm2', inp1, inp2);
        }
      case LKFail(_, _) =>
    }
  }

  // ==========================================================================
  // Memoization soundness: adding a FAILED tree to the seen set never changes
  // the reachable outcomes. Mirrors of PT.AddSeen / AddSeenNd / AddParentTree
  // (+ list versions). The LK case follows the GroupActionT template: the gm
  // changes under the node, so the "tseen fails" fact is carried across the
  // map change by NoTreeResult / NoTreeResultNdLk.
  // ==========================================================================

  /** Removing a failed (`TreeRes == None`) tree from `seen` preserves outcomes. */
  lemma AddSeenLk(t: LT.Tree, seen: SS.SeenTrees, tseen: LT.Tree, gm: LG.GroupMap, inp: LC.Input, res: Option<LT.Leaf>)
    requires LT.TreeRes(tseen, gm, inp, WP.Forward) == None
    requires TreeNdLk(t, gm, inp, SS.AddSeenTrees(seen, tseen), res)
    requires PikeSubtreeLk(tseen)
    ensures TreeNdLk(t, gm, inp, seen, res)
    decreases t
  {
    if SS.Inseen(SS.AddSeenTrees(seen, tseen), t) && res == None {
      SS.InAdd(seen, t, tseen);
      if t == tseen {
        TreeResNdLk(tseen, gm, inp, seen);
      }
    } else {
      match t
      case Mismatch =>
      case Match =>
      case Choice(t1, t2) =>
        var l1, l2 :| TreeNdLk(t1, gm, inp, SS.AddSeenTrees(seen, tseen), l1) && TreeNdLk(t2, gm, inp, SS.AddSeenTrees(seen, tseen), l2) && res == LT.Seqop(l1, l2);
        AddSeenLk(t1, seen, tseen, gm, inp, l1);
        AddSeenLk(t2, seen, tseen, gm, inp, l2);
      case Read(c, t1) =>
        PT.NoTreeResult(tseen, gm, gm, inp, PT.NextInp(inp));
        AddSeenLk(t1, seen, tseen, gm, PT.NextInp(inp), res);
      case Progress(t1) =>
        AddSeenLk(t1, seen, tseen, gm, inp, res);
      case GroupActionT(a, t1) =>
        PT.NoTreeResult(tseen, gm, LG.GMUpdate(a, LC.Idx(inp), gm), inp, inp);
        AddSeenLk(t1, seen, tseen, LG.GMUpdate(a, LC.Idx(inp), gm), inp, res);
      case ReadBackRef(_, _) =>
      case AnchorPass(_, t1) =>
        AddSeenLk(t1, seen, tseen, gm, inp, res);
      case LK(lk, tlk, t1) =>
        match LS.LkResult(lk, tlk, gm, inp) {
          case None =>
          case Some(gm1) =>
            PT.NoTreeResult(tseen, gm, gm1, inp, inp);
            AddSeenLk(t1, seen, tseen, gm1, inp, res);
        }
      case LKFail(_, _) =>
    }
  }

  /** List version of `AddSeenLk`. */
  lemma ListAddSeenLk(l: seq<(LT.Tree, LG.GroupMap)>, seen: SS.SeenTrees, tseen: LT.Tree, gm: LG.GroupMap, inp: LC.Input, res: Option<LT.Leaf>)
    requires LT.TreeRes(tseen, gm, inp, WP.Forward) == None
    requires ListNdLk(l, inp, SS.AddSeenTrees(seen, tseen), res)
    requires PikeSubtreeLk(tseen)
    ensures ListNdLk(l, inp, seen, res)
    decreases l
  {
    if |l| == 0 {
    } else {
      var t := l[0].0;
      var gm0 := l[0].1;
      var l1, l2 :| TreeNdLk(t, gm0, inp, SS.AddSeenTrees(seen, tseen), l1) && ListNdLk(l[1..], inp, SS.AddSeenTrees(seen, tseen), l2) && res == LT.Seqop(l1, l2);
      PT.NoTreeResult(tseen, gm, gm0, inp, inp);
      AddSeenLk(t, seen, tseen, gm0, inp, l1);
      ListAddSeenLk(l[1..], seen, tseen, gm, inp, l2);
    }
  }

  /** Like `AddSeenLk`, with the "failed" hypothesis itself nondeterministic. */
  lemma AddSeenNdLk(t: LT.Tree, seen: SS.SeenTrees, tseen: LT.Tree, gm: LG.GroupMap, inp: LC.Input, res: Option<LT.Leaf>)
    requires TreeNdLk(tseen, gm, inp, seen, None)
    requires TreeNdLk(t, gm, inp, SS.AddSeenTrees(seen, tseen), res)
    ensures TreeNdLk(t, gm, inp, seen, res)
    decreases t
  {
    if SS.Inseen(SS.AddSeenTrees(seen, tseen), t) && res == None {
      SS.InAdd(seen, t, tseen);
    } else {
      match t
      case Mismatch =>
      case Match =>
      case Choice(t1, t2) =>
        var l1, l2 :| TreeNdLk(t1, gm, inp, SS.AddSeenTrees(seen, tseen), l1) && TreeNdLk(t2, gm, inp, SS.AddSeenTrees(seen, tseen), l2) && res == LT.Seqop(l1, l2);
        AddSeenNdLk(t1, seen, tseen, gm, inp, l1);
        AddSeenNdLk(t2, seen, tseen, gm, inp, l2);
      case Read(c, t1) =>
        NoTreeResultNdLk(tseen, seen, gm, gm, inp, PT.NextInp(inp));
        AddSeenNdLk(t1, seen, tseen, gm, PT.NextInp(inp), res);
      case Progress(t1) =>
        AddSeenNdLk(t1, seen, tseen, gm, inp, res);
      case GroupActionT(a, t1) =>
        NoTreeResultNdLk(tseen, seen, gm, LG.GMUpdate(a, LC.Idx(inp), gm), inp, inp);
        AddSeenNdLk(t1, seen, tseen, LG.GMUpdate(a, LC.Idx(inp), gm), inp, res);
      case ReadBackRef(_, _) =>
      case AnchorPass(_, t1) =>
        AddSeenNdLk(t1, seen, tseen, gm, inp, res);
      case LK(lk, tlk, t1) =>
        match LS.LkResult(lk, tlk, gm, inp) {
          case None =>
          case Some(gm1) =>
            NoTreeResultNdLk(tseen, seen, gm, gm1, inp, inp);
            AddSeenNdLk(t1, seen, tseen, gm1, inp, res);
        }
      case LKFail(_, _) =>
    }
  }

  /** List version of `AddSeenNdLk`. */
  lemma ListAddSeenNdLk(l: seq<(LT.Tree, LG.GroupMap)>, seen: SS.SeenTrees, tseen: LT.Tree, gm: LG.GroupMap, inp: LC.Input, res: Option<LT.Leaf>)
    requires TreeNdLk(tseen, gm, inp, seen, None)
    requires ListNdLk(l, inp, SS.AddSeenTrees(seen, tseen), res)
    ensures ListNdLk(l, inp, seen, res)
    decreases l
  {
    if |l| == 0 {
    } else {
      var t := l[0].0;
      var gm0 := l[0].1;
      var l1, l2 :| TreeNdLk(t, gm0, inp, SS.AddSeenTrees(seen, tseen), l1) && ListNdLk(l[1..], inp, SS.AddSeenTrees(seen, tseen), l2) && res == LT.Seqop(l1, l2);
      NoTreeResultNdLk(tseen, seen, gm, gm0, inp, inp);
      AddSeenNdLk(t, seen, tseen, gm0, inp, l1);
      ListAddSeenNdLk(l[1..], seen, tseen, gm, inp, l2);
    }
  }

  /** A strictly larger memoized ancestor never triggers the skip case for a
      strictly smaller descendant (mirror of `PT.AddParentTree`; `PT.Size` does
      not count LK bodies, so the LK descent into the continuation decreases). */
  lemma AddParentTreeLk(tseen: LT.Tree, t: LT.Tree, res: Option<LT.Leaf>, seen: SS.SeenTrees, gm: LG.GroupMap, inp: LC.Input)
    requires PT.Size(t) < PT.Size(tseen)
    requires TreeNdLk(t, gm, inp, SS.AddSeenTrees(seen, tseen), res)
    ensures TreeNdLk(t, gm, inp, seen, res)
    decreases t
  {
    if SS.Inseen(SS.AddSeenTrees(seen, tseen), t) && res == None {
      SS.InAdd(seen, t, tseen);
    } else {
      match t
      case Mismatch =>
      case Match =>
      case Choice(t1, t2) =>
        var l1, l2 :| TreeNdLk(t1, gm, inp, SS.AddSeenTrees(seen, tseen), l1) && TreeNdLk(t2, gm, inp, SS.AddSeenTrees(seen, tseen), l2) && res == LT.Seqop(l1, l2);
        AddParentTreeLk(tseen, t1, l1, seen, gm, inp);
        AddParentTreeLk(tseen, t2, l2, seen, gm, inp);
      case Read(c, t1) =>
        AddParentTreeLk(tseen, t1, res, seen, gm, PT.NextInp(inp));
      case Progress(t1) =>
        AddParentTreeLk(tseen, t1, res, seen, gm, inp);
      case GroupActionT(a, t1) =>
        AddParentTreeLk(tseen, t1, res, seen, LG.GMUpdate(a, LC.Idx(inp), gm), inp);
      case ReadBackRef(_, _) =>
      case AnchorPass(_, t1) =>
        AddParentTreeLk(tseen, t1, res, seen, gm, inp);
      case LK(lk, tlk, t1) =>
        match LS.LkResult(lk, tlk, gm, inp) {
          case None =>
          case Some(gm1) =>
            AddParentTreeLk(tseen, t1, res, seen, gm1, inp);
        }
      case LKFail(_, _) =>
    }
  }

  // ==========================================================================
  // Establishment, preservation, and trace correctness — mirrors of
  // PT.InitPiketreeInv / PtsPreservation (+ case helpers) and
  // Correctness.TrcPikeTree / PikeTreeTrcCorrect.
  // ==========================================================================

  /** Builds a `ListNdLk` from a head `TreeNdLk` and a tail `ListNdLk`. */
  lemma ListNdLkCons(t: LT.Tree, gm: LG.GroupMap, tail: seq<(LT.Tree, LG.GroupMap)>, inp: LC.Input, seen: SS.SeenTrees, l1: Option<LT.Leaf>, l2: Option<LT.Leaf>)
    requires TreeNdLk(t, gm, inp, seen, l1)
    requires ListNdLk(tail, inp, seen, l2)
    ensures ListNdLk([(t, gm)] + tail, inp, seen, LT.Seqop(l1, l2))
  {
    assert ([(t, gm)] + tail)[0] == (t, gm);
    assert ([(t, gm)] + tail)[1..] == tail;
  }

  /** The invariant holds at the start against target `FirstLeaf(t, inp)`. */
  lemma InitPiketreeinvLk(t: LT.Tree, inp: LC.Input)
    requires PikeSubtreeLk(t)
    ensures PiketreeinvLk(PT.PikeTreeInitialState(t, inp), LT.FirstLeaf(t, inp))
  {
    var result := LT.FirstLeaf(t, inp);
    assert PikeListLk([(t, LG.Empty)]);
    forall res | StateNdLk(inp, [(t, LG.Empty)], None, [], SS.InitialSeenTrees, res)
      ensures res == result
    {
      var r2 :| ListNdLk([(t, LG.Empty)], inp, SS.InitialSeenTrees, r2)
                && res == LT.Seqop(PT.ListResult([], PT.NextInp(inp)), LT.Seqop(r2, None));
      assert PT.ListResult([], PT.NextInp(inp)) == None;
      assert PT.ListResult([], inp) == None;
      LT.SeqopNone(r2);
      assert res == r2;
      ListNdInitialLk([(t, LG.Empty)], inp, r2);
      assert [(t, LG.Empty)] + [] == [(t, LG.Empty)];
      PT.ListResultCons(t, LG.Empty, [], inp);
      LT.SeqopNone(LT.TreeRes(t, LG.Empty, inp, WP.Forward));
      assert r2 == LT.TreeRes(t, LG.Empty, inp, WP.Forward);
      assert result == LT.TreeRes(t, LG.Empty, inp, WP.Forward);
    }
  }

  /** Helper for `PtsActiveCaseLk`'s single-child branches (`Progress`,
      `GroupActionT`, `AnchorPass`, and passing `LK`): reconstructs the whole
      list's `ListNdLk` from head and tail facts. */
  lemma PtsActiveTailLk(t0: LT.Tree, tail: seq<(LT.Tree, LG.GroupMap)>, inp: LC.Input, seen: SS.SeenTrees, gm0: LG.GroupMap, l1: Option<LT.Leaf>, lrest: Option<LT.Leaf>, r2: Option<LT.Leaf>)
    requires PikeListLk(tail)
    requires TreeNdLk(t0, gm0, inp, seen, l1)
    requires ListNdLk(tail, inp, SS.AddSeenTrees(seen, t0), lrest)
    requires r2 == LT.Seqop(l1, lrest)
    ensures ListNdLk([(t0, gm0)] + tail, inp, seen, r2)
  {
    if l1.Some? {
      ListResultNdLk(tail, inp, seen);
      ListNdLkCons(t0, gm0, tail, inp, seen, l1, PT.ListResult(tail, inp));
    } else {
      ListAddSeenNdLk(tail, seen, t0, gm0, inp, lrest);
      ListNdLkCons(t0, gm0, tail, inp, seen, l1, lrest);
    }
  }

  /** `PtsActiveTailLk` specialized to a `Choice` head. */
  lemma PtsActiveTailChoiceLk(t0: LT.Tree, t1: LT.Tree, t2: LT.Tree, tail: seq<(LT.Tree, LG.GroupMap)>, inp: LC.Input, seen: SS.SeenTrees, gm0: LG.GroupMap, la: Option<LT.Leaf>, lb: Option<LT.Leaf>, lrest: Option<LT.Leaf>, r2: Option<LT.Leaf>)
    requires PikeListLk(tail) && t0 == LT.Choice(t1, t2)
    requires TreeNdLk(t0, gm0, inp, seen, LT.Seqop(la, lb))
    requires ListNdLk(tail, inp, SS.AddSeenTrees(seen, t0), lrest)
    requires r2 == LT.Seqop(LT.Seqop(la, lb), lrest)
    ensures ListNdLk([(t0, gm0)] + tail, inp, seen, r2)
  {
    var l1 := LT.Seqop(la, lb);
    if l1.Some? {
      ListResultNdLk(tail, inp, seen);
      ListNdLkCons(t0, gm0, tail, inp, seen, l1, PT.ListResult(tail, inp));
    } else {
      ListAddSeenNdLk(tail, seen, t0, gm0, inp, lrest);
      ListNdLkCons(t0, gm0, tail, inp, seen, l1, lrest);
    }
  }

  /** The `pts_active` case: the head expands via `StepActive` into `na`. */
  lemma PtsActiveCaseLk(inp: LC.Input, active: seq<(LT.Tree, LG.GroupMap)>, best: Option<LT.Leaf>, blocked: seq<(LT.Tree, LG.GroupMap)>, seen: SS.SeenTrees, t0: LT.Tree, gm0: LG.GroupMap, na: seq<(LT.Tree, LG.GroupMap)>, res: Option<LT.Leaf>)
    requires |active| > 0 && active[0] == (t0, gm0)
    requires PikeSubtreeLk(t0) && PikeListLk(active[1..]) && PikeListLk(blocked)
    requires forall r :: StateNdLk(inp, active, best, blocked, seen, r) ==> r == res
    requires TreeBfsStepLk(t0, gm0, inp) == PT.StepActive(na)
    ensures PiketreeinvLk(PT.PTS(inp, na + active[1..], best, blocked, SS.AddSeenTrees(seen, t0)), res)
  {
    assert active == [(t0, gm0)] + active[1..];
    var seen' := SS.AddSeenTrees(seen, t0);
    var tail := active[1..];
    assert PikeListLk(na + tail) by {
      assert PikeListLk(na) by {
        match t0
        case Mismatch => assert na == [];
        case Progress(t1) => assert na == [(t1, gm0)];
        case AnchorPass(_, t1) => assert na == [(t1, gm0)];
        case GroupActionT(a, t1) => assert na == [(t1, LG.GMUpdate(a, LC.Idx(inp), gm0))];
        case Choice(t1, t2) => assert na == [(t1, gm0), (t2, gm0)];
        case LK(lk, tlk, t1) =>
          match LS.LkResult(lk, tlk, gm0, inp) {
            case None => assert na == [];
            case Some(gm1) => assert na == [(t1, gm1)];
          }
        case LKFail(_, _) => assert na == [];
        case ReadBackRef(_, _) => assert false;
        case Match => assert false;
        case Read(_, _) => assert false;
      }
      PikeListLkApp(na, tail);
    }
    forall r | StateNdLk(inp, na + tail, best, blocked, seen', r) ensures r == res {
      var r2 :| ListNdLk(na + tail, inp, seen', r2)
                && r == LT.Seqop(PT.ListResult(blocked, PT.NextInp(inp)), LT.Seqop(r2, best));
      match t0
      case Mismatch =>
        assert na == [];
        assert na + tail == tail;
        ListAddSeenLk(tail, seen, t0, gm0, inp, r2);
        assert TreeNdLk(t0, gm0, inp, seen, None);
        ListNdLkCons(t0, gm0, tail, inp, seen, None, r2);
        assert StateNdLk(inp, active, best, blocked, seen, r);
      case Progress(t1) =>
        assert na == [(t1, gm0)];
        assert na + tail == [(t1, gm0)] + tail;
        var l1, lrest :| TreeNdLk(t1, gm0, inp, seen', l1) && ListNdLk(tail, inp, seen', lrest) && r2 == LT.Seqop(l1, lrest);
        AddParentTreeLk(t0, t1, l1, seen, gm0, inp);
        assert TreeNdLk(t0, gm0, inp, seen, l1);
        PtsActiveTailLk(t0, tail, inp, seen, gm0, l1, lrest, r2);
        assert StateNdLk(inp, active, best, blocked, seen, r);
      case AnchorPass(a, t1) =>
        assert na == [(t1, gm0)];
        assert na + tail == [(t1, gm0)] + tail;
        var l1, lrest :| TreeNdLk(t1, gm0, inp, seen', l1) && ListNdLk(tail, inp, seen', lrest) && r2 == LT.Seqop(l1, lrest);
        AddParentTreeLk(t0, t1, l1, seen, gm0, inp);
        assert TreeNdLk(t0, gm0, inp, seen, l1);
        PtsActiveTailLk(t0, tail, inp, seen, gm0, l1, lrest, r2);
        assert StateNdLk(inp, active, best, blocked, seen, r);
      case GroupActionT(a, t1) =>
        var gm1 := LG.GMUpdate(a, LC.Idx(inp), gm0);
        assert na == [(t1, gm1)];
        assert na + tail == [(t1, gm1)] + tail;
        var l1, lrest :| TreeNdLk(t1, gm1, inp, seen', l1) && ListNdLk(tail, inp, seen', lrest) && r2 == LT.Seqop(l1, lrest);
        AddParentTreeLk(t0, t1, l1, seen, gm1, inp);
        assert TreeNdLk(t0, gm0, inp, seen, l1);
        PtsActiveTailLk(t0, tail, inp, seen, gm0, l1, lrest, r2);
        assert StateNdLk(inp, active, best, blocked, seen, r);
      case Choice(t1, t2) =>
        assert na == [(t1, gm0), (t2, gm0)];
        assert na + tail == [(t1, gm0)] + ([(t2, gm0)] + tail);
        var la, lr1 :| TreeNdLk(t1, gm0, inp, seen', la) && ListNdLk([(t2, gm0)] + tail, inp, seen', lr1) && r2 == LT.Seqop(la, lr1);
        var lb, lrest :| TreeNdLk(t2, gm0, inp, seen', lb) && ListNdLk(tail, inp, seen', lrest) && lr1 == LT.Seqop(lb, lrest);
        AddParentTreeLk(t0, t1, la, seen, gm0, inp);
        AddParentTreeLk(t0, t2, lb, seen, gm0, inp);
        assert TreeNdLk(t0, gm0, inp, seen, LT.Seqop(la, lb));
        LT.SeqopAssoc(la, lb, lrest);
        PtsActiveTailChoiceLk(t0, t1, t2, tail, inp, seen, gm0, la, lb, lrest, r2);
        assert StateNdLk(inp, active, best, blocked, seen, r);
      case LK(lk, tlk, t1) =>
        // THE GATE: a passing gate is a zero-width gm update, exactly the
        // GroupActionT shape with gm1 := LkResult(...).value; a failed gate
        // is the Mismatch shape (TreeRes(t0) == None via TreeResLkUnfold).
        TreeResLkUnfold(lk, tlk, t1, gm0, inp);
        match LS.LkResult(lk, tlk, gm0, inp) {
          case None =>
            assert na == [];
            assert na + tail == tail;
            assert LT.TreeRes(t0, gm0, inp, WP.Forward) == None;
            ListAddSeenLk(tail, seen, t0, gm0, inp, r2);
            assert TreeNdLk(t0, gm0, inp, seen, None);
            ListNdLkCons(t0, gm0, tail, inp, seen, None, r2);
            assert StateNdLk(inp, active, best, blocked, seen, r);
          case Some(gm1) =>
            assert na == [(t1, gm1)];
            assert na + tail == [(t1, gm1)] + tail;
            var l1, lrest :| TreeNdLk(t1, gm1, inp, seen', l1) && ListNdLk(tail, inp, seen', lrest) && r2 == LT.Seqop(l1, lrest);
            AddParentTreeLk(t0, t1, l1, seen, gm1, inp);
            assert TreeNdLk(t0, gm0, inp, seen, l1);
            PtsActiveTailLk(t0, tail, inp, seen, gm0, l1, lrest, r2);
            assert StateNdLk(inp, active, best, blocked, seen, r);
        }
      case LKFail(lkf, tlkf) =>
        assert na == [];
        assert na + tail == tail;
        assert LT.TreeRes(t0, gm0, inp, WP.Forward) == None;
        ListAddSeenLk(tail, seen, t0, gm0, inp, r2);
        assert TreeNdLk(t0, gm0, inp, seen, None);
        ListNdLkCons(t0, gm0, tail, inp, seen, None, r2);
        assert StateNdLk(inp, active, best, blocked, seen, r);
      case ReadBackRef(_, _) =>
        assert false;
      case Match =>
        assert false;
      case Read(c, t1) =>
        assert false;
    }
  }

  /** The `pts_blocked` case: a `Read` head parks its continuation. */
  lemma PtsBlockedCaseLk(inp: LC.Input, active: seq<(LT.Tree, LG.GroupMap)>, best: Option<LT.Leaf>, blocked: seq<(LT.Tree, LG.GroupMap)>, seen: SS.SeenTrees, t0: LT.Tree, gm0: LG.GroupMap, newt: LT.Tree, res: Option<LT.Leaf>)
    requires |active| > 0 && active[0] == (t0, gm0)
    requires PikeSubtreeLk(t0) && PikeListLk(active[1..]) && PikeListLk(blocked)
    requires forall r :: StateNdLk(inp, active, best, blocked, seen, r) ==> r == res
    requires TreeBfsStepLk(t0, gm0, inp) == PT.StepBlocked(newt)
    ensures PiketreeinvLk(PT.PTS(inp, active[1..], best, blocked + [(newt, gm0)], SS.AddSeenTrees(seen, t0)), res)
  {
    assert t0.Read? && newt == t0.t;
    var t1 := t0.t;
    assert active == [(t0, gm0)] + active[1..];
    var tail := active[1..];
    var seen' := SS.AddSeenTrees(seen, t0);
    assert PikeSubtreeLk(t1);
    assert PikeListLk(blocked + [(t1, gm0)]) by {
      assert PikeListLk([(t1, gm0)]);
      PikeListLkApp(blocked, [(t1, gm0)]);
    }
    var B := LT.TreeRes(t1, gm0, PT.NextInp(inp), WP.Forward);
    assert LT.TreeRes(t0, gm0, inp, WP.Forward) == B;
    forall r | StateNdLk(inp, tail, best, blocked + [(newt, gm0)], seen', r) ensures r == res {
      var r2 :| ListNdLk(tail, inp, seen', r2)
                && r == LT.Seqop(PT.ListResult(blocked + [(t1, gm0)], PT.NextInp(inp)), LT.Seqop(r2, best));
      PT.ListResultApp(blocked, [(t1, gm0)], PT.NextInp(inp));
      PT.ListResultCons(t1, gm0, [], PT.NextInp(inp));
      assert [(t1, gm0)] + [] == [(t1, gm0)];
      assert PT.ListResult([], PT.NextInp(inp)) == None;
      LT.SeqopNone(B);
      assert PT.ListResult([(t1, gm0)], PT.NextInp(inp)) == B;
      assert PT.ListResult(blocked + [(t1, gm0)], PT.NextInp(inp)) == LT.Seqop(PT.ListResult(blocked, PT.NextInp(inp)), B);
      TreeResNdLk(t0, gm0, inp, seen);
      var r2old;
      if B.Some? {
        ListResultNdLk(tail, inp, seen);
        ListNdLkCons(t0, gm0, tail, inp, seen, B, PT.ListResult(tail, inp));
        r2old := LT.Seqop(B, PT.ListResult(tail, inp));
        assert r2old == B;
        assert LT.Seqop(B, LT.Seqop(r2, best)) == LT.Seqop(r2old, best);
      } else {
        ListAddSeenLk(tail, seen, t0, gm0, inp, r2);
        ListNdLkCons(t0, gm0, tail, inp, seen, B, r2);
        r2old := LT.Seqop(B, r2);
        assert r2old == r2;
        assert LT.Seqop(B, LT.Seqop(r2, best)) == LT.Seqop(r2old, best);
      }
      assert ListNdLk(active, inp, seen, r2old);
      LT.SeqopAssoc(PT.ListResult(blocked, PT.NextInp(inp)), B, LT.Seqop(r2, best));
      assert r == LT.Seqop(PT.ListResult(blocked, PT.NextInp(inp)), LT.Seqop(r2old, best));
      assert StateNdLk(inp, active, best, blocked, seen, r);
    }
  }

  /** Every `PikeTreeStepLk` preserves `PiketreeinvLk` (mirror of
      `PT.PtsPreservation`). */
  lemma PtsPreservationLk(pts1: PT.PikeTreeState, pts2: PT.PikeTreeState, res: Option<LT.Leaf>)
    requires PikeTreeStepLk(pts1, pts2)
    requires PiketreeinvLk(pts1, res)
    ensures PiketreeinvLk(pts2, res)
  {
    assert pts1.PTS?;
    var inp, active, best, blocked, seen := pts1.inp, pts1.active, pts1.best, pts1.blocked, pts1.seen;
    if |active| == 0 {
      if |blocked| == 0 {
        assert ListNdLk([], inp, seen, None);
        assert PT.ListResult([], PT.NextInp(inp)) == None;
        assert StateNdLk(inp, active, best, blocked, seen, best);
        assert best == res;
      } else {
        forall r | StateNdLk(PT.NextInp(inp), blocked, best, [], SS.InitialSeenTrees, r) ensures r == res {
          var r2 :| ListNdLk(blocked, PT.NextInp(inp), SS.InitialSeenTrees, r2)
                    && r == LT.Seqop(PT.ListResult([], PT.NextInp(PT.NextInp(inp))), LT.Seqop(r2, best));
          assert PT.ListResult([], PT.NextInp(PT.NextInp(inp))) == None;
          ListNdInitialLk(blocked, PT.NextInp(inp), r2);
          assert ListNdLk([], inp, seen, None);
          assert StateNdLk(inp, active, best, blocked, seen, r);
        }
      }
    } else {
      var t0, gm0 := active[0].0, active[0].1;
      assert active == [(t0, gm0)] + active[1..];
      PikeListLkCons(t0, gm0, active[1..]);
      if SS.Inseen(seen, t0) && pts2 == PT.PTS(inp, active[1..], best, blocked, seen) {
        forall r | StateNdLk(inp, active[1..], best, blocked, seen, r) ensures r == res {
          var r2 :| ListNdLk(active[1..], inp, seen, r2)
                    && r == LT.Seqop(PT.ListResult(blocked, PT.NextInp(inp)), LT.Seqop(r2, best));
          assert TreeNdLk(t0, gm0, inp, seen, None);
          ListNdLkCons(t0, gm0, active[1..], inp, seen, None, r2);
          assert StateNdLk(inp, active, best, blocked, seen, r);
        }
      } else {
        match TreeBfsStepLk(t0, gm0, inp) {
          case StepMatch =>
            assert t0 == LT.Match;
            assert pts2 == PT.PTS(inp, [], Some((inp, gm0)), blocked, SS.AddSeenTrees(seen, t0));
            forall r | StateNdLk(inp, [], Some((inp, gm0)), blocked, SS.AddSeenTrees(seen, t0), r) ensures r == res {
              var r2 :| ListNdLk([], inp, SS.AddSeenTrees(seen, t0), r2)
                        && r == LT.Seqop(PT.ListResult(blocked, PT.NextInp(inp)), LT.Seqop(r2, Some((inp, gm0))));
              ListResultNdLk(active[1..], inp, seen);
              assert TreeNdLk(LT.Match, gm0, inp, seen, Some((inp, gm0)));
              ListNdLkCons(t0, gm0, active[1..], inp, seen, Some((inp, gm0)), PT.ListResult(active[1..], inp));
              assert StateNdLk(inp, active, best, blocked, seen, r);
            }
          case StepActive(na) =>
            assert pts2 == PT.PTS(inp, na + active[1..], best, blocked, SS.AddSeenTrees(seen, t0));
            PtsActiveCaseLk(inp, active, best, blocked, seen, t0, gm0, na, res);
          case StepBlocked(newt) =>
            assert pts2 == PT.PTS(inp, active[1..], best, blocked + [(newt, gm0)], SS.AddSeenTrees(seen, t0));
            PtsBlockedCaseLk(inp, active, best, blocked, seen, t0, gm0, newt, res);
        }
      }
    }
  }

  /** Transitive-reflexive closure of `PikeTreeStepLk`. */
  least predicate TrcPikeTreeLk(x: PT.PikeTreeState, y: PT.PikeTreeState) {
    x == y || (exists z :: PikeTreeStepLk(x, z) && TrcPikeTreeLk(z, y))
  }

  /** `PiketreeinvLk` is preserved along a whole trace. */
  least lemma PikeTreeTrcCorrectLk(s1: PT.PikeTreeState, s2: PT.PikeTreeState, result: Option<LT.Leaf>)
    requires PiketreeinvLk(s1, result)
    requires TrcPikeTreeLk(s1, s2)
    ensures PiketreeinvLk(s2, result)
  {
    if s1 != s2 {
      var z :| PikeTreeStepLk(s1, z) && TrcPikeTreeLk(z, s2);
      PtsPreservationLk(s1, z, result);
      PikeTreeTrcCorrectLk(z, s2, result);
    }
  }

  /** THE ENDPOINT: a completed LK-aware machine trace on `t` from the initial
      state ends with `best == FirstLeaf(t, inp)` — the machine computes the
      spec tree's first-leaf answer, LK group-map merges included. */
  lemma PikeTreeLkComputesFirstLeaf(t: LT.Tree, inp: LC.Input, result: Option<LT.Leaf>)
    requires PikeSubtreeLk(t)
    requires TrcPikeTreeLk(PT.PikeTreeInitialState(t, inp), PT.PTS_final(result))
    ensures result == LT.FirstLeaf(t, inp)
  {
    InitPiketreeinvLk(t, inp);
    PikeTreeTrcCorrectLk(PT.PikeTreeInitialState(t, inp), PT.PTS_final(result), LT.FirstLeaf(t, inp));
  }
}
