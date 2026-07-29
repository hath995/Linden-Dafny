// Lookaround campaign (L1), §6.6: the ENTRY-side boolean layer with gates.
//
// The entry construction runs the boolean semantics once: MainTheorem takes the
// spec tree (`IsTree` at the empty group map), converts it to a boolean tree,
// and hands that to `ActionsTreeRepRE`, which builds the checked tree the
// simulation runs on. `BS.BoolTree` has no lookaround rule, so this file
// defines `BoolTreeLk` — the same relation widened with a gate rule — together
// with the FAITHFULNESS direction (`IsTree ==> BoolTreeLk`), which is all the
// entry needs (`BoolToIstree`, the converse, is used nowhere here).
//
// WHY A COPY RATHER THAN A WIDER `BS.BoolTree`: the rule was first added to the
// model package itself. It verified there, but `BoolTree`'s body is unfolded by
// every consumer, and linden-engine's `PikeEquiv.GenerateActiveF` sat right at
// the solver's limit — ANY extra case in the body tipped it over (measured:
// green in 4m51s before, one 300s timeout after, in three different
// formulations, including one sealed behind an opaque predicate). Keeping the
// widened relation here leaves the dependency packages bit-for-bit unchanged
// and puts the cost in the package that wants the feature.
//
// Two facts carry the gate case of the faithfulness proof:
//
//   * the rule pins the body's subtree FUNCTIONALLY, at the canonical empty
//     group map (which is what keeps the relation deterministic). The walk that
//     produced the tree carried some other map, so faithfulness needs the
//     body's tree to be group-map independent — true exactly for GROUP-FREE
//     bodies, which is the L1 fragment (`ComputeTreeGmIndep`);
//   * whether that subtree SUCCEEDS is group-map independent for free, by
//     `ResGroupMapIndep` (`TreeRes(t, ..) == None` is a property of `t`).
include "OracleSpec.dfy"

/** §6.6: `BoolTreeLk` (the boolean semantics with lookaround gates),
    `PikeLkRegex` (the pike fragment plus capture-free lookarounds), the
    group-map independence of group-free walks, and `BooleanCorrectLk` — the
    entry's `IsTree ==> BoolTreeLk` bridge. */
module LindenElkEntryLk {
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
  import CIT = ComputeIsTree
  import FU = FunctionalUtils
  import BS = BooleanSemantics
  import PS = PikeSubset
  import SSx = StrictSuffix
  import SD = LindenSpanDuality
  import R = RegElkRegex
  import T = LindenElkTranslate
  import NR = LindenElkNfaRep
  import OS = LindenElkOracleSpec

  // ===========================================================================
  // Group-map independence of group-free walks
  // ===========================================================================

  /** Every action is an `Acheck` guard or an `Areg` of a group-free regex — no
      `Aclose` (only a `Group` node pushes one), so nothing in the stack can
      read or write the group map. */
  ghost predicate GroupFreeActs(acts: LS.Actions) {
    forall i :: 0 <= i < |acts| ==>
      (acts[i].Acheck? || (acts[i].Areg? && SD.GroupFreeL(acts[i].r)))
  }

  /** `GroupFreeActs` of a cons. */
  lemma GroupFreeActsCons(x: LS.Action, cont: LS.Actions)
    ensures GroupFreeActs([x] + cont)
        <==> ((x.Acheck? || (x.Areg? && SD.GroupFreeL(x.r))) && GroupFreeActs(cont))
  {
    if (x.Acheck? || (x.Areg? && SD.GroupFreeL(x.r))) && GroupFreeActs(cont) {
      forall i | 0 <= i < |[x] + cont|
        ensures ([x] + cont)[i].Acheck? || (([x] + cont)[i].Areg? && SD.GroupFreeL(([x] + cont)[i].r))
      {
        if i == 0 {} else { assert ([x] + cont)[i] == cont[i - 1]; }
      }
    }
    if GroupFreeActs([x] + cont) {
      assert ([x] + cont)[0] == x;
      forall i | 0 <= i < |cont|
        ensures cont[i].Acheck? || (cont[i].Areg? && SD.GroupFreeL(cont[i].r))
      { assert ([x] + cont)[i + 1] == cont[i]; }
    }
  }

  /** `GroupFreeActs` of a tail. */
  lemma GroupFreeActsTail(acts: LS.Actions)
    requires |acts| > 0 && GroupFreeActs(acts)
    ensures GroupFreeActs(acts[1..])
  {
    forall i | 0 <= i < |acts[1..]|
      ensures acts[1..][i].Acheck? || (acts[1..][i].Areg? && SD.GroupFreeL(acts[1..][i].r))
    { assert acts[1..][i] == acts[i + 1]; }
  }

  /** THE independence: a group-free walk never consults the group map, so its
      tree is the same under any map. (`Quantified` resets `DefGroups(r1)`,
      which is `[]` for a group-free body, and resetting nothing is the
      identity.) */
  lemma ComputeTreeGmIndep(rer: LW.RegExpRecord, act: LS.Actions, inp: LC.Input,
                           gm1: LG.GroupMap, gm2: LG.GroupMap, dir: WP.Direction, fuel: nat)
    requires GroupFreeActs(act)
    ensures FS.ComputeTree(rer, act, inp, gm1, dir, fuel)
         == FS.ComputeTree(rer, act, inp, gm2, dir, fuel)
    decreases fuel
  {
    if fuel == 0 || |act| == 0 { return; }
    var f := fuel - 1;
    var cont := act[1..];
    GroupFreeActsTail(act);
    match act[0]
    case Acheck(strcheck) =>
      if SSx.IsStrictSuffix(inp, strcheck, dir) {
        ComputeTreeGmIndep(rer, cont, inp, gm1, gm2, dir, f);
      }
    case Aclose(gid) =>          // excluded: only a Group node pushes an Aclose
    case Areg(r) =>
      match r
      case Epsilon => ComputeTreeGmIndep(rer, cont, inp, gm1, gm2, dir, f);
      case Character(cd) =>
        match LC.ReadChar(rer, cd, inp, dir) {
          case None =>
          case Some(pair) => ComputeTreeGmIndep(rer, cont, pair.1, gm1, gm2, dir, f);
        }
      case Disjunction(r1, r2) =>
        GroupFreeActsCons(LS.Areg(r1), cont);
        GroupFreeActsCons(LS.Areg(r2), cont);
        ComputeTreeGmIndep(rer, [LS.Areg(r1)] + cont, inp, gm1, gm2, dir, f);
        ComputeTreeGmIndep(rer, [LS.Areg(r2)] + cont, inp, gm1, gm2, dir, f);
      case Sequence(r1, r2) =>
        var na := LS.SeqList(r1, r2, dir) + cont;
        assert GroupFreeActs(na) by {
          if dir.Forward? {
            assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
            GroupFreeActsCons(LS.Areg(r2), cont);
            GroupFreeActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
          } else {
            assert na == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
            GroupFreeActsCons(LS.Areg(r1), cont);
            GroupFreeActsCons(LS.Areg(r2), [LS.Areg(r1)] + cont);
          }
        }
        ComputeTreeGmIndep(rer, na, inp, gm1, gm2, dir, f);
      case Quantified(greedy, min, delta, r1) =>
        SD.GroupFreeDefGroups(r1);
        SD.GMResetNil(gm1);
        SD.GMResetNil(gm2);
        assert L.DefGroups(r1) == [];
        if min > 0 {
          var quant := L.Quantified(greedy, min - 1, delta, r1);
          var na := [LS.Areg(r1), LS.Areg(quant)] + cont;
          assert GroupFreeActs(na) by {
            assert na == [LS.Areg(r1)] + ([LS.Areg(quant)] + cont);
            GroupFreeActsCons(LS.Areg(quant), cont);
            GroupFreeActsCons(LS.Areg(r1), [LS.Areg(quant)] + cont);
          }
          ComputeTreeGmIndep(rer, na, inp, gm1, gm2, dir, f);
        } else if delta == LN.NN(0) {
          ComputeTreeGmIndep(rer, cont, inp, gm1, gm2, dir, f);
        } else {
          var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          var na := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
          assert GroupFreeActs(na) by {
            assert na == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
            GroupFreeActsCons(LS.Areg(quant), cont);
            GroupFreeActsCons(LS.Acheck(inp), [LS.Areg(quant)] + cont);
            GroupFreeActsCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
          }
          ComputeTreeGmIndep(rer, na, inp, gm1, gm2, dir, f);
          ComputeTreeGmIndep(rer, cont, inp, gm1, gm2, dir, f);
        }
      case Group(gid, r1) =>       // excluded by GroupFreeL
      case LookaroundR(lk, r1) =>  // excluded by GroupFreeL
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) {
          ComputeTreeGmIndep(rer, cont, inp, gm1, gm2, dir, f);
        }
      case Backreference(gid) =>   // excluded by GroupFreeL
  }

  /** The `ComputeTr` form of the independence. */
  lemma ComputeTrGmIndep(rer: LW.RegExpRecord, r: L.Regex, inp: LC.Input, gm: LG.GroupMap,
                         dir: WP.Direction)
    requires SD.GroupFreeL(r)
    ensures FU.ComputeTr(rer, [LS.Areg(r)], inp, gm, dir)
         == FU.ComputeTr(rer, [LS.Areg(r)], inp, LG.Empty, dir)
  {
    var acts := [LS.Areg(r)];
    assert GroupFreeActs(acts);
    var fuel := FS.ActionsFuel(acts, inp, dir) + 1;
    FS.FunctionalTerminates(rer, acts, inp, gm, dir, fuel);
    FS.FunctionalTerminates(rer, acts, inp, LG.Empty, dir, fuel);
    ComputeTreeGmIndep(rer, acts, inp, gm, LG.Empty, dir, fuel);
  }

  // ===========================================================================
  // L3a: the SAME group-map independence for LOOK-FREE (not necessarily
  // group-free) bodies. A body may CAPTURE; the tree STRUCTURE still ignores the
  // group map, because the only nodes that read it are `LookaroundR` (via
  // `LkResult`) and `Backreference` (via the captured string) -- neither present
  // in a look-free, backref-free body. `Group`/`Aclose`/`Quantified` merely
  // THREAD `GMOpen`/`GMClose`/`GMReset`, and the IH applies at whatever pair of
  // maps they produce. This is what lets the L3a captured-lookahead subtree
  // `tlk` (built at the main gm) be identified with the standalone body tree
  // (built at `Empty`).
  // ===========================================================================

  /** No `LookaroundR` and no `Backreference` anywhere -- groups ARE allowed.
      Exactly the class on which `ComputeTree`'s structure is group-map
      independent. */
  ghost predicate NoLkBrL(r: L.Regex) {
    match r
    case Epsilon => true
    case Character(_) => true
    case AnchorR(_) => true
    case Disjunction(r1, r2) => NoLkBrL(r1) && NoLkBrL(r2)
    case Sequence(r1, r2) => NoLkBrL(r1) && NoLkBrL(r2)
    case Quantified(_, _, _, r1) => NoLkBrL(r1)
    case Group(_, r1) => NoLkBrL(r1)
    case LookaroundR(_, _) => false
    case Backreference(_) => false
  }

  /** Every action is `Acheck`/`Aclose` (no regex) or `Areg` of a `NoLkBrL`
      regex -- the invariant preserved down a `ComputeTree` walk. */
  ghost predicate NoLkBrActs(acts: LS.Actions) {
    forall i :: 0 <= i < |acts| ==>
      (acts[i].Acheck? || acts[i].Aclose? || (acts[i].Areg? && NoLkBrL(acts[i].r)))
  }

  /** `NoLkBrActs` of a cons. */
  lemma NoLkBrActsCons(x: LS.Action, cont: LS.Actions)
    ensures NoLkBrActs([x] + cont)
        <==> ((x.Acheck? || x.Aclose? || (x.Areg? && NoLkBrL(x.r))) && NoLkBrActs(cont))
  {
    if (x.Acheck? || x.Aclose? || (x.Areg? && NoLkBrL(x.r))) && NoLkBrActs(cont) {
      forall i | 0 <= i < |[x] + cont|
        ensures ([x] + cont)[i].Acheck? || ([x] + cont)[i].Aclose? || (([x] + cont)[i].Areg? && NoLkBrL(([x] + cont)[i].r))
      { if i == 0 {} else { assert ([x] + cont)[i] == cont[i - 1]; } }
    }
    if NoLkBrActs([x] + cont) {
      assert ([x] + cont)[0] == x;
      forall i | 0 <= i < |cont|
        ensures cont[i].Acheck? || cont[i].Aclose? || (cont[i].Areg? && NoLkBrL(cont[i].r))
      { assert ([x] + cont)[i + 1] == cont[i]; }
    }
  }

  /** `NoLkBrActs` of a tail. */
  lemma NoLkBrActsTail(acts: LS.Actions)
    requires |acts| > 0 && NoLkBrActs(acts)
    ensures NoLkBrActs(acts[1..])
  {
    forall i | 0 <= i < |acts[1..]|
      ensures acts[1..][i].Acheck? || acts[1..][i].Aclose? || (acts[1..][i].Areg? && NoLkBrL(acts[1..][i].r))
    { assert acts[1..][i] == acts[i + 1]; }
  }

  /** The independence for `NoLkBrActs` (groups allowed): the tree is the same
      under any two group maps. */
  lemma ComputeTreeGmIndepLk(rer: LW.RegExpRecord, act: LS.Actions, inp: LC.Input,
                             gm1: LG.GroupMap, gm2: LG.GroupMap, dir: WP.Direction, fuel: nat)
    requires NoLkBrActs(act)
    ensures FS.ComputeTree(rer, act, inp, gm1, dir, fuel)
         == FS.ComputeTree(rer, act, inp, gm2, dir, fuel)
    decreases fuel
  {
    if fuel == 0 || |act| == 0 { return; }
    var f := fuel - 1;
    var cont := act[1..];
    NoLkBrActsTail(act);
    match act[0]
    case Acheck(strcheck) =>
      if SSx.IsStrictSuffix(inp, strcheck, dir) {
        ComputeTreeGmIndepLk(rer, cont, inp, gm1, gm2, dir, f);
      }
    case Aclose(gid) =>
      ComputeTreeGmIndepLk(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm1),
                           LG.GMClose(LC.Idx(inp), gid, gm2), dir, f);
    case Areg(r) =>
      match r
      case Epsilon => ComputeTreeGmIndepLk(rer, cont, inp, gm1, gm2, dir, f);
      case Character(cd) =>
        match LC.ReadChar(rer, cd, inp, dir) {
          case None =>
          case Some(pair) => ComputeTreeGmIndepLk(rer, cont, pair.1, gm1, gm2, dir, f);
        }
      case Disjunction(r1, r2) =>
        NoLkBrActsCons(LS.Areg(r1), cont);
        NoLkBrActsCons(LS.Areg(r2), cont);
        ComputeTreeGmIndepLk(rer, [LS.Areg(r1)] + cont, inp, gm1, gm2, dir, f);
        ComputeTreeGmIndepLk(rer, [LS.Areg(r2)] + cont, inp, gm1, gm2, dir, f);
      case Sequence(r1, r2) =>
        var na := LS.SeqList(r1, r2, dir) + cont;
        assert NoLkBrActs(na) by {
          if dir.Forward? {
            assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
            NoLkBrActsCons(LS.Areg(r2), cont);
            NoLkBrActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
          } else {
            assert na == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
            NoLkBrActsCons(LS.Areg(r1), cont);
            NoLkBrActsCons(LS.Areg(r2), [LS.Areg(r1)] + cont);
          }
        }
        ComputeTreeGmIndepLk(rer, na, inp, gm1, gm2, dir, f);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        if min > 0 {
          var quant := L.Quantified(greedy, min - 1, delta, r1);
          var na := [LS.Areg(r1), LS.Areg(quant)] + cont;
          assert NoLkBrActs(na) by {
            assert na == [LS.Areg(r1)] + ([LS.Areg(quant)] + cont);
            NoLkBrActsCons(LS.Areg(quant), cont);
            NoLkBrActsCons(LS.Areg(r1), [LS.Areg(quant)] + cont);
          }
          ComputeTreeGmIndepLk(rer, na, inp, LG.GMReset(gidl, gm1), LG.GMReset(gidl, gm2), dir, f);
        } else if delta == LN.NN(0) {
          ComputeTreeGmIndepLk(rer, cont, inp, gm1, gm2, dir, f);
        } else {
          var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          var na := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
          assert NoLkBrActs(na) by {
            assert na == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
            NoLkBrActsCons(LS.Areg(quant), cont);
            NoLkBrActsCons(LS.Acheck(inp), [LS.Areg(quant)] + cont);
            NoLkBrActsCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
          }
          ComputeTreeGmIndepLk(rer, na, inp, LG.GMReset(gidl, gm1), LG.GMReset(gidl, gm2), dir, f);
          ComputeTreeGmIndepLk(rer, cont, inp, gm1, gm2, dir, f);
        }
      case Group(gid, r1) =>
        var na := [LS.Areg(r1), LS.Aclose(gid)] + cont;
        assert NoLkBrActs(na) by {
          assert na == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
          NoLkBrActsCons(LS.Aclose(gid), cont);
          NoLkBrActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        }
        ComputeTreeGmIndepLk(rer, na, inp, LG.GMOpen(LC.Idx(inp), gid, gm1),
                             LG.GMOpen(LC.Idx(inp), gid, gm2), dir, f);
      case LookaroundR(lk, r1) =>   // excluded by NoLkBrL
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) {
          ComputeTreeGmIndepLk(rer, cont, inp, gm1, gm2, dir, f);
        }
      case Backreference(gid) =>    // excluded by NoLkBrL
  }

  /** The `ComputeTr` form of the look-free independence -- the tlk-identification
      workhorse: a look-free (backref-free) body's tree at the main `gm` equals
      its tree at `Empty`. */
  lemma ComputeTrGmIndepLk(rer: LW.RegExpRecord, r: L.Regex, inp: LC.Input, gm: LG.GroupMap,
                           dir: WP.Direction)
    requires NoLkBrL(r)
    ensures FU.ComputeTr(rer, [LS.Areg(r)], inp, gm, dir)
         == FU.ComputeTr(rer, [LS.Areg(r)], inp, LG.Empty, dir)
  {
    var acts := [LS.Areg(r)];
    assert NoLkBrActs(acts);
    var fuel := FS.ActionsFuel(acts, inp, dir) + 1;
    FS.FunctionalTerminates(rer, acts, inp, gm, dir, fuel);
    FS.FunctionalTerminates(rer, acts, inp, LG.Empty, dir, fuel);
    ComputeTreeGmIndepLk(rer, acts, inp, gm, LG.Empty, dir, fuel);
  }

  /** A tree with no `LK`/`LKFail` node -- the tree of a look-free regex. */
  predicate NoLKTree(t: LT.Tree) {
    match t
    case Mismatch => true
    case Match => true
    case Choice(t1, t2) => NoLKTree(t1) && NoLKTree(t2)
    case Read(_, t1) => NoLKTree(t1)
    case ReadBackRef(_, t1) => NoLKTree(t1)
    case Progress(t1) => NoLKTree(t1)
    case AnchorPass(_, t1) => NoLKTree(t1)
    case GroupActionT(_, t1) => NoLKTree(t1)
    case LK(_, _, _) => false
    case LKFail(_, _) => false
  }

  /** A `NoLkBrActs` walk builds a tree with no `LK`/`LKFail` node -- the `LK`
      node is produced only by the `LookaroundR` case, which is absent. */
  lemma ComputeTreeNoLK(rer: LW.RegExpRecord, act: LS.Actions, inp: LC.Input,
                        gm: LG.GroupMap, dir: WP.Direction, fuel: nat)
    requires NoLkBrActs(act)
    ensures FS.ComputeTree(rer, act, inp, gm, dir, fuel).Some?
         ==> NoLKTree(FS.ComputeTree(rer, act, inp, gm, dir, fuel).value)
    decreases fuel
  {
    if fuel == 0 || |act| == 0 { return; }
    var f := fuel - 1;
    var cont := act[1..];
    NoLkBrActsTail(act);
    match act[0]
    case Acheck(strcheck) =>
      if SSx.IsStrictSuffix(inp, strcheck, dir) {
        ComputeTreeNoLK(rer, cont, inp, gm, dir, f);
      }
    case Aclose(gid) =>
      ComputeTreeNoLK(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm), dir, f);
    case Areg(r) =>
      match r
      case Epsilon => ComputeTreeNoLK(rer, cont, inp, gm, dir, f);
      case Character(cd) =>
        match LC.ReadChar(rer, cd, inp, dir) {
          case None =>
          case Some(pair) => ComputeTreeNoLK(rer, cont, pair.1, gm, dir, f);
        }
      case Disjunction(r1, r2) =>
        NoLkBrActsCons(LS.Areg(r1), cont);
        NoLkBrActsCons(LS.Areg(r2), cont);
        ComputeTreeNoLK(rer, [LS.Areg(r1)] + cont, inp, gm, dir, f);
        ComputeTreeNoLK(rer, [LS.Areg(r2)] + cont, inp, gm, dir, f);
      case Sequence(r1, r2) =>
        var na := LS.SeqList(r1, r2, dir) + cont;
        assert NoLkBrActs(na) by {
          if dir.Forward? {
            assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
            NoLkBrActsCons(LS.Areg(r2), cont);
            NoLkBrActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
          } else {
            assert na == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
            NoLkBrActsCons(LS.Areg(r1), cont);
            NoLkBrActsCons(LS.Areg(r2), [LS.Areg(r1)] + cont);
          }
        }
        ComputeTreeNoLK(rer, na, inp, gm, dir, f);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        if min > 0 {
          var quant := L.Quantified(greedy, min - 1, delta, r1);
          var na := [LS.Areg(r1), LS.Areg(quant)] + cont;
          assert NoLkBrActs(na) by {
            assert na == [LS.Areg(r1)] + ([LS.Areg(quant)] + cont);
            NoLkBrActsCons(LS.Areg(quant), cont);
            NoLkBrActsCons(LS.Areg(r1), [LS.Areg(quant)] + cont);
          }
          ComputeTreeNoLK(rer, na, inp, LG.GMReset(gidl, gm), dir, f);
        } else if delta == LN.NN(0) {
          ComputeTreeNoLK(rer, cont, inp, gm, dir, f);
        } else {
          var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          var na := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
          assert NoLkBrActs(na) by {
            assert na == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
            NoLkBrActsCons(LS.Areg(quant), cont);
            NoLkBrActsCons(LS.Acheck(inp), [LS.Areg(quant)] + cont);
            NoLkBrActsCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
          }
          ComputeTreeNoLK(rer, na, inp, LG.GMReset(gidl, gm), dir, f);
          ComputeTreeNoLK(rer, cont, inp, gm, dir, f);
        }
      case Group(gid, r1) =>
        var na := [LS.Areg(r1), LS.Aclose(gid)] + cont;
        assert NoLkBrActs(na) by {
          assert na == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
          NoLkBrActsCons(LS.Aclose(gid), cont);
          NoLkBrActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        }
        ComputeTreeNoLK(rer, na, inp, LG.GMOpen(LC.Idx(inp), gid, gm), dir, f);
      case LookaroundR(lk, r1) =>   // excluded by NoLkBrL
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) {
          ComputeTreeNoLK(rer, cont, inp, gm, dir, f);
        }
      case Backreference(gid) =>    // excluded by NoLkBrL
  }

  /** The `ComputeTr` form: a look-free (backref-free) body's tree is `NoLKTree`. */
  lemma ComputeTrNoLK(rer: LW.RegExpRecord, r: L.Regex, inp: LC.Input, gm: LG.GroupMap, dir: WP.Direction)
    requires NoLkBrL(r)
    ensures NoLKTree(FU.ComputeTr(rer, [LS.Areg(r)], inp, gm, dir))
  {
    var acts := [LS.Areg(r)];
    assert NoLkBrActs(acts);
    var fuel := FS.ActionsFuel(acts, inp, dir) + 1;
    FS.FunctionalTerminates(rer, acts, inp, gm, dir, fuel);
    ComputeTreeNoLK(rer, acts, inp, gm, dir, fuel);
  }

  /** `GroupFreeL` is stronger than `NoLkBrL` (it excludes `Group`, `LookaroundR`,
      and `Backreference`). Backward-compat bridge for a future
      `PikeLkRegex(LookAhead)` widening to `NoLkBrL`: a currently-valid group-free
      lookahead body still qualifies. */
  lemma GroupFreeLNoLkBr(r: L.Regex)
    requires SD.GroupFreeL(r)
    ensures NoLkBrL(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => GroupFreeLNoLkBr(r1); GroupFreeLNoLkBr(r2);
    case Sequence(r1, r2) => GroupFreeLNoLkBr(r1); GroupFreeLNoLkBr(r2);
    case Quantified(_, _, _, r1) => GroupFreeLNoLkBr(r1);
    case _ =>
  }

  /** A look-free `R.regex` translates to a `NoLkBrL` `L.Regex`: `Translate`
      makes `LookaroundR` only from `Re_lookaround` (absent) and never makes a
      `Backreference` (no such `R.regex` constructor). */
  lemma TranslateNoLkBr(re: R.regex)
    requires T.TransWf(re) && NR.LookFreeRE(re)
    ensures NoLkBrL(T.Translate(re))
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) => TranslateNoLkBr(r1); TranslateNoLkBr(r2);
    case Re_con(r1, r2) => TranslateNoLkBr(r1); TranslateNoLkBr(r2);
    case Re_quant(_, _, _, r1) => TranslateNoLkBr(r1);
    case Re_capture(_, r1) => TranslateNoLkBr(r1);
    case Re_lookaround(_, _, _) =>   // excluded by LookFreeRE
  }

  /** Gate success is group-map independent outright (`ResGroupMapIndep`). */
  lemma LkResultGmIndep(lk: L.Lookaround, t: LT.Tree, gm: LG.GroupMap, inp: LC.Input)
    ensures LS.LkResult(lk, t, gm, inp).Some? <==> LS.LkResult(lk, t, LG.Empty, inp).Some?
  {
    if LT.TreeRes(t, gm, inp, L.LkDir(lk)) == None {
      LT.ResGroupMapIndep(t, gm, LG.Empty, inp, inp, L.LkDir(lk), L.LkDir(lk));
    }
    if LT.TreeRes(t, LG.Empty, inp, L.LkDir(lk)) == None {
      LT.ResGroupMapIndep(t, LG.Empty, gm, inp, inp, L.LkDir(lk), L.LkDir(lk));
    }
  }

  // ===========================================================================
  // The fragment: the pike subset plus capture-free lookarounds
  // ===========================================================================

  /** `PS.PikeRegex` widened with the L1 lookaround gate: a lookaround is
      admitted when its body is group-free (hence lookaround- and
      backreference-free) — exactly the image of a capture-free, look-free
      RegElk body under `Translate`. */
  ghost predicate PikeLkRegex(r: L.Regex)
    decreases r
  {
    match r
    case Epsilon => true
    case Character(_) => true
    case Disjunction(r1, r2) => PikeLkRegex(r1) && PikeLkRegex(r2)
    case Sequence(r1, r2) => PikeLkRegex(r1) && PikeLkRegex(r2)
    case Quantified(_, _, _, r1) => PikeLkRegex(r1)
    case Group(_, r1) => PikeLkRegex(r1)
    case LookaroundR(lk, r1) =>
      // L3a: a POSITIVE FORWARD lookahead admits a look-free (but possibly
      // capturing) body; every other flavour still requires a group-free body.
      if L.Positivity(lk) && L.LkDir(lk) == WP.Forward then NoLkBrL(r1)
      else SD.GroupFreeL(r1)
    case AnchorR(_) => true
    case Backreference(_) => false
  }

  /** `PS.PikeAction` for the widened fragment. */
  ghost predicate PikeLkAction(a: LS.Action) {
    match a case Areg(r) => PikeLkRegex(r) case Aclose(_) => true case Acheck(_) => true
  }

  /** `PS.PikeActions` for the widened fragment. */
  ghost predicate PikeLkActions(acts: LS.Actions) {
    forall i :: 0 <= i < |acts| ==> PikeLkAction(acts[i])
  }

  /** `PikeLkActions` of a cons. */
  lemma PikeLkActionsConsIff(x: LS.Action, cont: LS.Actions)
    ensures PikeLkActions([x] + cont) <==> (PikeLkAction(x) && PikeLkActions(cont))
  {
    if PikeLkAction(x) && PikeLkActions(cont) {
      forall i | 0 <= i < |[x] + cont| ensures PikeLkAction(([x] + cont)[i]) {
        if i == 0 {} else { assert ([x] + cont)[i] == cont[i - 1]; }
      }
    }
    if PikeLkActions([x] + cont) {
      assert ([x] + cont)[0] == x;
      forall i | 0 <= i < |cont| ensures PikeLkAction(cont[i]) { assert ([x] + cont)[i + 1] == cont[i]; }
    }
  }

  /** `PikeLkActions` of a tail. */
  lemma PikeLkActionsTail(acts: LS.Actions)
    requires |acts| > 0 && PikeLkActions(acts)
    ensures PikeLkActions(acts[1..])
  {
    forall i | 0 <= i < |acts[1..]| ensures PikeLkAction(acts[1..][i]) { assert acts[1..][i] == acts[i + 1]; }
  }

  /** The pike fragment embeds. */
  lemma PikeIsPikeLkRegex(r: L.Regex)
    requires PS.PikeRegex(r)
    ensures PikeLkRegex(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => PikeIsPikeLkRegex(r1); PikeIsPikeLkRegex(r2);
    case Sequence(r1, r2) => PikeIsPikeLkRegex(r1); PikeIsPikeLkRegex(r2);
    case Quantified(_, _, _, r1) => PikeIsPikeLkRegex(r1);
    case Group(_, r1) => PikeIsPikeLkRegex(r1);
    case _ =>
  }

  /** A lookbehind-fragment RegElk regex translates into `PikeLkRegex`. */
  lemma TranslateFragmentPikeLk(re: R.regex)
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re)
    ensures PikeLkRegex(T.Translate(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => TranslateFragmentPikeLk(r1); TranslateFragmentPikeLk(r2);
    case Re_con(r1, r2) => TranslateFragmentPikeLk(r1); TranslateFragmentPikeLk(r2);
    case Re_quant(_, _, _, r1) => TranslateFragmentPikeLk(r1);
    case Re_capture(_, r1) => TranslateFragmentPikeLk(r1);
    case Re_lookaround(lid, la, r1) =>
      // The fragment still keeps lookaround bodies capture-free, so the body's
      // translation is `GroupFreeL`; bridge to `NoLkBrL` for the widened
      // positive-forward arm of `PikeLkRegex`.
      OS.TranslateGroupFree(r1);
      GroupFreeLNoLkBr(T.Translate(r1));
    case _ =>
  }

  // ===========================================================================
  // BoolTreeLk: the boolean semantics, with gates
  // ===========================================================================

  /** The lookaround gate's payload: `tlk` is the body's tree at the canonical
      empty group map, and `ok` says whether that tree makes the lookaround
      succeed. Pinning `tlk` functionally is what keeps `BoolTreeLk`
      deterministic; the `Empty` map costs no generality because the
      faithfulness direction is used only for group-free bodies. */
  ghost predicate LkGateOk(rer: LW.RegExpRecord, lk: L.Lookaround, r1: L.Regex, inp: LC.Input,
                           tlk: LT.Tree, ok: bool)
  {
    tlk == FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk))
    && LS.LkResult(lk, tlk, LG.Empty, inp).Some? == ok
  }

  /** `BS.BoolTree` widened with the gate rule: identical on every other shape
      (this is a copy, not a refinement — see the file header for why the model
      package is left alone). */
  least predicate BoolTreeLk(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                             b: BS.LoopBool, t: LT.Tree)
  {
    if |acts| == 0 then t == LT.Match
    else
      var cont := acts[1..];
      match acts[0]
      case Acheck(strcheck) =>
        if b == BS.CanExit then
          (match t case Progress(tc) => BoolTreeLk(rer, cont, inp, BS.CanExit, tc) case _ => false)
        else
          t == LT.Mismatch
      case Aclose(gid) =>
        (match t case GroupActionT(g, tc) => g == LG.Close(gid) && BoolTreeLk(rer, cont, inp, b, tc) case _ => false)
      case Areg(r) =>
        match r
        case Epsilon => BoolTreeLk(rer, cont, inp, b, t)
        case Character(cd) =>
          (match LC.ReadChar(rer, cd, inp, WP.Forward)
           case None => t == LT.Mismatch
           case Some(pair) => (match t case Read(c, tc) => c == pair.0 && BoolTreeLk(rer, cont, pair.1, BS.CanExit, tc) case _ => false))
        case Disjunction(r1, r2) =>
          (match t case Choice(ta, tb) => BoolTreeLk(rer, [LS.Areg(r1)] + cont, inp, b, ta) && BoolTreeLk(rer, [LS.Areg(r2)] + cont, inp, b, tb) case _ => false)
        case Sequence(r1, r2) =>
          BoolTreeLk(rer, [LS.Areg(r1), LS.Areg(r2)] + cont, inp, b, t)
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 then
            (match t case GroupActionT(g, tc) => g == LG.Reset(gidl) && BoolTreeLk(rer, [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont, inp, b, tc) case _ => false)
          else if delta == LN.NN(0) then
            BoolTreeLk(rer, cont, inp, b, t)
          else
            (match t
             case Choice(ta, tb) =>
               var itert := if greedy then ta else tb;
               var skipt := if greedy then tb else ta;
               (match itert
                case GroupActionT(g, ti) =>
                  g == LG.Reset(gidl)
                  && BoolTreeLk(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, FS.NoiPred(delta), r1))] + cont, inp, BS.CannotExit, ti)
                  && BoolTreeLk(rer, cont, inp, b, skipt)
                case _ => false)
             case _ => false)
        case Group(gid, r1) =>
          (match t case GroupActionT(g, tc) => g == LG.Open(gid) && BoolTreeLk(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, b, tc) case _ => false)
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) then
            (match t case AnchorPass(a2, tc) => a2 == a && BoolTreeLk(rer, cont, inp, b, tc) case _ => false)
          else
            t == LT.Mismatch
        case LookaroundR(lk, r1) =>
          // THE GATE. Zero-width: the continuation walks from the same input
          // with the same flag; the body's tree and its verdict are pinned by
          // `LkGateOk`.
          (match t
           case LK(lk2, tlk, tc) =>
             lk2 == lk && LkGateOk(rer, lk, r1, inp, tlk, true) && BoolTreeLk(rer, cont, inp, b, tc)
           case LKFail(lk2, tlk) =>
             lk2 == lk && LkGateOk(rer, lk, r1, inp, tlk, false)
           case _ => false)
        case Backreference(_) => false
  }

  // ===========================================================================
  // Faithfulness: IsTree ==> BoolTreeLk
  // ===========================================================================

  /** `BS.ComputeBoolTree` for the widened fragment: the computed tree of a
      `PikeLkActions` stack is its `BoolTreeLk`. The gate case is where the
      group-map machinery is paid for — the walk's own map is erased in favour
      of `Empty` by `ComputeTrGmIndep` (the tree) and `LkResultGmIndep` (the
      verdict). */
  lemma ComputeBoolTreeLk(rer: LW.RegExpRecord, act: LS.Actions, inp: LC.Input, gm: LG.GroupMap,
                          b: BS.LoopBool, fuel: nat, t: LT.Tree)
    requires PikeLkActions(act)
    requires BS.BoolEncoding(b, inp, act)
    requires fuel > FS.ActionsFuel(act, inp, WP.Forward)
    requires FS.ComputeTree(rer, act, inp, gm, WP.Forward, fuel) == Some(t)
    ensures BoolTreeLk(rer, act, inp, b, t)
    decreases fuel
  {
    var f := fuel - 1;
    if |act| == 0 { return; }
    var cont := act[1..];
    PikeLkActionsTail(act);
    assert act == [act[0]] + cont;
    PikeLkActionsConsIff(act[0], cont);
    match act[0]
    case Acheck(strcheck) =>
      BS.EncodingSuffix(b, inp, act, strcheck);
      if SSx.IsStrictSuffix(inp, strcheck, WP.Forward) {
        assert SSx.StrictSuffix(inp, strcheck, WP.Forward);
        SSx.SSNeq(inp, strcheck, WP.Forward);
        BS.EncodingDifferent(b, inp, strcheck, cont);
        FS.CheckTermination(cont, inp, strcheck, WP.Forward);
        var sub := FS.ComputeTree(rer, cont, inp, gm, WP.Forward, f);
        ComputeBoolTreeLk(rer, cont, inp, gm, BS.CanExit, f, sub.value);
      } else {
        assert inp == strcheck;
        BS.EncodingSame(b, inp, cont);
      }
    case Aclose(gid) =>
      BS.EncodeClose(b, inp, cont, gid);
      var gm' := LG.GMClose(LC.Idx(inp), gid, gm);
      FS.CloseTermination(cont, inp, WP.Forward, gid);
      var sub := FS.ComputeTree(rer, cont, inp, gm', WP.Forward, f);
      ComputeBoolTreeLk(rer, cont, inp, gm', b, f, sub.value);
    case Areg(r) =>
      assert PikeLkRegex(r);
      match r
      case Epsilon =>
        BS.EncodeNext(b, inp, cont, L.Epsilon);
        FS.EpsilonTermination(cont, inp, WP.Forward);
        ComputeBoolTreeLk(rer, cont, inp, gm, b, f, t);
      case Character(cd) => {
        BS.EncodeNext(b, inp, cont, L.Character(cd));
        match LC.ReadChar(rer, cd, inp, WP.Forward) {
          case None =>
          case Some(pair) =>
            assert inp.next == [inp.next[0]] + inp.next[1..];
            assert inp == LC.Input([inp.next[0]] + inp.next[1..], inp.pref);
            assert pair.1 == LC.Input(inp.next[1..], [inp.next[0]] + inp.pref);
            BS.TrueEncoding(inp.next[1..], inp.next[0], inp.pref, cont, b);
            FS.CharacterTermination(rer, cont, inp, WP.Forward, cd, pair.0, pair.1);
            var sub := FS.ComputeTree(rer, cont, pair.1, gm, WP.Forward, f);
            ComputeBoolTreeLk(rer, cont, pair.1, gm, BS.CanExit, f, sub.value);
        }
      }
      case Disjunction(r1, r2) =>
        PikeLkActionsConsIff(LS.Areg(r1), cont);
        PikeLkActionsConsIff(LS.Areg(r2), cont);
        BS.EncodeNext(b, inp, cont, r1);
        BS.EncodeNext(b, inp, cont, r2);
        FS.DisjunctionLeftTermination(cont, inp, WP.Forward, r1, r2);
        FS.DisjunctionRightTermination(cont, inp, WP.Forward, r1, r2);
        var s1 := FS.ComputeTree(rer, [LS.Areg(r1)] + cont, inp, gm, WP.Forward, f);
        var s2 := FS.ComputeTree(rer, [LS.Areg(r2)] + cont, inp, gm, WP.Forward, f);
        ComputeBoolTreeLk(rer, [LS.Areg(r1)] + cont, inp, gm, b, f, s1.value);
        ComputeBoolTreeLk(rer, [LS.Areg(r2)] + cont, inp, gm, b, f, s2.value);
      case Sequence(r1, r2) =>
        var na := LS.SeqList(r1, r2, WP.Forward) + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        assert PikeLkActions(na) by {
          PikeLkActionsConsIff(LS.Areg(r2), cont);
          PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert BS.BoolEncoding(b, inp, na) by {
          BS.EncodeNext(b, inp, cont, r2);
          BS.EncodeNext(b, inp, [LS.Areg(r2)] + cont, r1);
        }
        FS.SequenceTermination(cont, inp, WP.Forward, r1, r2);
        var sub := FS.ComputeTree(rer, na, inp, gm, WP.Forward, f);
        ComputeBoolTreeLk(rer, na, inp, gm, b, f, sub.value);
      case Quantified(greedy, min, delta, r1) =>
        if min > 0 {
          var gidl := L.DefGroups(r1);
          var quant := L.Quantified(greedy, min - 1, delta, r1);
          var na := [LS.Areg(r1), LS.Areg(quant)] + cont;
          var gm' := LG.GMReset(gidl, gm);
          assert PikeLkActions(na) by {
            assert na == [LS.Areg(r1)] + ([LS.Areg(quant)] + cont);
            assert PikeLkRegex(quant);
            PikeLkActionsConsIff(LS.Areg(quant), cont);
            PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(quant)] + cont);
          }
          assert BS.BoolEncoding(b, inp, na) by {
            assert na == [LS.Areg(r1)] + ([LS.Areg(quant)] + cont);
            BS.EncodeNext(b, inp, cont, quant);
            BS.EncodeNext(b, inp, [LS.Areg(quant)] + cont, r1);
          }
          FS.QuantForcedTermination(cont, inp, WP.Forward, r1, min - 1, delta, greedy);
          var sub := FS.ComputeTree(rer, na, inp, gm', WP.Forward, f);
          ComputeBoolTreeLk(rer, na, inp, gm', b, f, sub.value);
          return;
        }
        if delta == LN.NN(0) {
          assert BS.BoolEncoding(b, inp, cont) by {
            BS.EncodeNext(b, inp, cont, L.Quantified(greedy, min, delta, r1));
          }
          FS.QuantDoneTermination(cont, inp, WP.Forward, r1, greedy);
          var sub := FS.ComputeTree(rer, cont, inp, gm, WP.Forward, f);
          ComputeBoolTreeLk(rer, cont, inp, gm, b, f, sub.value);
          return;
        }
        var gidl := L.DefGroups(r1);
        var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
        var na := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
        var gm' := LG.GMReset(gidl, gm);
        assert PikeLkRegex(quant);
        assert PikeLkActions(na) by {
          assert na == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
          PikeLkActionsConsIff(LS.Areg(quant), cont);
          PikeLkActionsConsIff(LS.Acheck(inp), [LS.Areg(quant)] + cont);
          PikeLkActionsConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
        }
        assert BS.BoolEncoding(b, inp, cont) by {
          BS.EncodeNext(b, inp, cont, L.Quantified(greedy, min, delta, r1));
        }
        assert BS.BoolEncoding(BS.CannotExit, inp, na) by {
          assert na == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
          BS.EncodeNext(b, inp, cont, quant);
          assert ([LS.Acheck(inp)] + ([LS.Areg(quant)] + cont))[0] == LS.Acheck(inp);
          assert ([LS.Acheck(inp)] + ([LS.Areg(quant)] + cont))[1..] == [LS.Areg(quant)] + cont;
          assert BS.BoolEncoding(BS.CannotExit, inp, [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
          BS.EncodeNext(BS.CannotExit, inp, [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont), r1);
        }
        FS.QuantFreeIterTermination(cont, inp, WP.Forward, r1, greedy, delta);
        FS.QuantFreeSkipTermination(cont, inp, WP.Forward, r1, greedy, delta);
        var siter := FS.ComputeTree(rer, na, inp, gm', WP.Forward, f);
        var sskip := FS.ComputeTree(rer, cont, inp, gm, WP.Forward, f);
        ComputeBoolTreeLk(rer, na, inp, gm', BS.CannotExit, f, siter.value);
        ComputeBoolTreeLk(rer, cont, inp, gm, b, f, sskip.value);
      case Group(gid, r1) =>
        var na := [LS.Areg(r1), LS.Aclose(gid)] + cont;
        var gm' := LG.GMOpen(LC.Idx(inp), gid, gm);
        assert PikeLkActions(na) by {
          assert na == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
          PikeLkActionsConsIff(LS.Aclose(gid), cont);
          PikeLkActionsConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        }
        assert BS.BoolEncoding(b, inp, na) by {
          assert na == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
          BS.EncodeClose(b, inp, cont, gid);
          BS.EncodeNext(b, inp, [LS.Aclose(gid)] + cont, r1);
        }
        FS.GroupTermination(cont, inp, WP.Forward, r1, gid);
        var sub := FS.ComputeTree(rer, na, inp, gm', WP.Forward, f);
        ComputeBoolTreeLk(rer, na, inp, gm', b, f, sub.value);
      case AnchorR(a) =>
        BS.EncodeNext(b, inp, cont, L.AnchorR(a));
        if LS.AnchorSatisfied(rer, a, inp) {
          FS.AnchorTermination(cont, inp, WP.Forward, a);
          var sub := FS.ComputeTree(rer, cont, inp, gm, WP.Forward, f);
          ComputeBoolTreeLk(rer, cont, inp, gm, b, f, sub.value);
        }
      case LookaroundR(lk, r1) =>
        // ComputeTree's gate case: the body's tree at the WALK's group map,
        // then the continuation under the map the gate produces. The rule
        // speaks of the canonical `Empty` map, so both halves are transported:
        // the tree by ComputeTrGmIndep (the body is group-free), the verdict by
        // LkResultGmIndep (free, for any tree).
        BS.EncodeNext(b, inp, cont, r);
        var lkacts := [LS.Areg(r1)];
        var treelkOpt := FS.ComputeTree(rer, lkacts, inp, gm, L.LkDir(lk), f);
        assert treelkOpt.Some?;                       // else ComputeTree gave None
        var tlk := treelkOpt.value;
        FS.LkLkTermination(cont, inp, WP.Forward, lk, r1);   // f exceeds the body's fuel
        assert f > FS.ActionsFuel(lkacts, inp, L.LkDir(lk));
        assert tlk == FU.ComputeTr(rer, lkacts, inp, LG.Empty, L.LkDir(lk)) by {
          FS.ComputeTreeFuelIrrelevance(rer, lkacts, inp, gm, L.LkDir(lk), f,
                                        FS.ActionsFuel(lkacts, inp, L.LkDir(lk)) + 1);
          // The body's tree is group-map independent: a positive forward
          // lookahead may capture (`NoLkBrL`), every other flavour is group-free.
          if L.Positivity(lk) && L.LkDir(lk) == WP.Forward {
            ComputeTrGmIndepLk(rer, r1, inp, gm, L.LkDir(lk));
          } else {
            ComputeTrGmIndep(rer, r1, inp, gm, L.LkDir(lk));
          }
        }
        FS.LkAfterTermination(cont, inp, WP.Forward, lk, r1);
        LkResultGmIndep(lk, tlk, gm, inp);
        match LS.LkResult(lk, tlk, gm, inp) {
          case Some(gmlk) =>
            var sub := FS.ComputeTree(rer, cont, inp, gmlk, WP.Forward, f);
            ComputeBoolTreeLk(rer, cont, inp, gmlk, b, f, sub.value);
          case None =>
        }
      case Backreference(gid) =>
  }

  /** `BS.EncodeEqual` for the widened fragment. */
  lemma EncodeEqualLk(rer: LW.RegExpRecord, inp: LC.Input, cont: LS.Actions, b: BS.LoopBool,
                      t: LT.Tree, gm: LG.GroupMap)
    requires PikeLkActions(cont)
    requires BS.BoolEncoding(b, inp, cont)
    requires LS.IsTree(rer, cont, inp, gm, WP.Forward, t)
    ensures BoolTreeLk(rer, cont, inp, b, t)
  {
    var fuel := FS.ActionsFuel(cont, inp, WP.Forward) + 1;
    FS.FunctionalTerminates(rer, cont, inp, gm, WP.Forward, fuel);
    assert fuel > FS.ActionsFuel(cont, inp, WP.Forward);
    var opt := FS.ComputeTree(rer, cont, inp, gm, WP.Forward, fuel);
    CIT.ComputeIsTreeThm(rer, cont, inp, gm, WP.Forward, fuel, opt.value);
    LS.IsTreeDeterm(rer, cont, inp, gm, WP.Forward, t, opt.value);
    ComputeBoolTreeLk(rer, cont, inp, gm, b, fuel, opt.value);
  }

  /** THE entry bridge: `BS.BooleanCorrect` for the widened fragment — a spec
      tree at the fresh initial state is the boolean tree the construction
      consumes. */
  lemma BooleanCorrectLk(rer: LW.RegExpRecord, r: L.Regex, inp: LC.Input, t: LT.Tree)
    requires PikeLkRegex(r)
    requires LS.IsTree(rer, [LS.Areg(r)], inp, LG.Empty, WP.Forward, t)
    ensures BoolTreeLk(rer, [LS.Areg(r)], inp, BS.CanExit, t)
  {
    assert PikeLkActions([LS.Areg(r)]);
    assert BS.BoolEncoding(BS.CanExit, inp, []);
    BS.EncodeNext(BS.CanExit, inp, [], r);
    assert [LS.Areg(r)] == [LS.Areg(r)] + [];
    EncodeEqualLk(rer, inp, [LS.Areg(r)], BS.CanExit, t, LG.Empty);
  }
}
