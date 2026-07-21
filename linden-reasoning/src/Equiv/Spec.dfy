// Phase 1: the specification of RegElk's matcher in terms of Linden's tree
// semantics — capture-array correspondence, MatcherSpec, its well-definedness,
// and the statement of the project's main theorem.
include "Translate.dfy"

/** THE specification module: defines `MatcherSpec`, the declarative
    characterization (in terms of Linden's `IsTree`/`FirstLeaf`) of what
    RegElk's `full_match` is supposed to compute, and states the project's
    main theorem — that RegElk's real matcher satisfies it. Everything else
    in `Equiv/` exists to prove that theorem. */
module LindenElkSpec {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LT = Tree
  import LS = Semantics
  import LFU = FunctionalUtils
  import R = RegElkRegex
  import T = LindenElkTranslate

  // ===========================================================================
  // Capture correspondence (plan finding 3)
  // ===========================================================================

  // The JS-style capture array denoted by a Linden leaf: slots 2i / 2i+1 hold
  // the start / end of group i, -1 when the group is unset. Group ids are
  // shared verbatim between RegElk (annotate, group 0 = whole match) and the
  // translated Linden regex.
  /** The JS-style capture array a Linden `Leaf` denotes: slots `2i`/`2i+1`
      hold the start/end of group `i`, `-1` when unset. This is the bridge
      between Linden's `GroupMap` and RegElk's flat integer capture array. */
  function CapArrayOfLeaf(leaf: LT.Leaf, ngroups: nat): seq<int>
    ensures |CapArrayOfLeaf(leaf, ngroups)| == 2 * ngroups
  {
    seq(2 * ngroups, j requires 0 <= j < 2 * ngroups =>
      var g: LG.GroupId := (j / 2) as nat;
      match LG.Find(g, leaf.1)
      case Some(rg) =>
        (match rg.endIdx
         case Some(e) => if j % 2 == 0 then rg.startIdx as int else e as int
         case None => -1)
      case None => -1)
  }

  // RegElk's output convention (Tests.dfy normalize_arr): a group is defined
  // iff its START slot is >= 0; a stale END slot is forced to -1.
  /** RegElk's output convention: a group is defined iff its START slot is
      `>= 0`; a stale END slot left over from a prior iteration is forced
      back to `-1`. Used to compare RegElk's raw output against `CapArrayOfLeaf`. */
  function NormalizeArr(arr: seq<int>): seq<int> {
    seq(|arr|, j requires 0 <= j < |arr| =>
      if j % 2 == 0 then arr[j]
      else if arr[j-1] < 0 then -1
      else arr[j])
  }

  /** Lifts `NormalizeArr` over an optional result (`None` on no match). */
  function Normalize(o: Option<seq<int>>): Option<seq<int>> {
    match o
    case None => None
    case Some(a) => Some(NormalizeArr(a))
  }

  // ===========================================================================
  // The spec-side regex and flag record
  // ===========================================================================

  // Number of capture groups of the annotated regex (group 0 included).
  /** Number of capture groups of the annotated regex, group 0 (the whole
      match) included. */
  function NGroups(raw: R.raw_regex): nat {
    (R.max_group(R.annotate(raw)) + 1) as nat
  }

  // The fixed flag record: RegElk has no flags, so case-sensitive, no
  // multiline, no dotAll (plan finding 4).
  /** The fixed Linden flag record RegElk is specified against: RegElk has no
      flags, so case-sensitive, non-multiline, non-dotAll, with `NGroups(raw)`
      capture groups. */
  function TheRer(raw: R.raw_regex): LW.RegExpRecord {
    LW.RER(false, false, false, NGroups(raw))
  }

  // The Linden regex whose anchored tree semantics IS RegElk's unanchored
  // leftmost search: RegElk bakes the search in at the AST level via
  // lazy_prefix (a .*? prefix) and the group-0 capture wrap in annotate
  // (plan finding 2), so the spec regex is simply the translation of
  // lazy_prefix(annotate(raw)).
  /** The Linden regex whose *anchored* tree semantics IS RegElk's
      *unanchored* leftmost search: the translation of
      `lazy_prefix(annotate(raw))`, where RegElk's own AST-level search
      wrapper and group-0 capture do the work of turning "search" into
      "anchored match". */
  function SpecRegex(raw: R.raw_regex): L.Regex
    requires T.Latin1Wf(raw)
  {
    T.AnnotateWf(raw);
    T.Translate(R.lazy_prefix(R.annotate(raw)))
  }

  // ===========================================================================
  // MatcherSpec — the declarative characterization of RegElk's full_match
  // ===========================================================================

  /** THE declarative characterization of what RegElk's `full_match` computes:
      `res` is correct for `raw` on `str` iff it is the capture array of the
      first leaf of `SpecRegex(raw)`'s (unique, by `MatcherSpecExistsUnique`)
      Linden backtracking tree. This is the specification the whole `Equiv/`
      layer proves the real engine satisfies. */
  ghost predicate MatcherSpec(raw: R.raw_regex, str: string, res: Option<seq<int>>)
    requires T.Latin1Wf(raw)
  {
    var rer := TheRer(raw);
    var inp := LC.InitInput(str);
    exists t: LT.Tree ::
      LS.IsTree(rer, [LS.Areg(SpecRegex(raw))], inp, LG.Empty, WP.Forward, t)
      && res == (match LT.FirstLeaf(t, inp)
                 case None => None
                 case Some(leaf) => Some(CapArrayOfLeaf(leaf, NGroups(raw))))
  }

  // MatcherSpec is well-defined: exactly one result satisfies it.
  // Provable today from Linden's verified artifacts alone:
  // existence via ComputeTr + ComputeTrIsTree, uniqueness via IsTreeDeterm.
  /** `MatcherSpec` is well-defined: exactly one `res` satisfies it for any
      `raw`/`str` — existence from Linden's `ComputeTr`/`ComputeTrIsTree`,
      uniqueness from `IsTreeDeterm`. Justifies treating `MatcherSpec` as a
      function rather than merely a relation. */
  lemma MatcherSpecExistsUnique(raw: R.raw_regex, str: string)
    requires T.Latin1Wf(raw)
    ensures exists res :: MatcherSpec(raw, str, res)
    ensures forall r1, r2 :: MatcherSpec(raw, str, r1) && MatcherSpec(raw, str, r2) ==> r1 == r2
  {
    var rer := TheRer(raw);
    var acts := [LS.Areg(SpecRegex(raw))];
    var inp := LC.InitInput(str);

    // existence
    LFU.ComputeTrIsTree(rer, acts, inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, acts, inp, LG.Empty, WP.Forward);
    var res := match LT.FirstLeaf(t, inp)
               case None => None
               case Some(leaf) => Some(CapArrayOfLeaf(leaf, NGroups(raw)));
    assert MatcherSpec(raw, str, res);

    // uniqueness
    forall r1, r2 | MatcherSpec(raw, str, r1) && MatcherSpec(raw, str, r2)
      ensures r1 == r2
    {
      var t1 :| LS.IsTree(rer, acts, inp, LG.Empty, WP.Forward, t1)
        && r1 == (match LT.FirstLeaf(t1, inp)
                  case None => None
                  case Some(leaf) => Some(CapArrayOfLeaf(leaf, NGroups(raw))));
      var t2 :| LS.IsTree(rer, acts, inp, LG.Empty, WP.Forward, t2)
        && r2 == (match LT.FirstLeaf(t2, inp)
                  case None => None
                  case Some(leaf) => Some(CapArrayOfLeaf(leaf, NGroups(raw))));
      LS.IsTreeDeterm(rer, acts, inp, LG.Empty, WP.Forward, t1, t2);
    }
  }

  // The executable reference result: the spec-side answer computed via
  // Linden's verified ComputeTr (exponential — test inputs only). The
  // Phase-2 differential harness compares RegElk's engines against this.
  /** The executable reference result: the `MatcherSpec`-satisfying answer
      computed directly via Linden's verified (but exponential) `ComputeTr` —
      used by the differential test harness as ground truth to compare
      RegElk's engines against on concrete test inputs. */
  function SpecResultByComputation(raw: R.raw_regex, str: string): Option<seq<int>>
    requires T.Latin1Wf(raw)
    ensures MatcherSpec(raw, str, SpecResultByComputation(raw, str))
  {
    var rer := TheRer(raw);
    var acts := [LS.Areg(SpecRegex(raw))];
    var inp := LC.InitInput(str);
    LFU.ComputeTrIsTree(rer, acts, inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, acts, inp, LG.Empty, WP.Forward);
    match LT.FirstLeaf(t, inp)
    case None => None
    case Some(leaf) => Some(CapArrayOfLeaf(leaf, NGroups(raw)))
  }

  // ===========================================================================
  // THE MAIN THEOREM (statement; proof is the work of Phases 3-8)
  // ===========================================================================
  //
  // Phase 3 defines FFullMatch, the pure functional model of RegElk's matcher,
  // and patches RegElk's `full_match` (all three register backends) with
  //   ensures res == FFullMatch(raw, str)
  // The main theorem then closes the loop to Linden's tree semantics:
  //
  //   lemma RegElkCorrect(raw: R.raw_regex, str: string)
  //     requires T.Latin1Wf(raw)
  //     ensures MatcherSpec(raw, str, Normalize(FFullMatch(raw, str)))
  //
  // yielding the verified wrapper (Phase 8):
  //
  //   method VerifiedFullMatch(raw: R.raw_regex, str: string) returns (res: Option<seq<int>>)
  //     requires T.Latin1Wf(raw)
  //     ensures MatcherSpec(raw, str, Normalize(res))
  //   { res := AI.full_match(raw, str); RegElkCorrect(raw, str); }
}
