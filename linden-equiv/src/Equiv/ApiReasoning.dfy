// The reasoning face (future linden-regex src/API/Reasoning.dfy, drafted here
// per LIBRARY_PLAN §2): the theorems a client calls to get pattern-level facts
// about Match's answer without touching the tree semantics. The ladder:
//   L1  MatchShape / MatchGroupRange / CaptureInRange — free shape & bounds
//   L2  TypedCapture — "group gid's content satisfies P", the headline; its
//       preconditions are small transparent predicates on the RAW pattern
//       (SimpleRaw / RawGidContainer / POnlyRaw) that unfold on concrete ASTs
//   L3  the transfer principle (MatchIsFirstLeaf) + Reduce.dfy's TA ladder,
//       for bespoke proofs beyond what L1/L2 state
include "ApiMatch.dfy"

/** Pattern-level theorems about `Match`'s answer: capture-array shape, per-
    group ranges, capture bounds, and the typed-capture content theorem — all
    with preconditions a client (human or AI) discharges by unfolding small
    predicates on their concrete pattern. */
module LindenRegexReasoning {
  import opened Std.Wrappers
  import LC = Chars
  import LG = Groups
  import LT = Tree
  import LS = Semantics
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LN = WarblreNumeric
  import L = Regex
  import R = RegElkRegex
  import T = LindenElkTranslate
  import LES = LindenElkSpec
  import API = LindenRegexApi
  import RD = LindenElkReduce
  import TR = LindenElkTransfer
  import CC = CaptureContent
  import SEM = LindenSemanticsReasoning

  // ==========================================================================
  // L1a — shape: the capture array always has 2 slots per group
  // ==========================================================================
  /** Every successful match yields exactly `2 * NGroups` capture slots —
      combine with `RD.NGroupsEq` (`NGroups == 1 + numCaptures`) to index
      group slots with no runtime length check. */
  lemma MatchShape(pattern: R.raw_regex, str: string)
    requires API.Supported(pattern)
    requires API.Match(pattern, str).Some?
    ensures |API.Match(pattern, str).value| == 2 * LES.NGroups(pattern)
  {
    API.MatchCorrect(pattern, str);
  }

  // ==========================================================================
  // L1b — per-group ranges: the flat array slots ARE the leaf's group map
  // ==========================================================================
  /** What slots `2i`/`2i+1` mean: exactly the tree leaf's group-map entry for
      group `i` — `Range(s, Some(e))` becomes `(s, e)`, anything else `(-1, -1)`.
      The bridge that lets a client turn group-map facts into slot facts
      without re-deriving `CapArrayOfLeaf`. */
  lemma MatchGroupRange(pattern: R.raw_regex, str: string, t: LT.Tree, i: nat)
    requires API.Supported(pattern)
    requires LS.IsTree(LES.TheRer(pattern), [LS.Areg(LES.SpecRegex(pattern))],
                       LC.InitInput(str), LG.Empty, WP.Forward, t)
    requires API.Match(pattern, str).Some?
    requires i < LES.NGroups(pattern)
    ensures var caps := API.Match(pattern, str).value;
            var lf := LT.FirstLeaf(t, LC.InitInput(str));
            |caps| == 2 * LES.NGroups(pattern)
            && lf.Some?
            && var leaf := lf.value;
            (match LG.Find(i, leaf.1)
                case Some(rg) =>
                  (match rg.endIdx
                   case Some(e) =>
                     caps[2*i] == rg.startIdx as int && caps[2*i + 1] == e as int
                   case None =>
                     caps[2*i] == -1 && caps[2*i + 1] == -1)
                case None =>
                  caps[2*i] == -1 && caps[2*i + 1] == -1)
  {
    API.MatchIsFirstLeaf(pattern, str, t);
    var leaf := LT.FirstLeaf(t, LC.InitInput(str)).value;
    var ng := LES.NGroups(pattern);
    var caps := LES.CapArrayOfLeaf(leaf, ng);
    assert (2*i) / 2 == i && (2*i + 1) / 2 == i;
    assert (2*i) % 2 == 0 && (2*i + 1) % 2 == 1;
  }

  // ==========================================================================
  // L2 — THE headline: typed captures. "Group gid of pattern p, wherever a
  // match succeeds, holds only P-characters and is in-range" — with every
  // precondition a transparent predicate on the raw pattern.
  // ==========================================================================
  /** THE typed-capture theorem. For a supported, simple pattern whose capture
      `gid` (ids counted depth-first from 1) wraps the capture-free body
      `body`, and whose body only reads `P`-characters: on every successful
      match, group `gid`'s slots are set, in-range, and its content satisfies
      `P` character-for-character. No tree, no reduction, no fuel. */
  lemma TypedCapture(pattern: R.raw_regex, str: string, gid: nat, body: R.raw_regex, P: char -> bool)
    requires API.Supported(pattern)
    requires TR.SimpleRaw(pattern)
    requires TR.RawGidContainer(pattern, 1, gid, body)
    requires TR.POnlyRaw(LES.TheRer(pattern), body, P)
    requires API.Match(pattern, str).Some?
    ensures var caps := API.Match(pattern, str).value;
            |caps| == 2 * LES.NGroups(pattern)
            && 2*gid + 1 < |caps|
            && 0 <= caps[2*gid] <= caps[2*gid + 1] <= |str|
            && (forall k :: caps[2*gid] <= k < caps[2*gid + 1] ==> P(str[k]))
  {
    var rer := LES.TheRer(pattern);
    assert !rer.ignoreCase;
    var inp0 := LC.InitInput(str);
    T.ReverseProps([]);
    assert LC.InputStr(inp0) == str;

    // the tree witness, from the API contract
    var m := API.Match(pattern, str);
    API.MatchCorrect(pattern, str);
    var spec := LES.SpecRegex(pattern);
    assert LES.MatcherSpec(pattern, str, m);
    var t :| LS.IsTree(rer, [LS.Areg(spec)], inp0, LG.Empty, WP.Forward, t)
          && m == (match LT.FirstLeaf(t, inp0)
                   case None => None
                   case Some(leaf) => Some(LES.CapArrayOfLeaf(leaf, LES.NGroups(pattern))));
    var leaf := LT.FirstLeaf(t, inp0).value;
    var ng := LES.NGroups(pattern);
    var caps := LES.CapArrayOfLeaf(leaf, ng);
    assert m.value == caps;

    // gid indexes a valid slot pair
    RD.NGroupsEq(pattern);
    TR.RawGidContainerBounds(pattern, 1, gid, body);
    assert gid < ng;

    // raw structure -> spec structure (the fuel-wall bypass)
    TR.SpecGidContainer(pattern, gid, body);
    TR.TrOfPOnly(rer, body, P);

    // run the winning path to the group and read the span off the leaf
    assert LT.TreeRes(t, LG.Empty, inp0, WP.Forward) == Some((leaf.0, leaf.1));
    assert [] + [LS.Areg(spec)] + [] == [LS.Areg(spec)];
    CC.RunToGroup(rer, P, str, [], spec, [], gid, TR.TrOf(body),
                  inp0, LG.Empty, t, leaf.0, leaf.1);
    var s: nat, e: nat :| LG.Find(gid, leaf.1) == Some(LG.Range(s, Some(e)))
               && s <= e <= |str| && (forall k :: s <= k < e ==> P(str[k]));
    assert (2*gid) / 2 == gid && (2*gid + 1) / 2 == gid;
    assert caps[2*gid] == s && caps[2*gid + 1] == e;
  }

  // ==========================================================================
  // L2b — typed captures UNDER ALTERNATION. The pattern may use `|`, and the
  // target group may sit inside one arm — at the price of a conditional
  // conclusion: an untaken arm leaves the group unset (slots == -1).
  // ==========================================================================
  /** The alternation-tolerant typed-capture theorem: if group `gid`'s slots
      are set on a successful match, they are in-range and the content is all
      `P`-characters. (They are unset exactly when the winning path took an
      alternative that does not contain the group.) */
  lemma TypedCaptureAlt(pattern: R.raw_regex, str: string, gid: nat, body: R.raw_regex, P: char -> bool)
    requires API.Supported(pattern)
    requires TR.AltRaw(pattern)
    requires TR.RawGidContainerAlt(pattern, 1, gid, body)
    requires TR.POnlyRaw(LES.TheRer(pattern), body, P)
    requires API.Match(pattern, str).Some?
    ensures var caps := API.Match(pattern, str).value;
            |caps| == 2 * LES.NGroups(pattern)
            && 2*gid + 1 < |caps|
            && (caps[2*gid] >= 0 ==>
                  0 <= caps[2*gid] <= caps[2*gid + 1] <= |str|
                  && (forall k :: caps[2*gid] <= k < caps[2*gid + 1] ==> P(str[k])))
  {
    var rer := LES.TheRer(pattern);
    assert !rer.ignoreCase;
    var inp0 := LC.InitInput(str);
    T.ReverseProps([]);
    assert LC.InputStr(inp0) == str;

    var m := API.Match(pattern, str);
    API.MatchCorrect(pattern, str);
    var spec := LES.SpecRegex(pattern);
    assert LES.MatcherSpec(pattern, str, m);
    var t :| LS.IsTree(rer, [LS.Areg(spec)], inp0, LG.Empty, WP.Forward, t)
          && m == (match LT.FirstLeaf(t, inp0)
                   case None => None
                   case Some(leaf) => Some(LES.CapArrayOfLeaf(leaf, LES.NGroups(pattern))));
    var leaf := LT.FirstLeaf(t, inp0).value;
    var ng := LES.NGroups(pattern);
    var caps := LES.CapArrayOfLeaf(leaf, ng);
    assert m.value == caps;

    RD.NGroupsEq(pattern);
    TR.RawGidContainerAltBounds(pattern, 1, gid, body);
    assert gid < ng;

    TR.SpecGidContainerAlt(pattern, gid, body);
    TR.TrOfPOnly(rer, body, P);

    assert LT.TreeRes(t, LG.Empty, inp0, WP.Forward) == Some((leaf.0, leaf.1));
    assert [] + [LS.Areg(spec)] + [] == [LS.Areg(spec)];
    CC.RunToGroupAlt(rer, P, str, [], spec, [], gid, TR.TrOf(body),
                     inp0, LG.Empty, t, leaf.0, leaf.1);
    assert (2*gid) / 2 == gid && (2*gid + 1) / 2 == gid;
    if LG.Find(gid, leaf.1).None? {
      assert caps[2*gid] == -1;
    } else {
      var s: nat, e: nat :| LG.Find(gid, leaf.1) == Some(LG.Range(s, Some(e)))
                 && s <= e <= |str| && (forall k :: s <= k < e ==> P(str[k]));
      assert caps[2*gid] == s && caps[2*gid + 1] == e;
    }
  }

  // ==========================================================================
  // L1c — bounds only: TypedCapture at the trivial predicate
  // ==========================================================================
  /** Capture bounds as a theorem, not a runtime check: group `gid`'s slots are
      set and `0 <= start <= end <= |str|` on every successful match. This is
      `TypedCapture` at `P := c => true`, so only the structural preconditions
      remain. */
  lemma CaptureInRange(pattern: R.raw_regex, str: string, gid: nat, body: R.raw_regex)
    requires API.Supported(pattern)
    requires TR.SimpleRaw(pattern)
    requires TR.RawGidContainer(pattern, 1, gid, body)
    requires API.Match(pattern, str).Some?
    ensures var caps := API.Match(pattern, str).value;
            |caps| == 2 * LES.NGroups(pattern)
            && 2*gid + 1 < |caps|
            && 0 <= caps[2*gid] <= caps[2*gid + 1] <= |str|
  {
    TR.RawGidContainerBounds(pattern, 1, gid, body);
    TR.RawGidContainerSimple(pattern, 1, gid, body);
    // Latin1Wf(body): from the container transfer's ensures
    TR.SpecGidContainer(pattern, gid, body);
    TR.POnlyRawTrue(LES.TheRer(pattern), body);
    TypedCapture(pattern, str, gid, body, c => true);
  }

  // ==========================================================================
  // L2c — WHOLE-MATCH content: the sanitizer theorem. For a capture-free,
  // P-only pattern, the whole match (group 0) has P-only content. Combined
  // with the two integer checks `caps[0] == 0 && caps[1] == |str|` at the use
  // site, this proves the ENTIRE INPUT satisfies P — allowlist validation
  // (`[a-z0-9_-]+`-style) with the safety proven, not assumed.
  // ==========================================================================
  /** On every successful match of a capture-free, `P`-only pattern, the whole
      match `[caps[0], caps[1])` is in-range and its content is all
      `P`-characters. */
  lemma WholeMatchContent(pattern: R.raw_regex, str: string, P: char -> bool)
    requires API.Supported(pattern)
    requires RD.numCaptures(pattern) == 0
    requires TR.POnlyRaw(LES.TheRer(pattern), pattern, P)
    requires API.Match(pattern, str).Some?
    ensures var caps := API.Match(pattern, str).value;
            |caps| == 2
            && 0 <= caps[0] <= caps[1] <= |str|
            && (forall k :: caps[0] <= k < caps[1] ==> P(str[k]))
  {
    var rer := LES.TheRer(pattern);
    assert !rer.ignoreCase;
    var inp0 := LC.InitInput(str);
    T.ReverseProps([]);
    assert LC.InputStr(inp0) == str;

    var m := API.Match(pattern, str);
    API.MatchCorrect(pattern, str);
    var spec := LES.SpecRegex(pattern);
    assert LES.MatcherSpec(pattern, str, m);
    var t :| LS.IsTree(rer, [LS.Areg(spec)], inp0, LG.Empty, WP.Forward, t)
          && m == (match LT.FirstLeaf(t, inp0)
                   case None => None
                   case Some(leaf) => Some(LES.CapArrayOfLeaf(leaf, LES.NGroups(pattern))));
    var leaf := LT.FirstLeaf(t, inp0).value;
    var ng := LES.NGroups(pattern);
    var caps := LES.CapArrayOfLeaf(leaf, ng);
    assert m.value == caps;
    RD.NGroupsEq(pattern);
    assert ng == 1;

    // spec == Sequence(.*?-prefix, Group(0, bodyT)); group 0 IS the container
    var bodyT := RD.TA(pattern, 1, 1, 1).0;
    RD.SpecRegexE(pattern, bodyT);
    TR.POnlyRawSpec(rer, pattern, P, 1, 1, 1);
    CC.POnlyIsSimpleFrag(rer, bodyT, P);
    RD.TA_DefGroups(pattern, 1, 1, 1, 0);   // block is [1, 1): 0 defines no group in bodyT
    var prefix := L.Quantified(false, 0, LN.Inf, L.Character(LC.CdAll));
    assert L.DefGroups(prefix) == [];
    assert 0 in L.DefGroups(L.Group(0, bodyT));
    assert CC.SimpleFragRe(prefix);
    assert CC.SimpleFragRe(L.Group(0, bodyT));
    assert CC.SimpleFragRe(spec);
    assert CC.GidContainer(spec, 0, bodyT);

    assert LT.TreeRes(t, LG.Empty, inp0, WP.Forward) == Some((leaf.0, leaf.1));
    assert [] + [LS.Areg(spec)] + [] == [LS.Areg(spec)];
    CC.RunToGroup(rer, P, str, [], spec, [], 0, bodyT, inp0, LG.Empty, t, leaf.0, leaf.1);
    var s: nat, e: nat :| LG.Find(0, leaf.1) == Some(LG.Range(s, Some(e)))
               && s <= e <= |str| && (forall k :: s <= k < e ==> P(str[k]));
    assert caps[0] == s && caps[1] == e;
  }

  // ==========================================================================
  // VERIFIED NEGATIVE SEARCH, engine face. Match is a leftmost SEARCH (the
  // engine bakes in a lazy .*? prefix), so None doesn't mean "no match at
  // position 0" — it means no match STARTING ANYWHERE. This states that as a
  // theorem: None is a proof of absence (what secret-scanning and redaction
  // tools implicitly rely on, made checkable).
  // ==========================================================================
  /** If the verified engine returns `None`, then the pattern (its translated
      body, group-0-wrapped) has no anchored match at ANY position of `str`. */
  lemma NoMatchMeansAbsent(pattern: R.raw_regex, str: string)
    requires API.Supported(pattern)
    requires API.Match(pattern, str) == None
    ensures forall i: nat :: i <= |str| ==>
              SEM.SemResultAt(LES.TheRer(pattern),
                              L.Group(0, RD.SpecBody(pattern)), str, i).None?
  {
    var rer := LES.TheRer(pattern);
    var inp0 := LC.InitInput(str);
    var G := L.Group(0, RD.SpecBody(pattern));

    // SpecRegex(pattern) IS the search form of G
    RD.SpecRegexE(pattern, RD.SpecBody(pattern));
    assert LES.SpecRegex(pattern) == SEM.SearchRe(G);

    // extract the tree witness; None means it has no leaf
    API.MatchCorrect(pattern, str);
    assert LES.MatcherSpec(pattern, str, None);
    var t :| LS.IsTree(rer, [LS.Areg(LES.SpecRegex(pattern))], inp0, LG.Empty, WP.Forward, t)
          && None == (match LT.FirstLeaf(t, inp0)
                      case None => None
                      case Some(leaf) => Some(LES.CapArrayOfLeaf(leaf, LES.NGroups(pattern))));
    assert LT.FirstLeaf(t, inp0) == None;

    // it is THE tree, so SemResult is None too; decompose
    SEM.TheTreeUnique(rer, SEM.SearchRe(G), str, t);
    assert SEM.SemResult(rer, SEM.SearchRe(G), str).None?;
    SEM.NoMatchAnywhereSem(rer, G, str);
  }

  // ==========================================================================
  // Re-export: the differential-testing bridge, so the reasoning face is one
  // import for everything a prover needs.
  // ==========================================================================
  /** `Match` equals the executable (exponential) reference semantics — thin
      re-export of `API.MatchEqualsComputedSpec` for one-import convenience. */
  lemma MatchAgreesWithComputedSpec(pattern: R.raw_regex, str: string)
    requires API.Supported(pattern)
    ensures API.Match(pattern, str) == LES.SpecResultByComputation(pattern, str)
  {
    API.MatchEqualsComputedSpec(pattern, str);
  }
}
