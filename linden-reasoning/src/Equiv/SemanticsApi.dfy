// THE SEMANTICS FACE. Theorems stated purely against Linden's ECMAScript tree
// semantics — no RegElk, no raw_regex, no Supported fragment. They hold of ANY
// engine that conforms to the ECMAScript semantics these trees mechanize: if
// your production JavaScript engine is correct, these are facts about what
// YOUR RegExp returns. (The verified RegElk engine is one such engine; the
// bridge from these theorems to its executable Match is ApiReasoning.dfy.)
//
// Because nothing here depends on the engine-equivalence proof, the regex
// fragment is the SEMANTIC one (AltFragRe: alternation and anchors included) —
// wider than the engine's proven star fragment.
include "CaptureContent.dfy"

/** Pattern-level theorems about the ECMAScript backtracking-tree semantics
    itself: what any conforming engine's match result looks like, for a Linden
    regex `E`, on input `str` — typed captures, capture bounds, and whole-match
    content. */
module LindenSemanticsReasoning {
  import opened Std.Wrappers
  import L = Regex
  import LT = Tree
  import LS = Semantics
  import LC = Chars
  import LG = Groups
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LFU = FunctionalUtils
  import LN = WarblreNumeric
  import SS = StrictSuffix
  import CC = CaptureContent

  // ==========================================================================
  // The result, as a function. Linden's tree for E on str exists (ComputeTr)
  // and is unique (IsTreeDeterm), so "the result a conforming engine returns"
  // is well-defined without the caller ever naming a tree.
  // ==========================================================================

  /** THE backtracking tree of `E` on `str` (anchored at position 0). */
  ghost function TheTree(rer: LW.RegExpRecord, E: L.Regex, str: string): LT.Tree
    ensures LS.IsTree(rer, [LS.Areg(E)], LC.InitInput(str), LG.Empty, WP.Forward,
                      TheTree(rer, E, str))
  {
    LFU.ComputeTrIsTree(rer, [LS.Areg(E)], LC.InitInput(str), LG.Empty, WP.Forward);
    LFU.ComputeTr(rer, [LS.Areg(E)], LC.InitInput(str), LG.Empty, WP.Forward)
  }

  /** What a conforming ECMAScript engine returns for an anchored match of `E`
      on `str`: `None` (no match) or the highest-priority leaf — final input
      position + group map. */
  ghost function SemResult(rer: LW.RegExpRecord, E: L.Regex, str: string): Option<LT.Leaf> {
    LT.FirstLeaf(TheTree(rer, E, str), LC.InitInput(str))
  }

  /** Uniqueness: ANY tree derivation for `E` on `str` is `TheTree` — so facts
      about `SemResult` apply to whatever witness an engine-correctness
      argument produces, and vice versa. */
  lemma TheTreeUnique(rer: LW.RegExpRecord, E: L.Regex, str: string, t: LT.Tree)
    requires LS.IsTree(rer, [LS.Areg(E)], LC.InitInput(str), LG.Empty, WP.Forward, t)
    ensures t == TheTree(rer, E, str)
  {
    LS.IsTreeDeterm(rer, [LS.Areg(E)], LC.InitInput(str), LG.Empty, WP.Forward,
                    t, TheTree(rer, E, str));
  }

  // ==========================================================================
  // Typed captures, at the semantics level. `t` is THE backtracking tree of E
  // on str (unique by IsTreeDeterm); its first leaf is what a conforming
  // engine returns.
  // ==========================================================================

  /** Group `gid` (wrapping the P-only body `body`, located by
      `GidContainerAlt`) is, in the first leaf: unset — an untaken alternative
      — or set to an in-range span whose every character satisfies `P`. */
  lemma TypedCaptureTree(rer: LW.RegExpRecord, E: L.Regex, str: string, gid: LG.GroupId,
                         body: L.Regex, P: char -> bool, t: LT.Tree)
    requires !rer.ignoreCase
    requires CC.AltFragRe(E)
    requires CC.GidContainerAlt(E, gid, body)
    requires CC.POnly(rer, body, P)
    requires LS.IsTree(rer, [LS.Areg(E)], LC.InitInput(str), LG.Empty, WP.Forward, t)
    requires LT.FirstLeaf(t, LC.InitInput(str)).Some?
    ensures var leaf := LT.FirstLeaf(t, LC.InitInput(str)).value;
            (LG.Find(gid, leaf.1).None?
             || exists s: nat, e: nat ::
                  (LG.Find(gid, leaf.1) == Some(LG.Range(s, Some(e)))
                   && s <= e <= |str|
                   && (forall k :: s <= k < e ==> P(str[k]))))
  {
    var inp0 := LC.InitInput(str);
    CC.ReverseProps([]);
    assert LC.InputStr(inp0) == str;
    var leaf := LT.FirstLeaf(t, inp0).value;
    assert LT.TreeRes(t, LG.Empty, inp0, WP.Forward) == Some((leaf.0, leaf.1));
    assert [] + [LS.Areg(E)] + [] == [LS.Areg(E)];
    CC.RunToGroupAlt(rer, P, str, [], E, [], gid, body, inp0, LG.Empty, t, leaf.0, leaf.1);
  }

  /** The unconditional variant for the alternation-free simple fragment: the
      group is always SET (it sits on the mandatory spine), in-range, P-only. */
  lemma TypedCaptureTreeSimple(rer: LW.RegExpRecord, E: L.Regex, str: string, gid: LG.GroupId,
                               body: L.Regex, P: char -> bool, t: LT.Tree)
    requires !rer.ignoreCase
    requires CC.SimpleFragRe(E)
    requires CC.GidContainer(E, gid, body)
    requires CC.POnly(rer, body, P)
    requires LS.IsTree(rer, [LS.Areg(E)], LC.InitInput(str), LG.Empty, WP.Forward, t)
    requires LT.FirstLeaf(t, LC.InitInput(str)).Some?
    ensures var leaf := LT.FirstLeaf(t, LC.InitInput(str)).value;
            exists s: nat, e: nat ::
              (LG.Find(gid, leaf.1) == Some(LG.Range(s, Some(e)))
               && s <= e <= |str|
               && (forall k :: s <= k < e ==> P(str[k])))
  {
    var inp0 := LC.InitInput(str);
    CC.ReverseProps([]);
    assert LC.InputStr(inp0) == str;
    var leaf := LT.FirstLeaf(t, inp0).value;
    assert LT.TreeRes(t, LG.Empty, inp0, WP.Forward) == Some((leaf.0, leaf.1));
    assert [] + [LS.Areg(E)] + [] == [LS.Areg(E)];
    CC.RunToGroup(rer, P, str, [], E, [], gid, body, inp0, LG.Empty, t, leaf.0, leaf.1);
  }

  // ==========================================================================
  // Whole-match safety: the SANITIZER theorem. Linden trees are anchored — a
  // match attempt of E starts exactly at position 0 — so a successful match of
  // a P-only E means everything it consumed is P. If the leaf's end position
  // is |str| (a full-input match, one integer comparison at the use site), the
  // ENTIRE string satisfies P.
  // ==========================================================================
  /** An (anchored) match of a P-only regex consumed only P-characters:
      every character in `[0, end)` of the match satisfies `P` — so
      `end == |str|` gives whole-string safety. */
  lemma WholeTreeSafe(rer: LW.RegExpRecord, E: L.Regex, str: string, P: char -> bool, t: LT.Tree)
    requires !rer.ignoreCase
    requires CC.POnly(rer, E, P)
    requires LS.IsTree(rer, [LS.Areg(E)], LC.InitInput(str), LG.Empty, WP.Forward, t)
    requires LT.FirstLeaf(t, LC.InitInput(str)).Some?
    ensures var leaf := LT.FirstLeaf(t, LC.InitInput(str)).value;
            LC.Idx(leaf.0) <= |str|
            && (forall k :: 0 <= k < LC.Idx(leaf.0) ==> P(str[k]))
  {
    var inp0 := LC.InitInput(str);
    CC.ReverseProps([]);
    assert LC.InputStr(inp0) == str && LC.Idx(inp0) == 0;
    var leaf := LT.FirstLeaf(t, inp0).value;
    assert LT.TreeRes(t, LG.Empty, inp0, WP.Forward) == Some((leaf.0, leaf.1));
    CC.PConsume(rer, P, [LS.Areg(E)], inp0, LG.Empty, t, leaf.0, leaf.1);
  }

  // ==========================================================================
  // The same theorems, tree-free — stated directly on SemResult. These are
  // the statements to read (and to show a JavaScript audience); the tree-
  // parameter versions above serve callers who carry their own witness.
  // ==========================================================================

  /** Tree-free `TypedCaptureTree`: in any conforming engine's result, group
      `gid` is unset (an untaken alternative) or an in-range `P`-only span. */
  lemma TypedCaptureSem(rer: LW.RegExpRecord, E: L.Regex, str: string, gid: LG.GroupId,
                        body: L.Regex, P: char -> bool)
    requires !rer.ignoreCase
    requires CC.AltFragRe(E)
    requires CC.GidContainerAlt(E, gid, body)
    requires CC.POnly(rer, body, P)
    requires SemResult(rer, E, str).Some?
    ensures var leaf := SemResult(rer, E, str).value;
            (LG.Find(gid, leaf.1).None?
             || exists s: nat, e: nat ::
                  (LG.Find(gid, leaf.1) == Some(LG.Range(s, Some(e)))
                   && s <= e <= |str|
                   && (forall k :: s <= k < e ==> P(str[k]))))
  {
    TypedCaptureTree(rer, E, str, gid, body, P, TheTree(rer, E, str));
  }

  /** Tree-free `TypedCaptureTreeSimple`: alternation-free location, so the
      group is always set — in-range, `P`-only. */
  lemma TypedCaptureSemSimple(rer: LW.RegExpRecord, E: L.Regex, str: string, gid: LG.GroupId,
                              body: L.Regex, P: char -> bool)
    requires !rer.ignoreCase
    requires CC.SimpleFragRe(E)
    requires CC.GidContainer(E, gid, body)
    requires CC.POnly(rer, body, P)
    requires SemResult(rer, E, str).Some?
    ensures var leaf := SemResult(rer, E, str).value;
            exists s: nat, e: nat ::
              (LG.Find(gid, leaf.1) == Some(LG.Range(s, Some(e)))
               && s <= e <= |str|
               && (forall k :: s <= k < e ==> P(str[k])))
  {
    TypedCaptureTreeSimple(rer, E, str, gid, body, P, TheTree(rer, E, str));
  }

  /** Tree-free `WholeTreeSafe`: a successful anchored match of a `P`-only `E`
      consumed only `P`-characters — end position `== |str|` gives
      whole-string safety (the sanitizer theorem). */
  lemma WholeMatchSem(rer: LW.RegExpRecord, E: L.Regex, str: string, P: char -> bool)
    requires !rer.ignoreCase
    requires CC.POnly(rer, E, P)
    requires SemResult(rer, E, str).Some?
    ensures var leaf := SemResult(rer, E, str).value;
            LC.Idx(leaf.0) <= |str|
            && (forall k :: 0 <= k < LC.Idx(leaf.0) ==> P(str[k]))
  {
    WholeTreeSafe(rer, E, str, P, TheTree(rer, E, str));
  }

  // ==========================================================================
  // VERIFIED NEGATIVE SEARCH: None is a proof of absence. `SearchRe(G)` is the
  // unanchored-search wrapper (a lazy `.*?` prefix — exactly what the engine's
  // lazy_prefix bakes in). If ITS anchored tree has no leaf, then G's anchored
  // tree has no leaf AT ANY POSITION of the string: the pattern occurs nowhere.
  // ==========================================================================

  /** The unanchored-search form of `G`: `.*?` then `G`. */
  ghost function SearchRe(G: L.Regex): L.Regex {
    L.Sequence(L.Quantified(false, 0, LN.Inf, L.Character(LC.CdAll)), G)
  }

  /** The Linden `Input` positioned at index `i` of `str`. */
  ghost function InputAt(str: string, i: nat): LC.Input
    requires i <= |str|
  {
    LC.Input(str[i..], LC.Reverse(str[..i]))
  }

  /** THE tree of `E` on `str` anchored at position `i`, and its first leaf. */
  ghost function TheTreeAt(rer: LW.RegExpRecord, E: L.Regex, str: string, i: nat): LT.Tree
    requires i <= |str|
    ensures LS.IsTree(rer, [LS.Areg(E)], InputAt(str, i), LG.Empty, WP.Forward,
                      TheTreeAt(rer, E, str, i))
  {
    LFU.ComputeTrIsTree(rer, [LS.Areg(E)], InputAt(str, i), LG.Empty, WP.Forward);
    LFU.ComputeTr(rer, [LS.Areg(E)], InputAt(str, i), LG.Empty, WP.Forward)
  }

  /** What a conforming engine returns for `E` anchored at position `i`. */
  ghost function SemResultAt(rer: LW.RegExpRecord, E: L.Regex, str: string, i: nat): Option<LT.Leaf>
    requires i <= |str|
  {
    LT.FirstLeaf(TheTreeAt(rer, E, str, i), InputAt(str, i))
  }

  lemma ReverseSnoc(s: string, x: char)
    ensures LC.Reverse(s + [x]) == [x] + LC.Reverse(s)
    decreases |s|
  {
    if |s| == 0 {
      assert s + [x] == [x];
    } else {
      assert (s + [x])[1..] == s[1..] + [x];
      ReverseSnoc(s[1..], x);
    }
  }

  /** Advancing one character from position `i` is position `i + 1`. */
  lemma InputAtAdvance(str: string, i: nat)
    requires i < |str|
    ensures |InputAt(str, i).next| > 0
    ensures LC.AdvanceInputP(InputAt(str, i), WP.Forward) == InputAt(str, i + 1)
  {
    var inp := InputAt(str, i);
    assert inp.next[0] == str[i];
    assert inp.next[1..] == str[i+1..];
    assert str[..i+1] == str[..i] + [str[i]];
    ReverseSnoc(str[..i], str[i]);
  }

  /** `InitInput` is position 0. */
  lemma InputAtZero(str: string)
    ensures InputAt(str, 0) == LC.InitInput(str)
  {
    assert str[0..] == str && str[..0] == [];
  }

  /** THE decomposition (by induction on the remaining input): if the search
      tree from position `i` has no leaf, then `G`'s anchored tree has no leaf
      at ANY position from `i` to the end. The lazy `.*?` loop tries `G` at
      `i`, then consumes one character and repeats. */
  lemma SearchDecompose(rer: LW.RegExpRecord, G: L.Regex, str: string, i: nat, t: LT.Tree)
    requires i <= |str|
    requires LS.IsTree(rer, [LS.Areg(SearchRe(G))], InputAt(str, i), LG.Empty, WP.Forward, t)
    requires LT.TreeRes(t, LG.Empty, InputAt(str, i), WP.Forward) == None
    ensures forall j: nat :: i <= j <= |str| ==> SemResultAt(rer, G, str, j).None?
    decreases |str| - i
  {
    var inp := InputAt(str, i);
    var lazyStar := L.Quantified(false, 0, LN.Inf, L.Character(LC.CdAll));
    // tree_sequence: the same tree derives the two-action stack
    assert [LS.Areg(SearchRe(G))][1..] == [];
    assert [LS.Areg(lazyStar), LS.Areg(G)] + [] == [LS.Areg(lazyStar)] + [LS.Areg(G)];
    assert LS.IsTree(rer, [LS.Areg(lazyStar), LS.Areg(G)], inp, LG.Empty, WP.Forward, t);
    assert ([LS.Areg(lazyStar), LS.Areg(G)])[1..] == [LS.Areg(G)];
    // quantifier head: min 0, delta Inf (and Inf - 1 == Inf)
    assert LN.NoISub(LN.Inf, 1) == LN.Inf;
    match t {
      case Choice(ta, tb) => {
        // lazy (greedy == false): iterate branch is tb, skip branch is ta
        assert LT.TreeRes(ta, LG.Empty, inp, WP.Forward) == None;
        assert LT.TreeRes(tb, LG.Empty, inp, WP.Forward) == None;
        // (1) skip branch: G attempted right here at i — and it failed
        assert LS.IsTree(rer, [LS.Areg(G)], inp, LG.Empty, WP.Forward, ta);
        LS.IsTreeDeterm(rer, [LS.Areg(G)], inp, LG.Empty, WP.Forward,
                        ta, TheTreeAt(rer, G, str, i));
        assert SemResultAt(rer, G, str, i).None?;
        // (2) iterate branch: consume one char, repeat the search at i + 1
        match tb {
          case GroupActionT(g, ti) => {
            assert L.DefGroups(L.Character(LC.CdAll)) == [];
            CC.GMResetEmpty(LG.Empty);
            assert LG.GMReset([], LG.Empty) == LG.Empty;
            assert LT.TreeRes(ti, LG.Empty, inp, WP.Forward) == None;
            var iterActs := [LS.Areg(L.Character(LC.CdAll)), LS.Acheck(inp), LS.Areg(lazyStar)]
                            + [LS.Areg(G)];
            assert LS.IsTree(rer, iterActs, inp, LG.Empty, WP.Forward, ti);
            assert iterActs[0] == LS.Areg(L.Character(LC.CdAll));
            assert iterActs[1..] == [LS.Acheck(inp), LS.Areg(lazyStar), LS.Areg(G)];
            match ti {
              case Read(c, tc) => {
                // a character was available: i < |str|
                assert |inp.next| > 0;
                assert i < |str|;
                InputAtAdvance(str, i);
                var inp' := InputAt(str, i + 1);
                assert LC.AdvanceInputP(inp, WP.Forward) == inp';
                assert LT.TreeRes(tc, LG.Empty, inp', WP.Forward) == None;
                assert LS.IsTree(rer, [LS.Acheck(inp), LS.Areg(lazyStar), LS.Areg(G)],
                                 inp', LG.Empty, WP.Forward, tc);
                // the progress check passes: inp' is a strict suffix of inp
                assert SS.StrictSuffix(inp', inp, WP.Forward) by {
                  assert LC.Input(inp.next[1..], [inp.next[0]] + inp.pref) == inp';
                }
                assert ([LS.Acheck(inp), LS.Areg(lazyStar), LS.Areg(G)])[1..]
                    == [LS.Areg(lazyStar), LS.Areg(G)];
                match tc {
                  case Progress(tcc) => {
                    assert LT.TreeRes(tcc, LG.Empty, inp', WP.Forward) == None;
                    assert LS.IsTree(rer, [LS.Areg(lazyStar), LS.Areg(G)],
                                     inp', LG.Empty, WP.Forward, tcc);
                    // reassemble the Sequence head and recurse at i + 1
                    assert [LS.Areg(lazyStar), LS.Areg(G)]
                        == [LS.Areg(lazyStar)] + [LS.Areg(G)];
                    assert LS.IsTree(rer, [LS.Areg(SearchRe(G))], inp', LG.Empty, WP.Forward, tcc);
                    SearchDecompose(rer, G, str, i + 1, tcc);
                  }
                  case _ => {}
                }
              }
              case Mismatch => {
                // no character left: i == |str|, so {i} is the whole range —
                // already covered by (1)
                assert |inp.next| == |str| - i;
              }
              case _ => {}
            }
          }
          case _ => {}
        }
      }
      case _ => {}
    }
  }

  /** THE user-facing negative-search theorem: if the search form of `G` has
      no match on `str`, then `G` matches at NO position of `str` — `None` is
      a proof of absence, not a shrug. */
  lemma NoMatchAnywhereSem(rer: LW.RegExpRecord, G: L.Regex, str: string)
    requires SemResult(rer, SearchRe(G), str).None?
    ensures forall i: nat :: i <= |str| ==> SemResultAt(rer, G, str, i).None?
  {
    InputAtZero(str);
    var t := TheTree(rer, SearchRe(G), str);
    assert LS.IsTree(rer, [LS.Areg(SearchRe(G))], InputAt(str, 0), LG.Empty, WP.Forward, t);
    assert LT.TreeRes(t, LG.Empty, InputAt(str, 0), WP.Forward) == None;
    SearchDecompose(rer, G, str, 0, t);
  }
}
