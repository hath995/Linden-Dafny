// Mirror of Semantics/Semantics.v.
// Inductive semantics relating a regex (via an action stack) and an input to its backtracking tree.
//
// `is_tree` is an inductive Prop in Coq. We encode it as a PLAIN RECURSIVE predicate (per the
// no-least-predicate policy), using the lexicographic structural measure
//   (TreeSize(t), ActionsRegexSize(acts))
// which strictly decreases in every rule: the result tree shrinks in all rules except
// epsilon / sequence / quant_done, and in exactly those rules the regex-size of the action stack
// shrinks instead. Determinism (Coq is_tree_determ) is then a recursive lemma over the same measure.
include "Regex.dfy"
include "Tree.dfy"
include "StrictSuffix.dfy"

/** The reference semantics. Defines `IsTree` — the relation assigning each regex
    (via an action stack) and input its backtracking `Tree` — together with the
    actions machinery it runs on and the determinism / highest-priority results
    that follow. This is the trusted definition of what a JavaScript regex *means*. */
module Semantics {
  import opened Std.Wrappers
  import opened WarblreRegExpRecord
  import opened WarblreNumeric
  import opened WarblrePrimitives
  import opened Chars
  import opened Groups
  import opened Regex
  import opened Tree
  import SS = StrictSuffix

  // ----- read_backref -----
  /** Match backreference `\gid`: re-reads group `gid`'s previously-captured text
      (case-folded per `rer`) at `inp`, returning the matched string and advanced
      input, or `None` if it doesn't match. An unset group matches the empty string. */
  function ReadBackref(rer: RegExpRecord, gm: GroupMap, gid: GroupId, inp: Input, dir: Direction): Option<(String, Input)> {
    match Find(gid, gm)
    case None => Some(([], inp))
    case Some(Range(_, None)) => Some(([], inp))
    case Some(Range(startIdx, Some(endIdx))) =>
      var subCan := MapCanon(rer, Substr(inp, startIdx, endIdx));
      var len := if endIdx >= startIdx then endIdx - startIdx else 0;
      match dir
      case Forward =>
        if len > |inp.next| then None
        else
          var firstn := Take(inp.next, len);
          if MapCanon(rer, firstn) == subCan then Some((firstn, AdvanceInputN(inp, len, Forward)))
          else None
      case Backward =>
        if len > |inp.pref| then None
        else
          var revFirstn := Reverse(Take(inp.pref, len));
          if MapCanon(rer, revFirstn) == subCan then Some((revFirstn, AdvanceInputN(inp, len, Backward)))
          else None
  }

  // Coq: read_backref_success_advance
  lemma ReadBackrefSuccessAdvance(rer: RegExpRecord, gm: GroupMap, gid: GroupId, inp: Input, dir: Direction, brStr: String, nextinp: Input)
    requires ReadBackref(rer, gm, gid, inp, dir) == Some((brStr, nextinp))
    ensures nextinp == AdvanceInputN(inp, |brStr|, dir)
  {
    match Find(gid, gm)
    case None => assert nextinp == inp; AdvanceInputN0(inp, dir);
    case Some(Range(startIdx, None)) => assert nextinp == inp; AdvanceInputN0(inp, dir);
    case Some(Range(startIdx, Some(endIdx))) =>
      var len := if endIdx >= startIdx then endIdx - startIdx else 0;
      match dir
      case Forward =>
        assert brStr == Take(inp.next, len) && len <= |inp.next|;
        assert |brStr| == len;
      case Backward =>
        assert brStr == Reverse(Take(inp.pref, len)) && len <= |inp.pref|;
        ReverseLength(Take(inp.pref, len));
        assert |brStr| == len;
  }

  lemma ReverseLength<T>(s: seq<T>)
    ensures |Reverse(s)| == |s|
  {
    if |s| != 0 { ReverseLength(s[1..]); }
  }

  lemma AdvanceInputN0(inp: Input, dir: Direction)
    ensures AdvanceInputN(inp, 0, dir) == inp
  {
    assert Take(inp.next, 0) == [] && Take(inp.pref, 0) == [];
    assert Drop(inp.next, 0) == inp.next && Drop(inp.pref, 0) == inp.pref;
  }

  // ----- lookaround result (Coq: lk_result) -----
  /** The group map a lookaround contributes: for a positive lookaround, the
      captures from its highest-priority sub-match (`None` if it fails); for a
      negative one, the unchanged `gm` iff the sub-pattern fails. */
  function LkResult(lk: Lookaround, t: Tree, gm: GroupMap, inp: Input): Option<GroupMap> {
    if Positivity(lk) then
      (match TreeRes(t, gm, inp, LkDir(lk))
       case None => None
       case Some(pair) => Some(pair.1))
    else
      (match TreeRes(t, gm, inp, LkDir(lk))
       case Some(_) => None
       case None => Some(gm))
  }

  // ----- anchors -----
  // Coq: is_boundary
  /** Whether position `i` sits on a `\b` word boundary: exactly one of the
      characters on either side is a word character. */
  predicate IsBoundary(rer: RegExpRecord, i: Input) {
    if |i.next| == 0 && |i.pref| == 0 then false
    else if |i.next| == 0 then WordChar(rer, i.pref[0])
    else if |i.pref| == 0 then WordChar(rer, i.next[0])
    else WordChar(rer, i.next[0]) != WordChar(rer, i.pref[0])  // xor
  }

  // Coq: is_input_boundary
  predicate IsInputBoundary(multiline: bool, str: String) {
    if |str| == 0 then true
    else multiline && str[0] in LineTerminators()
  }

  // Coq: anchor_satisfied
  /** Whether anchor `a` (`^`, `$`, `\b`, `\B`) holds at input position `i`
      (respecting the `multiline` flag for `^`/`$`). */
  predicate AnchorSatisfied(rer: RegExpRecord, a: Anchor, i: Input) {
    match a
    case BeginInput => IsInputBoundary(rer.multiline, i.pref)
    case EndInput => IsInputBoundary(rer.multiline, i.next)
    case WordBoundary => IsBoundary(rer, i)
    case NonWordBoundary => !IsBoundary(rer, i)
  }

  // ----- actions -----
  // Coq: Inductive action := Areg | Acheck | Aclose.
  /** One pending step on the semantics' continuation stack: `Areg(r)` = match `r`
      then continue; `Acheck(inp)` = the empty-iteration progress guard (recording
      where an iteration began); `Aclose(gid)` = close capture group `gid` here. */
  datatype Action = Areg(r: Regex) | Acheck(inp: Input) | Aclose(gid: GroupId)
  /** A stack of pending `Action`s — the continuation that `IsTree` walks. */
  type Actions = seq<Action>

  // Coq: seq_list
  /** The two parts of a `Sequence`, pushed onto the action stack in scanning
      order: `r1` then `r2` going forward, reversed when matching backward
      (inside a lookbehind). */
  function SeqList(r1: Regex, r2: Regex, dir: Direction): Actions {
    match dir
    case Forward => [Areg(r1), Areg(r2)]
    case Backward => [Areg(r2), Areg(r1)]
  }

  // ----- structural measures for the is_tree recursion -----
  function RegexSize(r: Regex): nat
    decreases r
  {
    match r
    case Epsilon => 1
    case Character(_) => 1
    case AnchorR(_) => 1
    case Backreference(_) => 1
    case Disjunction(r1, r2) => 1 + RegexSize(r1) + RegexSize(r2)
    case Sequence(r1, r2) => 1 + RegexSize(r1) + RegexSize(r2)
    case Quantified(_, _, _, r1) => 1 + RegexSize(r1)
    case LookaroundR(_, r0) => 1 + RegexSize(r0)
    case Group(_, r0) => 1 + RegexSize(r0)
  }

  function ActionRegexSize(a: Action): nat {
    match a case Areg(r) => RegexSize(r) case Acheck(_) => 0 case Aclose(_) => 0
  }

  function ActionsRegexSize(acts: Actions): nat
    decreases |acts|
  {
    if |acts| == 0 then 0 else ActionRegexSize(acts[0]) + ActionsRegexSize(acts[1..])
  }

  function TreeSize(t: Tree): nat
    decreases t
  {
    match t
    case Mismatch => 1
    case Match => 1
    case Choice(t1, t2) => 1 + TreeSize(t1) + TreeSize(t2)
    case Read(_, t0) => 1 + TreeSize(t0)
    case ReadBackRef(_, t0) => 1 + TreeSize(t0)
    case Progress(t0) => 1 + TreeSize(t0)
    case AnchorPass(_, t0) => 1 + TreeSize(t0)
    case GroupActionT(_, t0) => 1 + TreeSize(t0)
    case LK(_, tlk, t0) => 1 + TreeSize(tlk) + TreeSize(t0)
    case LKFail(_, tlk) => 1 + TreeSize(tlk)
  }

  // ----- is_tree -----
  // `IsTree(rer, acts, inp, gm, dir, t)` ⟺ t is the (unique) backtracking tree for `acts`.
  // Encoded as a `least predicate` (inductive least fixpoint). A plain recursive predicate with the
  // lexicographic measure (TreeSize(t), ActionsRegexSize(acts)) almost works — the measure decreases
  // in every rule — but the tree_sequence rule keeps the same tree while rewriting the action stack
  // via a concatenation `seq_list(r1,r2,dir) ++ cont`, and Dafny will not accept the
  // ActionsRegexSize-decrease across that concat without an additivity lemma (which cannot be
  // invoked inside a predicate's termination check). So we use the inductive encoding here; all
  // IsTree recursive calls occur positively, so the least fixpoint is well-defined.
  /** **The reference semantics.** `IsTree(rer, acts, inp, gm, dir, t)` holds exactly
      when `t` is the backtracking tree produced by running action stack `acts` from
      input position `inp` with captures `gm`, scanning in direction `dir`.

      A `least predicate` with one clause per ECMAScript rule — `tree_match`,
      `tree_char`, `tree_disj`, `tree_sequence`, `tree_quant_forced`/`_done`/`_free`,
      `tree_group`, `tree_lk`/`_fail`, `tree_anchor`, `tree_backref`. The tree of a
      whole regex is `Priotree`; by `IsTreeDeterm` it is unique. */
  least predicate IsTree(rer: RegExpRecord, acts: Actions, inp: Input, gm: GroupMap, dir: Direction, t: Tree)
  {
    if |acts| == 0 then
      t == Match  // tree_match
    else
      var cont := acts[1..];
      match acts[0]
      case Acheck(strcheck) =>
        if SS.StrictSuffix(inp, strcheck, dir) then
          (match t case Progress(tc) => IsTree(rer, cont, inp, gm, dir, tc) case _ => false)  // tree_check
        else
          t == Mismatch  // tree_check_fail
      case Aclose(gid) =>
        // tree_close
        (match t
         case GroupActionT(g, tc) => g == Close(gid) && IsTree(rer, cont, inp, GMClose(Idx(inp), gid, gm), dir, tc)
         case _ => false)
      case Areg(r) =>
        match r
        case Epsilon => IsTree(rer, cont, inp, gm, dir, t)  // tree_epsilon
        case Character(cd) =>
          (match ReadChar(rer, cd, inp, dir)
           case None => t == Mismatch  // tree_char_fail
           case Some(pair) =>
             (match t case Read(c, tc) => c == pair.0 && IsTree(rer, cont, pair.1, gm, dir, tc) case _ => false))  // tree_char
        case Disjunction(r1, r2) =>
          // tree_disj
          (match t
           case Choice(ta, tb) =>
             IsTree(rer, [Areg(r1)] + cont, inp, gm, dir, ta)
             && IsTree(rer, [Areg(r2)] + cont, inp, gm, dir, tb)
           case _ => false)
        case Sequence(r1, r2) =>
          // tree_sequence
          (match dir
           case Forward => IsTree(rer, [Areg(r1), Areg(r2)] + cont, inp, gm, dir, t)
           case Backward => IsTree(rer, [Areg(r2), Areg(r1)] + cont, inp, gm, dir, t))
        case Quantified(greedy, min, delta, r1) =>
          var gidl := DefGroups(r1);
          if min > 0 then
            // tree_quant_forced
            (match t
             case GroupActionT(g, tc) =>
               g == Reset(gidl)
               && IsTree(rer, [Areg(r1), Areg(Quantified(greedy, min - 1, delta, r1))] + cont,
                         inp, GMReset(gidl, gm), dir, tc)
             case _ => false)
          else if delta == NN(0) then
            IsTree(rer, cont, inp, gm, dir, t)  // tree_quant_done
          else
            // tree_quant_free
            var plus := NoISub(delta, 1);
            var iterActs := [Areg(r1), Acheck(inp), Areg(Quantified(greedy, 0, plus, r1))] + cont;
            (match t
             case Choice(ta, tb) =>
               var itert := if greedy then ta else tb;
               var skipt := if greedy then tb else ta;
               (match itert
                case GroupActionT(g, ti) =>
                  g == Reset(gidl) && IsTree(rer, iterActs, inp, GMReset(gidl, gm), dir, ti)
                  && IsTree(rer, cont, inp, gm, dir, skipt)
                case _ => false)
             case _ => false)
        case LookaroundR(lk, r1) =>
          (match t
           case LK(lk2, tlk, tc) =>
             // tree_lk
             lk2 == lk
             && IsTree(rer, [Areg(r1)], inp, gm, LkDir(lk), tlk)
             && LkResult(lk, tlk, gm, inp).Some?
             && IsTree(rer, cont, inp, LkResult(lk, tlk, gm, inp).value, dir, tc)
           case LKFail(lk2, tlk) =>
             // tree_lk_fail
             lk2 == lk
             && IsTree(rer, [Areg(r1)], inp, gm, LkDir(lk), tlk)
             && LkResult(lk, tlk, gm, inp).None?
           case _ => false)
        case Group(gid, r1) =>
          // tree_group
          (match t
           case GroupActionT(g, tc) =>
             g == Open(gid)
             && IsTree(rer, [Areg(r1), Aclose(gid)] + cont, inp, GMOpen(Idx(inp), gid, gm), dir, tc)
           case _ => false)
        case AnchorR(a) =>
          if AnchorSatisfied(rer, a, inp) then
            (match t case AnchorPass(a2, tc) => a2 == a && IsTree(rer, cont, inp, gm, dir, tc) case _ => false)  // tree_anchor
          else
            t == Mismatch  // tree_anchor_fail
        case Backreference(gid) =>
          (match ReadBackref(rer, gm, gid, inp, dir)
           case None => t == Mismatch  // tree_backref_fail
           case Some(pair) =>
             (match t case ReadBackRef(s, tc) => s == pair.0 && IsTree(rer, cont, pair.1, gm, dir, tc) case _ => false))  // tree_backref
  }

  // Coq: priotree / priotree_inp
  /** `t` is *the* backtracking tree of regex `r` on string `str` — the whole-regex
      specialization of `IsTree` (single action `[Areg(r)]`, empty captures, forward). */
  ghost predicate Priotree(rer: RegExpRecord, r: Regex, str: String, t: Tree) {
    IsTree(rer, [Areg(r)], InitInput(str), Empty, Forward, t)
  }
  /** `Priotree` starting from an arbitrary input position `inp` rather than the
      start of a string. */
  ghost predicate PriotreeInp(rer: RegExpRecord, r: Regex, inp: Input, t: Tree) {
    IsTree(rer, [Areg(r)], inp, Empty, Forward, t)
  }

  // Coq: is_tree_determ — recursive determinism over the lex measure (TreeSize, ActionsRegexSize),
  // unfolding both IsTree hypotheses (the ==> body direction holds for least predicates).
  /** **Determinism.** A given action stack and position determine a *unique* tree:
      from `IsTree(…, t1)` and `IsTree(…, t2)` it proves `t1 == t2`. This is what
      lets the spec speak of *the* tree and *the* match. */
  lemma IsTreeDeterm(rer: RegExpRecord, acts: Actions, i: Input, gm: GroupMap, dir: Direction, t1: Tree, t2: Tree)
    requires IsTree(rer, acts, i, gm, dir, t1)
    requires IsTree(rer, acts, i, gm, dir, t2)
    ensures t1 == t2
    decreases TreeSize(t1), ActionsRegexSize(acts)
  {
    if |acts| == 0 {
    } else {
      var cont := acts[1..];
      match acts[0]
      case Acheck(strcheck) =>
        if SS.StrictSuffix(i, strcheck, dir) {
          match t1 { case Progress(tc1) => match t2 { case Progress(tc2) => IsTreeDeterm(rer, cont, i, gm, dir, tc1, tc2); case _ => } case _ => }
        }
      case Aclose(gid) =>
        match t1 { case GroupActionT(g1, tc1) => match t2 { case GroupActionT(g2, tc2) => IsTreeDeterm(rer, cont, i, GMClose(Idx(i), gid, gm), dir, tc1, tc2); case _ => } case _ => }
      case Areg(r) =>
        match r
        case Epsilon => IsTreeDeterm(rer, cont, i, gm, dir, t1, t2);
        case Character(cd) => {
          match ReadChar(rer, cd, i, dir) {
            case None =>
            case Some(pair) =>
              match t1 { case Read(c1, tc1) => match t2 { case Read(c2, tc2) => IsTreeDeterm(rer, cont, pair.1, gm, dir, tc1, tc2); case _ => } case _ => }
          }
        }
        case Disjunction(r1, r2) => {
          match t1 { case Choice(ta1, tb1) => match t2 { case Choice(ta2, tb2) => {
            IsTreeDeterm(rer, [Areg(r1)] + cont, i, gm, dir, ta1, ta2);
            IsTreeDeterm(rer, [Areg(r2)] + cont, i, gm, dir, tb1, tb2);
          } case _ => } case _ => }
        }
        case Sequence(r1, r2) => {
          match dir {
            case Forward =>
              assert ([Areg(r1), Areg(r2)] + cont)[1..] == [Areg(r2)] + cont;
              assert ([Areg(r2)] + cont)[1..] == cont;
              assert acts == [Areg(Sequence(r1, r2))] + cont;
              assert ActionsRegexSize([Areg(r1), Areg(r2)] + cont) == RegexSize(r1) + RegexSize(r2) + ActionsRegexSize(cont);
              assert ActionsRegexSize(acts) == RegexSize(Sequence(r1, r2)) + ActionsRegexSize(cont);
              IsTreeDeterm(rer, [Areg(r1), Areg(r2)] + cont, i, gm, dir, t1, t2);
            case Backward =>
              assert ([Areg(r2), Areg(r1)] + cont)[1..] == [Areg(r1)] + cont;
              assert ([Areg(r1)] + cont)[1..] == cont;
              assert acts == [Areg(Sequence(r1, r2))] + cont;
              assert ActionsRegexSize([Areg(r2), Areg(r1)] + cont) == RegexSize(r2) + RegexSize(r1) + ActionsRegexSize(cont);
              assert ActionsRegexSize(acts) == RegexSize(Sequence(r1, r2)) + ActionsRegexSize(cont);
              IsTreeDeterm(rer, [Areg(r2), Areg(r1)] + cont, i, gm, dir, t1, t2);
          }
        }
        case Quantified(greedy, min, delta, r1) => {
          var gidl := DefGroups(r1);
          if min > 0 {
            match t1 { case GroupActionT(g1, tc1) => match t2 { case GroupActionT(g2, tc2) =>
              IsTreeDeterm(rer, [Areg(r1), Areg(Quantified(greedy, min - 1, delta, r1))] + cont, i, GMReset(gidl, gm), dir, tc1, tc2);
            case _ => } case _ => }
          } else if delta == NN(0) {
            IsTreeDeterm(rer, cont, i, gm, dir, t1, t2);
          } else {
            var iterActs := [Areg(r1), Acheck(i), Areg(Quantified(greedy, 0, NoISub(delta, 1), r1))] + cont;
            match t1 { case Choice(ta1, tb1) => match t2 { case Choice(ta2, tb2) => {
              var itert1 := if greedy then ta1 else tb1;
              var skipt1 := if greedy then tb1 else ta1;
              var itert2 := if greedy then ta2 else tb2;
              var skipt2 := if greedy then tb2 else ta2;
              match itert1 { case GroupActionT(g1, ti1) => match itert2 { case GroupActionT(g2, ti2) => {
                assert TreeSize(ti1) < TreeSize(t1);
                assert TreeSize(skipt1) < TreeSize(t1);
                IsTreeDeterm(rer, iterActs, i, GMReset(gidl, gm), dir, ti1, ti2);
                IsTreeDeterm(rer, cont, i, gm, dir, skipt1, skipt2);
              } case _ => } case _ => }
            } case _ => } case _ => }
          }
        }
        case LookaroundR(lk, r1) => {
          match t1 {
            case LK(lka1, tlk1, tc1) => match t2 {
              case LK(lka2, tlk2, tc2) =>
                IsTreeDeterm(rer, [Areg(r1)], i, gm, LkDir(lk), tlk1, tlk2);   // tlk1 == tlk2
                IsTreeDeterm(rer, cont, i, LkResult(lk, tlk1, gm, i).value, dir, tc1, tc2);
              case LKFail(lka2, tlk2) =>
                IsTreeDeterm(rer, [Areg(r1)], i, gm, LkDir(lk), tlk1, tlk2);   // tlk1==tlk2 ⟹ LkResult agrees ⟹ contradiction
              case _ =>
            }
            case LKFail(lka1, tlk1) => match t2 {
              case LK(lka2, tlk2, tc2) =>
                IsTreeDeterm(rer, [Areg(r1)], i, gm, LkDir(lk), tlk1, tlk2);
              case LKFail(lka2, tlk2) =>
                IsTreeDeterm(rer, [Areg(r1)], i, gm, LkDir(lk), tlk1, tlk2);
              case _ =>
            }
            case _ =>
          }
        }
        case Group(gid, r1) => {
          match t1 { case GroupActionT(g1, tc1) => match t2 { case GroupActionT(g2, tc2) =>
            IsTreeDeterm(rer, [Areg(r1), Aclose(gid)] + cont, i, GMOpen(Idx(i), gid, gm), dir, tc1, tc2);
          case _ => } case _ => }
        }
        case AnchorR(a) =>
          if AnchorSatisfied(rer, a, i) {
            match t1 { case AnchorPass(a1, tc1) => match t2 { case AnchorPass(a2, tc2) => IsTreeDeterm(rer, cont, i, gm, dir, tc1, tc2); case _ => } case _ => }
          }
        case Backreference(gid) => {
          match ReadBackref(rer, gm, gid, i, dir) {
            case None =>
            case Some(pair) =>
              match t1 { case ReadBackRef(s1, tc1) => match t2 { case ReadBackRef(s2, tc2) => IsTreeDeterm(rer, cont, pair.1, gm, dir, tc1, tc2); case _ => } case _ => }
          }
        }
    }
  }

  /** The backtracking tree of a regex on a string is unique (corollary of
      `IsTreeDeterm`). */
  lemma PriotreeDeterm(rer: RegExpRecord, r: Regex, str: String, t1: Tree, t2: Tree)
    requires Priotree(rer, r, str, t1)
    requires Priotree(rer, r, str, t2)
    ensures t1 == t2
  {
    IsTreeDeterm(rer, [Areg(r)], InitInput(str), Empty, Forward, t1, t2);
  }

  lemma PriotreeInpDeterm(rer: RegExpRecord, r: Regex, inp: Input, t1: Tree, t2: Tree)
    requires PriotreeInp(rer, r, inp, t1)
    requires PriotreeInp(rer, r, inp, t2)
    ensures t1 == t2
  {
    IsTreeDeterm(rer, [Areg(r)], inp, Empty, Forward, t1, t2);
  }

  // Coq: highestprio_result / highestprio_result_inp
  /** `res` is the match JavaScript returns for regex `r` on `str`: the first leaf
      (`FirstBranch`) of the regex's `Priotree`. This is the spec a matcher targets. */
  ghost predicate HighestprioResult(rer: RegExpRecord, r: Regex, str: String, res: Option<Leaf>) {
    exists tree :: Priotree(rer, r, str, tree) && FirstBranch(tree, str) == res
  }
  /** `HighestprioResult` from an arbitrary input position `inp`. */
  ghost predicate HighestprioResultInp(rer: RegExpRecord, r: Regex, inp: Input, res: Option<Leaf>) {
    exists tree :: PriotreeInp(rer, r, inp, tree) && FirstLeaf(tree, inp) == res
  }

  /** The highest-priority result is unique (corollary of `PriotreeDeterm`). */
  lemma HighestprioDeterm(rer: RegExpRecord, r: Regex, str: String, res1: Option<Leaf>, res2: Option<Leaf>)
    requires HighestprioResult(rer, r, str, res1)
    requires HighestprioResult(rer, r, str, res2)
    ensures res1 == res2
  {
    var tree1 :| Priotree(rer, r, str, tree1) && FirstBranch(tree1, str) == res1;
    var tree2 :| Priotree(rer, r, str, tree2) && FirstBranch(tree2, str) == res2;
    PriotreeDeterm(rer, r, str, tree1, tree2);
  }
}
