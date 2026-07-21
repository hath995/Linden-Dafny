// Mirror of Semantics/FunctionalSemantics.v.
// Functional (fuel-based) version of the is_tree semantics: `compute_tree`, the fuel measures
// (regex_fuel/actions_fuel), and the termination theorem `functional_terminates`.
// compute_tree ports directly as a fuel-recursive function. The termination/monotonicity lemmas
// are arithmetic or depend on the strict_suffix lemmas; the suffix-dependent ones and the big
// functional_terminates induction are axiomatized for now (see PROGRESS.md Axiom Debt).
include "Semantics.dfy"

/** The **executable**, fuel-driven presentation of the semantics: `ComputeTree` computes the
    backtracking tree directly (mirroring `IsTree`'s rules), fueled by the `RegexFuel`/
    `ActionsFuel` upper bounds, with `FunctionalTerminates` proving that bound is always
    enough fuel and `ComputeTreeFuelIrrelevance` proving the result doesn't depend on exactly
    how much (sufficient) fuel is supplied. */
module FunctionalSemantics {
  import opened Std.Wrappers
  import opened WarblreRegExpRecord
  import opened WarblreNumeric
  import opened WarblrePrimitives
  import opened Chars
  import opened Groups
  import opened Regex
  import opened Tree
  import SS = StrictSuffix
  import opened Semantics

  // ----- worst-case total input (Coq: worst_input) -----
  /** The *total* input in direction `dir` — all characters gathered onto the `next` (or
      `pref`) side, with nothing left over. Gives a lookaround (which flips direction) a fuel
      bound independent of the outer scan position (see `SuffixSameWorst`). */
  function WorstInput(inp: Input, dir: Direction): Input {
    match dir
    case Forward => Input(Reverse(inp.pref) + inp.next, [])
    case Backward => Input([], Reverse(inp.next) + inp.pref)
  }

  // Coq: noi_pred
  /** The predecessor of a `NoI`, saturating at 0 (`Inf` stays `Inf`); steps a free
      quantifier's remaining `delta` down by one iteration. */
  function NoiPred(noi: NoI): NoI {
    match noi case NN(x) => NN(if x >= 1 then x - 1 else 0) case Inf => Inf
  }

  // Coq: max_iter
  /** An upper bound on how many more zero-width-checked quantifier iterations are possible
      from `inp`: one more than the remaining input length. */
  function MaxIter(inp: Input, dir: Direction): nat {
    1 + |CurrentStr(inp, dir)|
  }

  // Coq: regex_fuel — upper bound on the number of actions for a regex.
  /** An upper bound on the number of recursive steps `ComputeTree` needs to fully process
      regex `r` from `inp` — enough for `FunctionalTerminates` to guarantee termination.
      Quantifiers multiply by `MaxIter`; lookarounds recurse over the `WorstInput` in their
      own direction. */
  function RegexFuel(r: Regex, inp: Input, dir: Direction): nat
    decreases r
  {
    match r
    case Epsilon => 1
    case Character(_) => 1
    case Disjunction(r1, r2) => 1 + RegexFuel(r1, inp, dir) + RegexFuel(r2, inp, dir)
    case Sequence(r1, r2) => 1 + RegexFuel(r1, inp, dir) + RegexFuel(r2, inp, dir)
    case Quantified(b, min, delta, r1) => (2 + RegexFuel(r1, inp, dir)) * (min + MaxIter(inp, dir))
    case LookaroundR(lk, r1) => 2 + RegexFuel(r1, WorstInput(inp, LkDir(lk)), LkDir(lk))
    case Group(_, r1) => 2 + RegexFuel(r1, inp, dir)
    case AnchorR(_) => 1
    case Backreference(_) => 1
  }

  // Coq: actions_fuel
  /** The fuel bound for a whole action stack: sums `RegexFuel` over each `Areg`, adds 1 per
      `Aclose`, and (for `Acheck`) recurses only if the checked position can still advance —
      mirroring how `ComputeTree` handles each action. */
  function ActionsFuel(act: Actions, inp: Input, dir: Direction): nat
    decreases |act|
  {
    if |act| == 0 then 1
    else
      match act[0]
      case Areg(r) => RegexFuel(r, inp, dir) + ActionsFuel(act[1..], inp, dir)
      case Acheck(inpcheck) =>
        (match AdvanceInput(inpcheck, dir)
         case Some(nextinp) => 1 + ActionsFuel(act[1..], nextinp, dir)
         case None => 0)
      case Aclose(_) => 1 + ActionsFuel(act[1..], inp, dir)
  }

  // ----- compute_tree -----
  /** The executable counterpart of `IsTree`: computes the backtracking tree for action stack
      `act` at `inp`, or `None` if `fuel` runs out before finishing. Each case mirrors an
      `IsTree` rule (`tree_done`, `tree_char`, `tree_disj`, `tree_quant_forced`/`_done`/
      `_free`, `tree_group`, `tree_lk`, `tree_anchor`, `tree_backref`, ...); `FunctionalTerminates`
      shows `RegexFuel`/`ActionsFuel` is always enough fuel to reach `Some`. */
  function ComputeTree(rer: RegExpRecord, act: Actions, inp: Input, gm: GroupMap, dir: Direction, fuel: nat): Option<Tree>
    decreases fuel
  {
    if fuel == 0 then None
    else
      var f := fuel - 1;
      if |act| == 0 then Some(Match)  // tree_done
      else
        var cont := act[1..];
        match act[0]
        case Acheck(strcheck) =>
          if SS.IsStrictSuffix(inp, strcheck, dir) then
            (match ComputeTree(rer, cont, inp, gm, dir, f)
             case Some(treecont) => Some(Progress(treecont))
             case None => None)
          else Some(Mismatch)
        case Aclose(gid) =>
          (match ComputeTree(rer, cont, inp, GMClose(Idx(inp), gid, gm), dir, f)
           case Some(treecont) => Some(GroupActionT(Close(gid), treecont))
           case None => None)
        case Areg(r) =>
          match r
          case Epsilon => ComputeTree(rer, cont, inp, gm, dir, f)
          case Character(cd) =>
            (match ReadChar(rer, cd, inp, dir)
             case Some(pair) =>
               (match ComputeTree(rer, cont, pair.1, gm, dir, f)
                case Some(treecont) => Some(Read(pair.0, treecont))
                case None => None)
             case None => Some(Mismatch))
          case Disjunction(r1, r2) =>
            (match (ComputeTree(rer, [Areg(r1)] + cont, inp, gm, dir, f), ComputeTree(rer, [Areg(r2)] + cont, inp, gm, dir, f))
             case (Some(t1), Some(t2)) => Some(Choice(t1, t2))
             case _ => None)
          case Sequence(r1, r2) =>
            ComputeTree(rer, SeqList(r1, r2, dir) + cont, inp, gm, dir, f)
          case Quantified(greedy, min, delta, r1) =>
            var gidl := DefGroups(r1);
            if min > 0 then
              // tree_quant_forced
              (match ComputeTree(rer, [Areg(r1), Areg(Quantified(greedy, min - 1, delta, r1))] + cont, inp, GMReset(gidl, gm), dir, f)
               case Some(titer) => Some(GroupActionT(Reset(gidl), titer))
               case None => None)
            else if delta == NN(0) then
              ComputeTree(rer, cont, inp, gm, dir, f)  // tree_quant_done
            else
              // tree_quant_free
              (match (ComputeTree(rer, [Areg(r1), Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r1))] + cont, inp, GMReset(gidl, gm), dir, f),
                      ComputeTree(rer, cont, inp, gm, dir, f))
               case (Some(titer), Some(tskip)) => Some(GreedyChoice(greedy, GroupActionT(Reset(gidl), titer), tskip))
               case _ => None)
          case Group(gid, r1) =>
            (match ComputeTree(rer, [Areg(r1), Aclose(gid)] + cont, inp, GMOpen(Idx(inp), gid, gm), dir, f)
             case Some(treecont) => Some(GroupActionT(Open(gid), treecont))
             case None => None)
          case LookaroundR(lk, r1) =>
            (match ComputeTree(rer, [Areg(r1)], inp, gm, LkDir(lk), f)
             case None => None
             case Some(treelk) =>
               (match LkResult(lk, treelk, gm, inp)
                case Some(gmlk) =>
                  (match ComputeTree(rer, cont, inp, gmlk, dir, f)
                   case None => None
                   case Some(treecont) => Some(LK(lk, treelk, treecont)))
                case None => Some(LKFail(lk, treelk))))
          case AnchorR(a) =>
            if AnchorSatisfied(rer, a, inp) then
              (match ComputeTree(rer, cont, inp, gm, dir, f)
               case None => None
               case Some(treecont) => Some(AnchorPass(a, treecont)))
            else Some(Mismatch)
          case Backreference(gid) =>
            (match ReadBackref(rer, gm, gid, inp, dir)
             case Some(pair) =>
               (match ComputeTree(rer, cont, pair.1, gm, dir, f)
                case None => None
                case Some(tcont) => Some(ReadBackRef(pair.0, tcont)))
             case None => Some(Mismatch))
  }

  // ===== termination / monotonicity lemmas =====
  // helper: ActionsFuel additivity over a prepended Areg/Aclose head (used by trivial cases).
  lemma ActionsFuelConsAreg(r: Regex, cont: Actions, inp: Input, dir: Direction)
    ensures ActionsFuel([Areg(r)] + cont, inp, dir) == RegexFuel(r, inp, dir) + ActionsFuel(cont, inp, dir)
  {
    assert ([Areg(r)] + cont)[0] == Areg(r);
    assert ([Areg(r)] + cont)[1..] == cont;
  }

  lemma ActionsFuelConsAclose(gid: GroupId, cont: Actions, inp: Input, dir: Direction)
    ensures ActionsFuel([Aclose(gid)] + cont, inp, dir) == 1 + ActionsFuel(cont, inp, dir)
  {
    assert ([Aclose(gid)] + cont)[0] == Aclose(gid);
    assert ([Aclose(gid)] + cont)[1..] == cont;
  }

  // Coq: max_iter monotonicity from strict suffix.
  /** A strict suffix strictly decreases `MaxIter` — the well-founded measure termination
      arguments recurse on. */
  lemma StrictSuffixMaxIter(inp1: Input, inp2: Input, dir: Direction)
    requires SS.StrictSuffix(inp1, inp2, dir)
    ensures MaxIter(inp1, dir) < MaxIter(inp2, dir)
  {
    SS.SSLengthLt(inp1, inp2, dir);
  }

  // Coq: advance_max_iter / no_advance_max_iter
  lemma AdvanceMaxIter(inp: Input, nextinp: Input, dir: Direction)
    requires AdvanceInput(inp, dir) == Some(nextinp)
    ensures MaxIter(inp, dir) == MaxIter(nextinp, dir) + 1
  {}

  lemma NoAdvanceMaxIter(inp: Input, dir: Direction)
    requires AdvanceInput(inp, dir) == None
    ensures MaxIter(inp, dir) == 1
  {}

  // ----- trivial (arithmetic) termination lemmas -----
  lemma CloseTermination(cont: Actions, inp: Input, dir: Direction, gid: GroupId)
    ensures ActionsFuel(cont, inp, dir) < ActionsFuel([Aclose(gid)] + cont, inp, dir)
  { ActionsFuelConsAclose(gid, cont, inp, dir); }

  lemma EpsilonTermination(cont: Actions, inp: Input, dir: Direction)
    ensures ActionsFuel(cont, inp, dir) < ActionsFuel([Areg(Epsilon)] + cont, inp, dir)
  { ActionsFuelConsAreg(Epsilon, cont, inp, dir); }

  lemma DisjunctionLeftTermination(cont: Actions, inp: Input, dir: Direction, r1: Regex, r2: Regex)
    ensures ActionsFuel([Areg(r1)] + cont, inp, dir) < ActionsFuel([Areg(Disjunction(r1, r2))] + cont, inp, dir)
  { ActionsFuelConsAreg(r1, cont, inp, dir); ActionsFuelConsAreg(Disjunction(r1, r2), cont, inp, dir); }

  lemma DisjunctionRightTermination(cont: Actions, inp: Input, dir: Direction, r1: Regex, r2: Regex)
    ensures ActionsFuel([Areg(r2)] + cont, inp, dir) < ActionsFuel([Areg(Disjunction(r1, r2))] + cont, inp, dir)
  { ActionsFuelConsAreg(r2, cont, inp, dir); ActionsFuelConsAreg(Disjunction(r1, r2), cont, inp, dir); }

  lemma QuantDoneTermination(cont: Actions, inp: Input, dir: Direction, r1: Regex, greedy: bool)
    ensures ActionsFuel(cont, inp, dir) < ActionsFuel([Areg(Quantified(greedy, 0, NN(0), r1))] + cont, inp, dir)
  { ActionsFuelConsAreg(Quantified(greedy, 0, NN(0), r1), cont, inp, dir); }

  lemma QuantFreeSkipTermination(cont: Actions, inp: Input, dir: Direction, r1: Regex, greedy: bool, delta: NoI)
    ensures ActionsFuel(cont, inp, dir) < ActionsFuel([Areg(Quantified(greedy, 0, delta, r1))] + cont, inp, dir)
  { ActionsFuelConsAreg(Quantified(greedy, 0, delta, r1), cont, inp, dir); }

  lemma GroupTermination(cont: Actions, inp: Input, dir: Direction, r1: Regex, gid: GroupId)
    ensures ActionsFuel([Areg(r1), Aclose(gid)] + cont, inp, dir) < ActionsFuel([Areg(Group(gid, r1))] + cont, inp, dir)
  {
    assert ([Areg(r1), Aclose(gid)] + cont)[1..] == [Aclose(gid)] + cont;
    ActionsFuelConsAreg(r1, [Aclose(gid)] + cont, inp, dir);
    ActionsFuelConsAclose(gid, cont, inp, dir);
    ActionsFuelConsAreg(Group(gid, r1), cont, inp, dir);
  }

  lemma LkAfterTermination(cont: Actions, inp: Input, dir: Direction, lk: Lookaround, r1: Regex)
    ensures ActionsFuel(cont, inp, dir) < ActionsFuel([Areg(LookaroundR(lk, r1))] + cont, inp, dir)
  { ActionsFuelConsAreg(LookaroundR(lk, r1), cont, inp, dir); }

  lemma AnchorTermination(cont: Actions, inp: Input, dir: Direction, a: Anchor)
    ensures ActionsFuel(cont, inp, dir) < ActionsFuel([Areg(AnchorR(a))] + cont, inp, dir)
  { ActionsFuelConsAreg(AnchorR(a), cont, inp, dir); }

  lemma QuantForcedTermination(cont: Actions, inp: Input, dir: Direction, r1: Regex, min: nat, delta: NoI, greedy: bool)
    ensures ActionsFuel([Areg(r1), Areg(Quantified(greedy, min, delta, r1))] + cont, inp, dir)
          < ActionsFuel([Areg(Quantified(greedy, min + 1, delta, r1))] + cont, inp, dir)
  {
    assert ([Areg(r1), Areg(Quantified(greedy, min, delta, r1))] + cont)[1..] == [Areg(Quantified(greedy, min, delta, r1))] + cont;
    ActionsFuelConsAreg(r1, [Areg(Quantified(greedy, min, delta, r1))] + cont, inp, dir);
    ActionsFuelConsAreg(Quantified(greedy, min, delta, r1), cont, inp, dir);
    ActionsFuelConsAreg(Quantified(greedy, min + 1, delta, r1), cont, inp, dir);
  }

  lemma SequenceTermination(cont: Actions, inp: Input, dir: Direction, r1: Regex, r2: Regex)
    ensures ActionsFuel(SeqList(r1, r2, dir) + cont, inp, dir) < ActionsFuel([Areg(Sequence(r1, r2))] + cont, inp, dir)
  {
    match dir
    case Forward =>
      assert SeqList(r1, r2, dir) + cont == [Areg(r1), Areg(r2)] + cont;
      assert ([Areg(r1), Areg(r2)] + cont)[1..] == [Areg(r2)] + cont;
      ActionsFuelConsAreg(r1, [Areg(r2)] + cont, inp, dir);
      ActionsFuelConsAreg(r2, cont, inp, dir);
    case Backward =>
      assert SeqList(r1, r2, dir) + cont == [Areg(r2), Areg(r1)] + cont;
      assert ([Areg(r2), Areg(r1)] + cont)[1..] == [Areg(r1)] + cont;
      ActionsFuelConsAreg(r2, [Areg(r1)] + cont, inp, dir);
      ActionsFuelConsAreg(r1, cont, inp, dir);
    ActionsFuelConsAreg(Sequence(r1, r2), cont, inp, dir);
  }

  // ===== Discharged suffix-dependent monotonicity & per-rule termination lemmas. =====

  // ----- small reverse / arithmetic helpers -----
  lemma ReverseReverse(s: seq<char>)
    ensures Reverse(Reverse(s)) == s
    decreases s
  {
    if |s| == 0 {
    } else {
      assert Reverse(s) == Reverse(s[1..]) + [s[0]];
      SS.ReverseSnoc(Reverse(s[1..]), s[0]);
      ReverseReverse(s[1..]);
      assert s == [s[0]] + s[1..];
    }
  }

  lemma MulMonoRight(a: nat, b: nat, c: nat)
    requires a <= b
    ensures a * c <= b * c
  {}

  lemma MulMonoLeft(a: nat, b: nat, c: nat)
    requires b <= c
    ensures a * b <= a * c
  {}

  lemma MulSucc(x: nat, m: nat)
    ensures x * (m + 1) == x * m + x
  {}

  // Coq: suffix_same_worst (uses ss_fwd_diff/ss_bwd_diff) — strict suffix preserves the total input.
  /** Stepping to a strict suffix doesn't change the *total* input: `WorstInput` is the same
      before and after. Justifies giving a lookaround's `RegexFuel` a bound independent of the
      surrounding scan position. */
  lemma SuffixSameWorst(inp1: Input, inp2: Input, d: Direction, dir: Direction)
    requires SS.StrictSuffix(inp1, inp2, d)
    ensures WorstInput(inp1, dir) == WorstInput(inp2, dir)
  {
    match d
    case Forward =>
      SS.SSFwdDiff(inp1.next, inp1.pref, inp2.next, inp2.pref);
      var diff :| diff != [] && inp2.next == diff + inp1.next && inp1.pref == Reverse(diff) + inp2.pref;
      SS.ReverseApp(Reverse(diff), inp2.pref);
      ReverseReverse(diff);
      assert Reverse(inp1.pref) == Reverse(inp2.pref) + diff;
      SS.ReverseApp(diff, inp1.next);
      assert Reverse(inp2.next) == Reverse(inp1.next) + Reverse(diff);
      assert Reverse(inp1.pref) + inp1.next == Reverse(inp2.pref) + inp2.next;
      assert Reverse(inp1.next) + inp1.pref == Reverse(inp2.next) + inp2.pref;
    case Backward =>
      SS.SSBwdDiff(inp1.next, inp1.pref, inp2.next, inp2.pref);
      var diff :| diff != [] && inp1.next == diff + inp2.next && inp2.pref == Reverse(diff) + inp1.pref;
      SS.ReverseApp(Reverse(diff), inp1.pref);
      ReverseReverse(diff);
      assert Reverse(inp2.pref) == Reverse(inp1.pref) + diff;
      SS.ReverseApp(diff, inp2.next);
      assert Reverse(inp1.next) == Reverse(inp2.next) + Reverse(diff);
      assert Reverse(inp1.pref) + inp1.next == Reverse(inp2.pref) + inp2.next;
      assert Reverse(inp1.next) + inp1.pref == Reverse(inp2.next) + inp2.pref;
  }

  // Coq: worst_input_suffix
  /** `inp` either already *is* its own `WorstInput`, or is a strict suffix of it — i.e.
      `WorstInput` is always reachable from `inp` by advancing zero or more times. */
  lemma WorstInputSuffix(inp: Input, worst: Input, dir: Direction)
    requires WorstInput(inp, dir) == worst
    ensures worst == inp || SS.StrictSuffix(inp, worst, dir)
  {
    match dir
    case Forward =>
      assert worst == Input(Reverse(inp.pref) + inp.next, []);
      if inp.pref == [] {
        assert worst == inp;
      } else {
        var diff := Reverse(inp.pref);
        ReverseLength(inp.pref);
        assert diff != [];
        assert worst.next == diff + inp.next;
        ReverseReverse(inp.pref);
        assert inp.pref == Reverse(diff) + worst.pref;
        SS.SSFwdDiff(inp.next, inp.pref, worst.next, worst.pref);
        assert inp == Input(inp.next, inp.pref) && worst == Input(worst.next, worst.pref);
      }
    case Backward =>
      assert worst == Input([], Reverse(inp.next) + inp.pref);
      if inp.next == [] {
        assert worst == inp;
      } else {
        var diff := inp.next;
        assert diff != [];
        assert inp.next == diff + worst.next;
        assert worst.pref == Reverse(diff) + inp.pref;
        SS.SSBwdDiff(inp.next, inp.pref, worst.next, worst.pref);
        assert inp == Input(inp.next, inp.pref) && worst == Input(worst.next, worst.pref);
      }
  }

  // Coq: regex_monoton
  /** `RegexFuel` is monotone: shrinking the input (moving to a strict suffix) never needs
      more fuel to process `r`. */
  lemma RegexMonoton(r: Regex, dir: Direction, inp1: Input, inp2: Input)
    requires SS.StrictSuffix(inp1, inp2, dir)
    ensures RegexFuel(r, inp1, dir) <= RegexFuel(r, inp2, dir)
    decreases r
  {
    match r
    case Epsilon =>
    case Character(_) =>
    case AnchorR(_) =>
    case Backreference(_) =>
    case Disjunction(r1, r2) => RegexMonoton(r1, dir, inp1, inp2); RegexMonoton(r2, dir, inp1, inp2);
    case Sequence(r1, r2) => RegexMonoton(r1, dir, inp1, inp2); RegexMonoton(r2, dir, inp1, inp2);
    case Group(_, r1) => RegexMonoton(r1, dir, inp1, inp2);
    case Quantified(b, min, delta, r1) =>
      RegexMonoton(r1, dir, inp1, inp2);
      StrictSuffixMaxIter(inp1, inp2, dir);
      MulMonoRight(2 + RegexFuel(r1, inp1, dir), 2 + RegexFuel(r1, inp2, dir), min + MaxIter(inp1, dir));
      MulMonoLeft(2 + RegexFuel(r1, inp2, dir), min + MaxIter(inp1, dir), min + MaxIter(inp2, dir));
    case LookaroundR(lk, r1) =>
      SuffixSameWorst(inp1, inp2, dir, LkDir(lk));   // WorstInput equal ⇒ RegexFuel calls identical
  }

  // Coq: actions_monoton
  /** `ActionsFuel` is monotone in the same sense as `RegexMonoton`, propagated down the
      action stack. */
  lemma ActionsMonoton(act: Actions, dir: Direction, inp1: Input, inp2: Input)
    requires SS.StrictSuffix(inp1, inp2, dir)
    ensures ActionsFuel(act, inp1, dir) <= ActionsFuel(act, inp2, dir)
    decreases |act|
  {
    if |act| == 0 {
    } else {
      match act[0]
      case Areg(r) =>
        RegexMonoton(r, dir, inp1, inp2);
        ActionsMonoton(act[1..], dir, inp1, inp2);
      case Acheck(inpcheck) =>
        // both reduce via AdvanceInput(inpcheck, dir), independent of inp1/inp2 ⇒ equal
      case Aclose(_) =>
        ActionsMonoton(act[1..], dir, inp1, inp2);
    }
  }

  // Coq: check_termination
  /** Processing an `Acheck(strcheck)` action strictly costs fuel: since `inp` is a strict
      suffix of `strcheck`, the continuation needs strictly less fuel than the whole
      `[Acheck(strcheck)] + cont` stack. */
  lemma CheckTermination(cont: Actions, inp: Input, strcheck: Input, dir: Direction)
    requires SS.StrictSuffix(inp, strcheck, dir)
    ensures ActionsFuel(cont, inp, dir) < ActionsFuel([Acheck(strcheck)] + cont, inp, dir)
  {
    assert ([Acheck(strcheck)] + cont)[0] == Acheck(strcheck);
    assert ([Acheck(strcheck)] + cont)[1..] == cont;
    SS.StrictNoAdvance(inp, strcheck, dir);
    var n := AdvanceInput(strcheck, dir).value;
    assert AdvanceInput(strcheck, dir) == Some(n);
    SS.AdvanceSuffix(strcheck, n, inp, dir);   // n == inp || StrictSuffix(inp, n, dir)
    if n != inp {
      ActionsMonoton(cont, dir, inp, n);
    }
  }

  // Coq: character_termination
  /** After successfully reading a character (`ReadChar`), the continuation's fuel requirement
      is strictly less than that of the whole `Character` action — the per-rule fact
      `FunctionalTerminates` needs for the `Character` case. */
  lemma CharacterTermination(rer: RegExpRecord, cont: Actions, inp: Input, dir: Direction, cd: CharDescr, c: char, nextinp: Input)
    requires ReadChar(rer, cd, inp, dir) == Some((c, nextinp))
    ensures ActionsFuel(cont, nextinp, dir) < ActionsFuel([Areg(Character(cd))] + cont, inp, dir)
  {
    ActionsFuelConsAreg(Character(cd), cont, inp, dir);
    SS.ReadCharSuffix(inp, dir, nextinp, cd, c, rer);   // StrictSuffix(nextinp, inp, dir)
    ActionsMonoton(cont, dir, nextinp, inp);
  }

  // Coq: quant_free_iter_termination
  /** Taking one more free-quantifier iteration strictly reduces the fuel bound versus the
      whole `Quantified(greedy, 0, delta, r1)` action — the arithmetic core of why unbounded
      quantifiers still terminate. */
  lemma QuantFreeIterTermination(cont: Actions, inp: Input, dir: Direction, r1: Regex, greedy: bool, delta: NoI)
    ensures ActionsFuel([Areg(r1), Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r1))] + cont, inp, dir)
          < ActionsFuel([Areg(Quantified(greedy, 0, delta, r1))] + cont, inp, dir)
  {
    var qd := Quantified(greedy, 0, delta, r1);
    var qp := Quantified(greedy, 0, NoiPred(delta), r1);
    var lhsList := [Areg(r1), Acheck(inp), Areg(qp)] + cont;
    ActionsFuelConsAreg(qd, cont, inp, dir);
    assert RegexFuel(qd, inp, dir) == (2 + RegexFuel(r1, inp, dir)) * MaxIter(inp, dir);
    assert lhsList[0] == Areg(r1);
    assert lhsList[1..] == [Acheck(inp), Areg(qp)] + cont;
    ActionsFuelConsAreg(r1, [Acheck(inp), Areg(qp)] + cont, inp, dir);
    var mid := [Acheck(inp), Areg(qp)] + cont;
    assert mid[0] == Acheck(inp);
    assert mid[1..] == [Areg(qp)] + cont;
    var A := RegexFuel(r1, inp, dir);
    var C := ActionsFuel(cont, inp, dir);
    match AdvanceInput(inp, dir)
    case None =>
      NoAdvanceMaxIter(inp, dir);   // MaxIter(inp,dir) == 1 ⇒ RHS == 2+A+C, LHS == A
    case Some(n) =>
      AdvanceMaxIter(inp, n, dir);   // MaxIter(inp,dir) == MaxIter(n,dir)+1
      SS.ReadSuffix(inp, dir, n);    // StrictSuffix(n, inp, dir)
      RegexMonoton(r1, dir, n, inp);
      ActionsMonoton(cont, dir, n, inp);
      ActionsFuelConsAreg(qp, cont, n, dir);
      var An := RegexFuel(r1, n, dir);
      var Mn := MaxIter(n, dir);
      assert RegexFuel(qp, n, dir) == (2 + An) * Mn;
      MulSucc(2 + A, Mn);                  // (2+A)*(Mn+1) == (2+A)*Mn + (2+A)
      MulMonoRight(2 + An, 2 + A, Mn);     // (2+An)*Mn <= (2+A)*Mn
  }

  // Coq: lk_lk_termination
  /** Matching a lookaround's body (`[Areg(r1)]` in `LkDir(lk)`) always costs strictly less
      fuel than the surrounding `LookaroundR` action, regardless of the outer continuation
      `cont`. */
  lemma LkLkTermination(cont: Actions, inp: Input, dir: Direction, lk: Lookaround, r1: Regex)
    ensures ActionsFuel([Areg(r1)], inp, LkDir(lk)) < ActionsFuel([Areg(LookaroundR(lk, r1))] + cont, inp, dir)
  {
    var d := LkDir(lk);
    var worst := WorstInput(inp, d);
    ActionsFuelConsAreg(LookaroundR(lk, r1), cont, inp, dir);
    ActionsFuelConsAreg(r1, [], inp, d);   // ActionsFuel([Areg(r1)],inp,d) == RegexFuel(r1,inp,d)+1
    WorstInputSuffix(inp, worst, d);
    if worst != inp {
      RegexMonoton(r1, d, inp, worst);
    }
  }

  // ----- backref helpers -----
  // AdvanceInputN by a positive in-bounds amount is a strict suffix.
  /** Advancing the input by a positive, in-bounds amount `n` (`AdvanceInputN`) always yields
      a strict suffix of the original — the multi-character analogue of
      `StrictSuffix.ReadSuffix`, needed for backreference termination. */
  lemma AdvanceInputNSuffix(inp: Input, n: nat, dir: Direction)
    requires n > 0
    requires match dir case Forward => n <= |inp.next| case Backward => n <= |inp.pref|
    ensures SS.StrictSuffix(AdvanceInputN(inp, n, dir), inp, dir)
  {
    var nextinp := AdvanceInputN(inp, n, dir);
    match dir
    case Forward =>
      var diff := Take(inp.next, n);
      assert inp.next == Take(inp.next, n) + Drop(inp.next, n);
      assert nextinp.next == Drop(inp.next, n);
      assert |diff| == n && diff != [];
      assert inp.next == diff + nextinp.next;
      assert nextinp.pref == Reverse(diff) + inp.pref;
      SS.SSFwdDiff(nextinp.next, nextinp.pref, inp.next, inp.pref);
      assert nextinp == Input(nextinp.next, nextinp.pref) && inp == Input(inp.next, inp.pref);
    case Backward =>
      var diff := Reverse(Take(inp.pref, n));
      assert inp.pref == Take(inp.pref, n) + Drop(inp.pref, n);
      ReverseLength(Take(inp.pref, n));
      assert |diff| == n && diff != [];
      assert nextinp.next == diff + inp.next;
      ReverseReverse(Take(inp.pref, n));   // Reverse(diff) == Take(inp.pref,n)
      assert inp.pref == Reverse(diff) + nextinp.pref;
      SS.SSBwdDiff(nextinp.next, nextinp.pref, inp.next, inp.pref);
      assert nextinp == Input(nextinp.next, nextinp.pref) && inp == Input(inp.next, inp.pref);
  }

  // |brStr| is within the readable bound in the matching direction.
  /** The text captured by a successful backreference read (`ReadBackref`) is no longer than
      the remaining input in the matching direction — so consuming it via `AdvanceInputN`
      stays in bounds. */
  lemma BackrefBound(rer: RegExpRecord, gm: GroupMap, gid: GroupId, inp: Input, dir: Direction, brStr: String, nextinp: Input)
    requires ReadBackref(rer, gm, gid, inp, dir) == Some((brStr, nextinp))
    ensures match dir case Forward => |brStr| <= |inp.next| case Backward => |brStr| <= |inp.pref|
  {
    match Find(gid, gm)
    case None =>
    case Some(Range(_, None)) =>
    case Some(Range(startIdx, Some(endIdx))) =>
      var len := if endIdx >= startIdx then endIdx - startIdx else 0;
      match dir
      case Forward => assert brStr == Take(inp.next, len) && len <= |inp.next|;
      case Backward =>
        assert brStr == Reverse(Take(inp.pref, len)) && len <= |inp.pref|;
        ReverseLength(Take(inp.pref, len));
  }

  // Coq: backref_suffix / backref_termination
  /** After successfully reading a backreference (`ReadBackref`), the continuation's fuel
      requirement is strictly less than that of the whole `Backreference` action. */
  lemma BackrefTermination(rer: RegExpRecord, cont: Actions, inp: Input, dir: Direction, gid: GroupId, gm: GroupMap, brStr: String, nextinp: Input)
    requires ReadBackref(rer, gm, gid, inp, dir) == Some((brStr, nextinp))
    ensures ActionsFuel(cont, nextinp, dir) < ActionsFuel([Areg(Backreference(gid))] + cont, inp, dir)
  {
    ActionsFuelConsAreg(Backreference(gid), cont, inp, dir);
    ReadBackrefSuccessAdvance(rer, gm, gid, inp, dir, brStr, nextinp);   // nextinp == AdvanceInputN(inp,|brStr|,dir)
    if nextinp != inp {
      AdvanceInputN0(inp, dir);    // |brStr| == 0 would force nextinp == inp
      assert |brStr| > 0;
      BackrefBound(rer, gm, gid, inp, dir, brStr, nextinp);
      AdvanceInputNSuffix(inp, |brStr|, dir);
      ActionsMonoton(cont, dir, nextinp, inp);
    }
  }

  // Coq: functional_terminates — enough fuel guarantees a tree. Induction on fuel, mirroring
  // ComputeTree: each recursive call's actions-fuel is strictly smaller (per-rule termination
  // lemma), so f = fuel-1 >= ActionsFuel(act,..) > ActionsFuel(act',..) feeds the IH.
  /** **Enough fuel guarantees a tree.** If `fuel` exceeds `ActionsFuel(act, inp, dir)`,
      `ComputeTree` is guaranteed to return `Some` rather than running out of fuel — proved by
      induction on `fuel`, using the per-rule termination lemmas above to show each recursive
      call's required fuel strictly decreases. */
  lemma FunctionalTerminates(rer: RegExpRecord, act: Actions, inp: Input, gm: GroupMap, dir: Direction, fuel: nat)
    requires fuel > ActionsFuel(act, inp, dir)
    ensures ComputeTree(rer, act, inp, gm, dir, fuel).Some?
    decreases fuel
  {
    var f := fuel - 1;
    if |act| == 0 {
      return;   // ComputeTree returns Some(Match)
    }
    var cont := act[1..];
    assert act == [act[0]] + cont;
    match act[0]
    case Acheck(strcheck) =>
      assert act == [Acheck(strcheck)] + cont;
      if SS.IsStrictSuffix(inp, strcheck, dir) {
        CheckTermination(cont, inp, strcheck, dir);
        FunctionalTerminates(rer, cont, inp, gm, dir, f);
      }
    case Aclose(gid) =>
      assert act == [Aclose(gid)] + cont;
      CloseTermination(cont, inp, dir, gid);
      FunctionalTerminates(rer, cont, inp, GMClose(Idx(inp), gid, gm), dir, f);
    case Areg(r) =>
      match r
      case Epsilon =>
        assert act == [Areg(Epsilon)] + cont;
        EpsilonTermination(cont, inp, dir);
        FunctionalTerminates(rer, cont, inp, gm, dir, f);
      case Character(cd) =>
        assert act == [Areg(Character(cd))] + cont;
        match ReadChar(rer, cd, inp, dir) {
          case Some(pair) =>
            CharacterTermination(rer, cont, inp, dir, cd, pair.0, pair.1);
            FunctionalTerminates(rer, cont, pair.1, gm, dir, f);
          case None =>
        }
      case Disjunction(r1, r2) =>
        assert act == [Areg(Disjunction(r1, r2))] + cont;
        DisjunctionLeftTermination(cont, inp, dir, r1, r2);
        DisjunctionRightTermination(cont, inp, dir, r1, r2);
        FunctionalTerminates(rer, [Areg(r1)] + cont, inp, gm, dir, f);
        FunctionalTerminates(rer, [Areg(r2)] + cont, inp, gm, dir, f);
      case Sequence(r1, r2) =>
        assert act == [Areg(Sequence(r1, r2))] + cont;
        SequenceTermination(cont, inp, dir, r1, r2);
        FunctionalTerminates(rer, SeqList(r1, r2, dir) + cont, inp, gm, dir, f);
      case Quantified(greedy, min, delta, r1) =>
        assert act == [Areg(Quantified(greedy, min, delta, r1))] + cont;
        var gidl := DefGroups(r1);
        if min > 0 {
          QuantForcedTermination(cont, inp, dir, r1, min - 1, delta, greedy);
          assert (min - 1) + 1 == min;
          FunctionalTerminates(rer, [Areg(r1), Areg(Quantified(greedy, min - 1, delta, r1))] + cont, inp, GMReset(gidl, gm), dir, f);
        } else if delta == NN(0) {
          QuantDoneTermination(cont, inp, dir, r1, greedy);
          FunctionalTerminates(rer, cont, inp, gm, dir, f);
        } else {
          QuantFreeIterTermination(cont, inp, dir, r1, greedy, delta);
          QuantFreeSkipTermination(cont, inp, dir, r1, greedy, delta);
          FunctionalTerminates(rer, [Areg(r1), Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r1))] + cont, inp, GMReset(gidl, gm), dir, f);
          FunctionalTerminates(rer, cont, inp, gm, dir, f);
        }
      case Group(gid, r1) =>
        assert act == [Areg(Group(gid, r1))] + cont;
        GroupTermination(cont, inp, dir, r1, gid);
        FunctionalTerminates(rer, [Areg(r1), Aclose(gid)] + cont, inp, GMOpen(Idx(inp), gid, gm), dir, f);
      case LookaroundR(lk, r1) =>
        assert act == [Areg(LookaroundR(lk, r1))] + cont;
        LkLkTermination(cont, inp, dir, lk, r1);
        FunctionalTerminates(rer, [Areg(r1)], inp, gm, LkDir(lk), f);
        var treelk := ComputeTree(rer, [Areg(r1)], inp, gm, LkDir(lk), f).value;
        match LkResult(lk, treelk, gm, inp) {
          case Some(gmlk) =>
            LkAfterTermination(cont, inp, dir, lk, r1);
            FunctionalTerminates(rer, cont, inp, gmlk, dir, f);
          case None =>
        }
      case AnchorR(a) =>
        assert act == [Areg(AnchorR(a))] + cont;
        if AnchorSatisfied(rer, a, inp) {
          AnchorTermination(cont, inp, dir, a);
          FunctionalTerminates(rer, cont, inp, gm, dir, f);
        }
      case Backreference(gid) =>
        assert act == [Areg(Backreference(gid))] + cont;
        match ReadBackref(rer, gm, gid, inp, dir) {
          case Some(pair) =>
            BackrefTermination(rer, cont, inp, dir, gid, gm, pair.0, pair.1);
            FunctionalTerminates(rer, cont, pair.1, gm, dir, f);
          case None =>
        }
  }

  // ComputeTree's result is independent of the fuel value, as long as fuel is sufficient.
  // Same case structure as FunctionalTerminates; each recursive sub-call's fuel (f1,f2) is still
  // sufficient (per-rule termination lemma), so the IH equates the two and the one-step unfolds match.
  /** `ComputeTree`'s result doesn't depend on exactly how much fuel it's given, as long as
      it's sufficient (per `FunctionalTerminates`) — so `ComputeTree` computes a well-defined
      tree independent of the fuel parameter. */
  lemma ComputeTreeFuelIrrelevance(rer: RegExpRecord, act: Actions, inp: Input, gm: GroupMap, dir: Direction, fuel1: nat, fuel2: nat)
    requires fuel1 > ActionsFuel(act, inp, dir)
    requires fuel2 > ActionsFuel(act, inp, dir)
    ensures ComputeTree(rer, act, inp, gm, dir, fuel1) == ComputeTree(rer, act, inp, gm, dir, fuel2)
    decreases fuel1 + fuel2
  {
    if |act| == 0 {
      return;
    }
    var cont := act[1..];
    var f1 := fuel1 - 1;
    var f2 := fuel2 - 1;
    assert act == [act[0]] + cont;
    match act[0]
    case Acheck(strcheck) =>
      assert act == [Acheck(strcheck)] + cont;
      if SS.IsStrictSuffix(inp, strcheck, dir) {
        CheckTermination(cont, inp, strcheck, dir);
        ComputeTreeFuelIrrelevance(rer, cont, inp, gm, dir, f1, f2);
      }
    case Aclose(gid) =>
      assert act == [Aclose(gid)] + cont;
      CloseTermination(cont, inp, dir, gid);
      ComputeTreeFuelIrrelevance(rer, cont, inp, GMClose(Idx(inp), gid, gm), dir, f1, f2);
    case Areg(r) =>
      match r
      case Epsilon =>
        assert act == [Areg(Epsilon)] + cont;
        EpsilonTermination(cont, inp, dir);
        ComputeTreeFuelIrrelevance(rer, cont, inp, gm, dir, f1, f2);
      case Character(cd) =>
        assert act == [Areg(Character(cd))] + cont;
        match ReadChar(rer, cd, inp, dir) {
          case Some(pair) =>
            CharacterTermination(rer, cont, inp, dir, cd, pair.0, pair.1);
            ComputeTreeFuelIrrelevance(rer, cont, pair.1, gm, dir, f1, f2);
          case None =>
        }
      case Disjunction(r1, r2) =>
        assert act == [Areg(Disjunction(r1, r2))] + cont;
        DisjunctionLeftTermination(cont, inp, dir, r1, r2);
        DisjunctionRightTermination(cont, inp, dir, r1, r2);
        ComputeTreeFuelIrrelevance(rer, [Areg(r1)] + cont, inp, gm, dir, f1, f2);
        ComputeTreeFuelIrrelevance(rer, [Areg(r2)] + cont, inp, gm, dir, f1, f2);
      case Sequence(r1, r2) =>
        assert act == [Areg(Sequence(r1, r2))] + cont;
        SequenceTermination(cont, inp, dir, r1, r2);
        ComputeTreeFuelIrrelevance(rer, SeqList(r1, r2, dir) + cont, inp, gm, dir, f1, f2);
      case Quantified(greedy, min, delta, r1) =>
        assert act == [Areg(Quantified(greedy, min, delta, r1))] + cont;
        var gidl := DefGroups(r1);
        if min > 0 {
          QuantForcedTermination(cont, inp, dir, r1, min - 1, delta, greedy);
          assert (min - 1) + 1 == min;
          ComputeTreeFuelIrrelevance(rer, [Areg(r1), Areg(Quantified(greedy, min - 1, delta, r1))] + cont, inp, GMReset(gidl, gm), dir, f1, f2);
        } else if delta == NN(0) {
          QuantDoneTermination(cont, inp, dir, r1, greedy);
          ComputeTreeFuelIrrelevance(rer, cont, inp, gm, dir, f1, f2);
        } else {
          QuantFreeIterTermination(cont, inp, dir, r1, greedy, delta);
          QuantFreeSkipTermination(cont, inp, dir, r1, greedy, delta);
          ComputeTreeFuelIrrelevance(rer, [Areg(r1), Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r1))] + cont, inp, GMReset(gidl, gm), dir, f1, f2);
          ComputeTreeFuelIrrelevance(rer, cont, inp, gm, dir, f1, f2);
        }
      case Group(gid, r1) =>
        assert act == [Areg(Group(gid, r1))] + cont;
        GroupTermination(cont, inp, dir, r1, gid);
        ComputeTreeFuelIrrelevance(rer, [Areg(r1), Aclose(gid)] + cont, inp, GMOpen(Idx(inp), gid, gm), dir, f1, f2);
      case LookaroundR(lk, r1) =>
        assert act == [Areg(LookaroundR(lk, r1))] + cont;
        LkLkTermination(cont, inp, dir, lk, r1);
        ComputeTreeFuelIrrelevance(rer, [Areg(r1)], inp, gm, LkDir(lk), f1, f2);
        var o1 := ComputeTree(rer, [Areg(r1)], inp, gm, LkDir(lk), f1);
        if o1.Some? {
          var treelk := o1.value;
          match LkResult(lk, treelk, gm, inp) {
            case Some(gmlk) =>
              LkAfterTermination(cont, inp, dir, lk, r1);
              ComputeTreeFuelIrrelevance(rer, cont, inp, gmlk, dir, f1, f2);
            case None =>
          }
        }
      case AnchorR(a) =>
        assert act == [Areg(AnchorR(a))] + cont;
        if AnchorSatisfied(rer, a, inp) {
          AnchorTermination(cont, inp, dir, a);
          ComputeTreeFuelIrrelevance(rer, cont, inp, gm, dir, f1, f2);
        }
      case Backreference(gid) =>
        assert act == [Areg(Backreference(gid))] + cont;
        match ReadBackref(rer, gm, gid, inp, dir) {
          case Some(pair) =>
            BackrefTermination(rer, cont, inp, dir, gid, gm, pair.0, pair.1);
            ComputeTreeFuelIrrelevance(rer, cont, pair.1, gm, dir, f1, f2);
          case None =>
        }
  }
}
