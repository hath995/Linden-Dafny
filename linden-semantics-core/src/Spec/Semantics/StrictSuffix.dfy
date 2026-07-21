// Mirror of Semantics/StrictSuffix.v.
// strict_suffix is the transitive closure of advance_input. In Coq it is an inductive Prop with a
// separate functional decider `is_strict_suffix` proven equivalent (is_strict_suffix_correct).
// Here we DEFINE StrictSuffix as that functional decider (a plain recursive predicate, per the
// no-least-predicate policy); is_strict_suffix_correct is then reflexivity. The structural
// characterization lemmas (ss_fwd_diff/ss_bwd_diff/strict_advance/advance_suffix/trans) are
// currently axiomatized — see Axiom Debt in PROGRESS.md.
include "Chars.dfy"

/** The "strict suffix" progress relation: `StrictSuffix(inp1, inp2, dir)` holds when `inp1`
    is reachable from `inp2` by advancing at least once in direction `dir`. This is the
    machinery behind the empty-iteration guard (`Semantics.Acheck`/`Tree.Progress`) that stops
    a quantifier iteration from repeating when it consumed no input — e.g. what keeps
    a nested star like `(a*)*` from looping forever. */
module StrictSuffix {
  import opened Std.Wrappers
  import opened WarblreRegExpRecord
  import opened WarblrePrimitives  // Direction
  import opened Chars

  // Coq: Fixpoint strict_suffix_forward inp next pref.
  /** Forward-direction decision procedure underlying `StrictSuffix`: whether `inp` is reached
      by consuming some nonempty prefix of `next` (accumulating it onto `pref`). */
  predicate StrictSuffixForward(inp: Input, next: seq<char>, pref: seq<char>)
    decreases |next|
  {
    if |next| == 0 then false
    else if Input(next[1..], [next[0]] + pref) == inp then true
    else StrictSuffixForward(inp, next[1..], [next[0]] + pref)
  }

  // Coq: Fixpoint strict_suffix_backward inp next pref.
  /** Backward-direction mirror of `StrictSuffixForward`, walking `pref` instead of `next`. */
  predicate StrictSuffixBackward(inp: Input, next: seq<char>, pref: seq<char>)
    decreases |pref|
  {
    if |pref| == 0 then false
    else if Input([pref[0]] + next, pref[1..]) == inp then true
    else StrictSuffixBackward(inp, [pref[0]] + next, pref[1..])
  }

  // Coq: is_strict_suffix
  /** Direction-dispatching decision procedure: picks `StrictSuffixForward` or
      `StrictSuffixBackward` according to `dir`. */
  predicate IsStrictSuffix(inp1: Input, inp2: Input, dir: Direction) {
    match dir
    case Forward => StrictSuffixForward(inp1, inp2.next, inp2.pref)
    case Backward => StrictSuffixBackward(inp1, inp2.next, inp2.pref)
  }

  // strict_suffix (identified with its decision procedure).
  /** The public strict-suffix relation (identified with its decision procedure
      `IsStrictSuffix`). */
  predicate StrictSuffix(inp1: Input, inp2: Input, dir: Direction) {
    IsStrictSuffix(inp1, inp2, dir)
  }

  // Coq: is_strict_suffix_correct — reflexivity in this encoding.
  /** `IsStrictSuffix` and `StrictSuffix` agree — trivial here since `StrictSuffix` is defined
      as `IsStrictSuffix`. */
  lemma IsStrictSuffixCorrect(inp1: Input, inp2: Input, dir: Direction)
    ensures IsStrictSuffix(inp1, inp2, dir) <==> StrictSuffix(inp1, inp2, dir)
  {}

  /** The negated form of `IsStrictSuffixCorrect`. */
  lemma IsStrictSuffixInvFalse(inp1: Input, inp2: Input, dir: Direction)
    ensures !IsStrictSuffix(inp1, inp2, dir) <==> !StrictSuffix(inp1, inp2, dir)
  {}

  // ----- length decrease (critical for fuel arguments) -----
  /** A forward strict suffix strictly shrinks the remaining input `next`. */
  lemma SSForwardLen(inp: Input, next: seq<char>, pref: seq<char>)
    requires StrictSuffixForward(inp, next, pref)
    ensures |inp.next| < |next|
    decreases |next|
  {
    if |next| != 0 && Input(next[1..], [next[0]] + pref) != inp {
      SSForwardLen(inp, next[1..], [next[0]] + pref);
    }
  }

  /** A backward strict suffix strictly shrinks the consumed prefix `pref`. */
  lemma SSBackwardLen(inp: Input, next: seq<char>, pref: seq<char>)
    requires StrictSuffixBackward(inp, next, pref)
    ensures |inp.pref| < |pref|
    decreases |pref|
  {
    if |pref| != 0 && Input([pref[0]] + next, pref[1..]) != inp {
      SSBackwardLen(inp, [pref[0]] + next, pref[1..]);
    }
  }

  // Coq: ss_length_lt / strict_suffix_current
  /** If `inp1` is a strict suffix of `inp2`, the remaining string at `inp1`
      (`CurrentStr(inp1, dir)`) is strictly shorter — the core progress measure that founds
      fuel/termination arguments over the semantics. */
  lemma SSLengthLt(inp1: Input, inp2: Input, dir: Direction)
    requires StrictSuffix(inp1, inp2, dir)
    ensures |CurrentStr(inp1, dir)| < |CurrentStr(inp2, dir)|
  {
    match dir
    case Forward => SSForwardLen(inp1, inp2.next, inp2.pref);
    case Backward => SSBackwardLen(inp1, inp2.next, inp2.pref);
  }

  /** Restates `SSLengthLt` under the Coq name `strict_suffix_current`. */
  lemma StrictSuffixCurrent(inp1: Input, inp2: Input, dir: Direction)
    requires StrictSuffix(inp1, inp2, dir)
    ensures |CurrentStr(inp1, dir)| < |CurrentStr(inp2, dir)|
  {
    SSLengthLt(inp1, inp2, dir);
  }

  // Coq: ss_neq
  /** A strict-suffix relationship implies the two inputs are different. */
  lemma SSNeq(inp1: Input, inp2: Input, dir: Direction)
    requires StrictSuffix(inp1, inp2, dir)
    ensures inp1 != inp2
  {
    SSLengthLt(inp1, inp2, dir);
  }

  // Coq: read_suffix — one advance is a strict suffix.
  /** Advancing the input by one step (`AdvanceInput`) always yields a strict suffix of the
      starting input — the base case that founds the whole relation. */
  lemma ReadSuffix(inp: Input, dir: Direction, nextinp: Input)
    requires AdvanceInput(inp, dir) == Some(nextinp)
    ensures StrictSuffix(nextinp, inp, dir)
  {
    match dir
    case Forward =>
      assert |inp.next| != 0;
      assert Input(inp.next[1..], [inp.next[0]] + inp.pref) == nextinp;
    case Backward =>
      assert |inp.pref| != 0;
      assert Input([inp.pref[0]] + inp.next, inp.pref[1..]) == nextinp;
  }

  // Coq: advance_current_plus_one
  /** One step of `AdvanceInput` shortens the current string by exactly one character. */
  lemma AdvanceCurrentPlusOne(inp1: Input, inp2: Input, dir: Direction)
    requires AdvanceInput(inp2, dir) == Some(inp1)
    ensures |CurrentStr(inp2, dir)| == |CurrentStr(inp1, dir)| + 1
  {}

  // Coq: read_char_suffix
  /** Successfully reading a character (`ReadChar`) leaves a strict suffix of the input it
      started from. */
  lemma ReadCharSuffix(inp: Input, dir: Direction, nextinp: Input, cd: CharDescr, c: char, rer: RegExpRecord)
    requires ReadChar(rer, cd, inp, dir) == Some((c, nextinp))
    ensures StrictSuffix(nextinp, inp, dir)
  {
    ReadCharSuccessAdvance(rer, cd, inp, dir, c, nextinp);
    ReadSuffix(inp, dir, nextinp);
  }

  // Coq: strict_no_advance — a strict suffix means inp2 can advance.
  /** If `inp1` is a strict suffix of `inp2`, then `inp2` can still be advanced — a strict
      suffix witnesses that at least one more step was possible. */
  lemma StrictNoAdvance(inp1: Input, inp2: Input, dir: Direction)
    requires StrictSuffix(inp1, inp2, dir)
    ensures AdvanceInput(inp2, dir) != None
  {
    SSLengthLt(inp1, inp2, dir);
    match dir
    case Forward => assert |inp2.next| > 0;
    case Backward => assert |inp2.pref| > 0;
  }

  // reverse-of-snoc (Reverse is head-recursive, so this needs its own induction).
  /** `Reverse` distributes over appending a single trailing character: an auxiliary fact for
      the diff-based characterization lemmas below. */
  lemma ReverseSnoc(s: seq<char>, x: char)
    ensures Reverse(s + [x]) == [x] + Reverse(s)
    decreases s
  {
    if |s| == 0 {
      assert s + [x] == [x];
    } else {
      assert (s + [x])[0] == s[0] && (s + [x])[1..] == s[1..] + [x];
      ReverseSnoc(s[1..], x);
    }
  }

  /** `Reverse` distributes over concatenation: `Reverse(a + b) == Reverse(b) + Reverse(a)`. */
  lemma ReverseApp(a: seq<char>, b: seq<char>)
    ensures Reverse(a + b) == Reverse(b) + Reverse(a)
    decreases a
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      assert (a + b)[0] == a[0] && (a + b)[1..] == a[1..] + b;
      ReverseApp(a[1..], b);
    }
  }

  // Coq: strict_suffix_trans — via the diff characterizations.
  /** `StrictSuffix` is transitive, proved via the `SSFwdDiff`/`SSBwdDiff` structural
      characterizations. */
  lemma StrictSuffixTrans(inp1: Input, inp2: Input, inp3: Input, dir: Direction)
    requires StrictSuffix(inp1, inp2, dir)
    requires StrictSuffix(inp2, inp3, dir)
    ensures StrictSuffix(inp1, inp3, dir)
  {
    match dir
    case Forward =>
      SSFwdDiff(inp1.next, inp1.pref, inp2.next, inp2.pref);
      SSFwdDiff(inp2.next, inp2.pref, inp3.next, inp3.pref);
      var da :| da != [] && inp2.next == da + inp1.next && inp1.pref == Reverse(da) + inp2.pref;
      var db :| db != [] && inp3.next == db + inp2.next && inp2.pref == Reverse(db) + inp3.pref;
      var diff := db + da;
      assert inp3.next == diff + inp1.next;
      ReverseApp(db, da);
      assert inp1.pref == Reverse(diff) + inp3.pref;
      SSFwdDiff(inp1.next, inp1.pref, inp3.next, inp3.pref);
      assert inp1 == Input(inp1.next, inp1.pref) && inp3 == Input(inp3.next, inp3.pref);
    case Backward =>
      SSBwdDiff(inp1.next, inp1.pref, inp2.next, inp2.pref);
      SSBwdDiff(inp2.next, inp2.pref, inp3.next, inp3.pref);
      var da :| da != [] && inp1.next == da + inp2.next && inp2.pref == Reverse(da) + inp1.pref;
      var db :| db != [] && inp2.next == db + inp3.next && inp3.pref == Reverse(db) + inp2.pref;
      var diff := da + db;
      assert inp1.next == diff + inp3.next;
      ReverseApp(da, db);
      assert inp3.pref == Reverse(diff) + inp1.pref;
      SSBwdDiff(inp1.next, inp1.pref, inp3.next, inp3.pref);
      assert inp1 == Input(inp1.next, inp1.pref) && inp3 == Input(inp3.next, inp3.pref);
  }

  // Coq: ss_fwd_diff — induction on next2 (the structure of StrictSuffixForward).
  /** Structural characterization of forward `StrictSuffix`: it holds exactly when `next2`
      extends `next1` by some nonempty `diff`, with `pref1` correspondingly extending `pref2`
      by `Reverse(diff)`. Powers `StrictSuffixTrans`, `StrictAdvance`, and `AdvanceSuffix`. */
  lemma SSFwdDiff(next1: seq<char>, pref1: seq<char>, next2: seq<char>, pref2: seq<char>)
    ensures StrictSuffix(Input(next1, pref1), Input(next2, pref2), Forward)
        <==> (exists diff :: diff != [] && next2 == diff + next1 && pref1 == Reverse(diff) + pref2)
    decreases |next2|
  {
    var inp1 := Input(next1, pref1);
    if |next2| == 0 {
      forall diff | diff != [] && next2 == diff + next1 ensures false {
      }
    } else {
      var h := next2[0];
      var rest := next2[1..];
      assert next2 == [h] + rest;
      assert Reverse([h]) == [h];
      if Input(rest, [h] + pref2) == inp1 {
        assert StrictSuffix(inp1, Input(next2, pref2), Forward);   // StrictSuffixForward first branch
        assert rest == next1 && pref1 == [h] + pref2;
        assert next2 == [h] + next1 && pref1 == Reverse([h]) + pref2;   // RHS witness diff = [h]
      } else {
        SSFwdDiff(next1, pref1, rest, [h] + pref2);   // IH for (rest, [h]+pref2)
        assert StrictSuffix(inp1, Input(next2, pref2), Forward) == StrictSuffix(inp1, Input(rest, [h] + pref2), Forward);
        // RHS(next2) <==> RHS(rest, [h]+pref2)
        if exists diff :: diff != [] && next2 == diff + next1 && pref1 == Reverse(diff) + pref2 {
          var diff :| diff != [] && next2 == diff + next1 && pref1 == Reverse(diff) + pref2;
          assert (diff + next1)[0] == h;
          assert diff[0] == h;
          var diffp := diff[1..];
          assert diff == [h] + diffp;
          if diffp == [] {
            assert rest == next1 && pref1 == [h] + pref2;   // diff == [h]
            assert false;   // would make Input(rest,[h]+pref2) == inp1
          } else {
            assert rest == diffp + next1;
            assert Reverse(diff) == Reverse(diffp) + [h];
            assert pref1 == Reverse(diffp) + ([h] + pref2);   // RHS(rest,[h]+pref2) witness diffp
          }
        }
        if exists diffp :: diffp != [] && rest == diffp + next1 && pref1 == Reverse(diffp) + ([h] + pref2) {
          var diffp :| diffp != [] && rest == diffp + next1 && pref1 == Reverse(diffp) + ([h] + pref2);
          var diff := [h] + diffp;
          assert next2 == diff + next1;
          assert Reverse(diff) == Reverse(diffp) + [h];
          assert pref1 == Reverse(diff) + pref2;   // RHS(next2) witness diff
        }
      }
    }
  }

  // Coq: ss_bwd_diff — induction on pref2 (the structure of StrictSuffixBackward).
  /** Backward-direction mirror of `SSFwdDiff`. */
  lemma SSBwdDiff(next1: seq<char>, pref1: seq<char>, next2: seq<char>, pref2: seq<char>)
    ensures StrictSuffix(Input(next1, pref1), Input(next2, pref2), Backward)
        <==> (exists diff :: diff != [] && next1 == diff + next2 && pref2 == Reverse(diff) + pref1)
    decreases |pref2|
  {
    var inp1 := Input(next1, pref1);
    if |pref2| == 0 {
      forall diff | diff != [] && pref2 == Reverse(diff) + pref1 ensures false {
      }
    } else {
      var h := pref2[0];
      var rest := pref2[1..];
      assert pref2 == [h] + rest;
      assert Reverse([h]) == [h];
      if Input([h] + next2, rest) == inp1 {
        assert StrictSuffix(inp1, Input(next2, pref2), Backward);
        assert next1 == [h] + next2 && pref1 == rest;
        assert next1 == [h] + next2 && pref2 == Reverse([h]) + pref1;   // RHS witness diff = [h]
      } else {
        SSBwdDiff(next1, pref1, [h] + next2, rest);   // IH for ([h]+next2, rest)
        assert StrictSuffix(inp1, Input(next2, pref2), Backward) == StrictSuffix(inp1, Input([h] + next2, rest), Backward);
        if exists diff :: diff != [] && next1 == diff + next2 && pref2 == Reverse(diff) + pref1 {
          var diff :| diff != [] && next1 == diff + next2 && pref2 == Reverse(diff) + pref1;
          // pref2 == Reverse(diff) + pref1, and pref2 == [h] + rest; Reverse(diff) ends... use last element
          assert |diff| >= 1;
          var diffp := diff[..|diff| - 1];
          var last := diff[|diff| - 1];
          assert diff == diffp + [last];
          ReverseSnoc(diffp, last);
          assert Reverse(diff) == [last] + Reverse(diffp);   // reverse of (diffp + [last])
          assert pref2 == [last] + (Reverse(diffp) + pref1);
          assert last == h;
          if diffp == [] {
            assert diff == [h];
            assert next1 == [h] + next2 && pref1 == rest;
            assert false;
          } else {
            assert next1 == diffp + ([h] + next2);    // next1 = diff+next2 = diffp+[h]+next2
            assert rest == Reverse(diffp) + pref1;     // RHS([h]+next2, rest) witness diffp
          }
        }
        if exists diffp :: diffp != [] && next1 == diffp + ([h] + next2) && rest == Reverse(diffp) + pref1 {
          var diffp :| diffp != [] && next1 == diffp + ([h] + next2) && rest == Reverse(diffp) + pref1;
          var diff := diffp + [h];
          assert next1 == diff + next2;
          ReverseSnoc(diffp, h);
          assert Reverse(diff) == [h] + Reverse(diffp);   // reverse of (diffp + [h])
          assert pref2 == Reverse(diff) + pref1;   // RHS(next2,pref2) witness diff
        }
      }
    }
  }

  // Coq: strict_advance
  /** Strict-suffixing is stable under stepping both sides in lockstep: if `inp1` is a strict
      suffix of `inp2` and `inp1` can advance, then `inp2` can advance too, and the
      strict-suffix relationship is preserved between the two results. */
  lemma StrictAdvance(inp1: Input, inp2: Input, dir: Direction, nextinp1: Input)
    requires StrictSuffix(inp1, inp2, dir)
    requires AdvanceInput(inp1, dir) == Some(nextinp1)
    ensures exists nextinp2 :: AdvanceInput(inp2, dir) == Some(nextinp2)
                            && StrictSuffix(nextinp1, nextinp2, dir)
  {
    match dir
    case Forward =>
      var n1 := inp1.next;
      SSFwdDiff(inp1.next, inp1.pref, inp2.next, inp2.pref);
      var diff :| diff != [] && inp2.next == diff + n1 && inp1.pref == Reverse(diff) + inp2.pref;
      assert |n1| > 0 && nextinp1 == Input(n1[1..], [n1[0]] + inp1.pref);
      assert inp2.next[0] == diff[0] && inp2.next[1..] == diff[1..] + n1;
      var nextinp2 := AdvanceInput(inp2, Forward).value;
      assert nextinp2 == Input(diff[1..] + n1, [diff[0]] + inp2.pref);
      assert n1 == [n1[0]] + n1[1..] && diff == [diff[0]] + diff[1..];
      var diffp := diff[1..] + [n1[0]];
      assert nextinp2.next == diffp + nextinp1.next;
      ReverseSnoc(diff[1..], n1[0]);
      assert nextinp1.pref == Reverse(diffp) + nextinp2.pref;
      SSFwdDiff(nextinp1.next, nextinp1.pref, nextinp2.next, nextinp2.pref);
      assert nextinp1 == Input(nextinp1.next, nextinp1.pref) && nextinp2 == Input(nextinp2.next, nextinp2.pref);
      assert AdvanceInput(inp2, Forward) == Some(nextinp2) && StrictSuffix(nextinp1, nextinp2, Forward);
    case Backward =>
      var p1 := inp1.pref;
      SSBwdDiff(inp1.next, inp1.pref, inp2.next, inp2.pref);
      var diff :| diff != [] && inp1.next == diff + inp2.next && inp2.pref == Reverse(diff) + p1;
      assert |p1| > 0 && nextinp1 == Input([p1[0]] + inp1.next, p1[1..]);
      var dlast := diff[|diff| - 1];
      var dinit := diff[..|diff| - 1];
      assert diff == dinit + [dlast];
      ReverseSnoc(dinit, dlast);                           // Reverse(diff) == [dlast] + Reverse(dinit)
      assert inp2.pref[0] == dlast && inp2.pref[1..] == Reverse(dinit) + p1;
      var nextinp2 := AdvanceInput(inp2, Backward).value;
      assert nextinp2 == Input([dlast] + inp2.next, Reverse(dinit) + p1);
      assert p1 == [p1[0]] + p1[1..];
      var diffp := [p1[0]] + dinit;
      assert nextinp1.next == [p1[0]] + (dinit + ([dlast] + inp2.next));
      assert nextinp2.next == [dlast] + inp2.next;
      assert nextinp1.next == diffp + nextinp2.next;
      assert nextinp2.pref == Reverse(diffp) + nextinp1.pref;   // Reverse([p1[0]]+dinit) = Reverse(dinit)+[p1[0]]
      SSBwdDiff(nextinp1.next, nextinp1.pref, nextinp2.next, nextinp2.pref);
      assert nextinp1 == Input(nextinp1.next, nextinp1.pref) && nextinp2 == Input(nextinp2.next, nextinp2.pref);
      assert AdvanceInput(inp2, Backward) == Some(nextinp2) && StrictSuffix(nextinp1, nextinp2, Backward);
  }

  // Coq: advance_suffix
  /** Advancing `inp` to `inpnext` narrows the gap to a strict suffix `inpsuf` by exactly one
      step: either `inpnext` catches up to equal `inpsuf`, or `inpsuf` is still a strict
      suffix of `inpnext`. This is what licenses re-checking the `Acheck` progress guard after
      each quantifier iteration. */
  lemma AdvanceSuffix(inp: Input, inpnext: Input, inpsuf: Input, dir: Direction)
    requires StrictSuffix(inpsuf, inp, dir)
    requires AdvanceInput(inp, dir) == Some(inpnext)
    ensures inpnext == inpsuf || StrictSuffix(inpsuf, inpnext, dir)
  {
    match dir
    case Forward =>
      var n := inp.next;
      SSFwdDiff(inpsuf.next, inpsuf.pref, inp.next, inp.pref);
      var diff :| diff != [] && inp.next == diff + inpsuf.next && inpsuf.pref == Reverse(diff) + inp.pref;
      assert |n| > 0 && inpnext == Input(n[1..], [n[0]] + inp.pref);
      assert diff[0] == n[0];
      if |diff| == 1 {
        assert diff == [n[0]];
        assert n[1..] == inpsuf.next && inpsuf.pref == [n[0]] + inp.pref;
        assert inpnext == inpsuf;
      } else {
        var diffp := diff[1..];
        assert diff == [n[0]] + diffp && diffp != [];
        assert n[1..] == diffp + inpsuf.next;
        assert inpsuf.pref == Reverse(diffp) + ([n[0]] + inp.pref);
        SSFwdDiff(inpsuf.next, inpsuf.pref, inpnext.next, inpnext.pref);
        assert inpsuf == Input(inpsuf.next, inpsuf.pref) && inpnext == Input(inpnext.next, inpnext.pref);
      }
    case Backward =>
      var p := inp.pref;
      SSBwdDiff(inpsuf.next, inpsuf.pref, inp.next, inp.pref);
      var diff :| diff != [] && inpsuf.next == diff + inp.next && inp.pref == Reverse(diff) + inpsuf.pref;
      assert |p| > 0 && inpnext == Input([p[0]] + inp.next, p[1..]);
      var dlast := diff[|diff| - 1];
      var dinit := diff[..|diff| - 1];
      assert diff == dinit + [dlast];
      ReverseSnoc(dinit, dlast);                       // Reverse(diff) == [dlast] + Reverse(dinit)
      assert p[0] == dlast && p[1..] == Reverse(dinit) + inpsuf.pref;
      if |diff| == 1 {
        assert dinit == [] && diff == [dlast];
        assert inpsuf.next == [dlast] + inp.next;
        assert inpnext.next == [p[0]] + inp.next && p[0] == dlast;
        assert inpnext == inpsuf;
      } else {
        assert dinit != [];
        assert inpsuf.next == dinit + ([dlast] + inp.next);   // diff+inp.next
        assert inpnext.next == [dlast] + inp.next;
        assert inpsuf.next == dinit + inpnext.next;
        assert inpnext.pref == Reverse(dinit) + inpsuf.pref;   // == p[1..]
        SSBwdDiff(inpsuf.next, inpsuf.pref, inpnext.next, inpnext.pref);
        assert inpsuf == Input(inpsuf.next, inpsuf.pref) && inpnext == Input(inpnext.next, inpnext.pref);
      }
  }
}
