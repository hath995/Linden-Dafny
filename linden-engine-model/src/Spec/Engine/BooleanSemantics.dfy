// Mirror of Engine/BooleanSemantics.v.
// Alternative semantics `bool_tree` using a LoopBool (can-we-exit-a-loop) instead of comparing
// strings at checks, and the encoding invariant `bool_encoding` linking the two. Forward-only,
// no group map. bool_tree is a least predicate (same alternating recursion as is_tree); the
// encoding invariant is structurally recursive on the action list.
include "PikeSubset.dfy"

/** An intermediate semantics between `IsTree`/`ComputeTree` and the `PikeVM`: the empty-loop
    "did the input advance?" check (a full input comparison) is replaced by a single `LoopBool`
    flag. `BoolTree` is the tree relation restated over this flag; `BoolEncoding` says when the
    flag correctly reflects the real check, so that `BoolTree` and `IsTree` agree
    (`BoolTreeIsTreeEquiv`). This is the bridge that lets `TreeRep`/`PikeEquiv` relate trees to
    bytecode without carrying whole strings around. */
module BooleanSemantics {
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
  import opened FunctionalSemantics
  import opened ComputeIsTree
  import opened FunctionalUtils
  import opened PikeSubset

  // Coq: Inductive LoopBool := CanExit | CannotExit.
  /** Whether the current position can still "exit" a quantifier's empty-iteration guard.
      `CannotExit` means an iteration just started at this input position (so stopping here
      without progress is forbidden); `CanExit` means it's safe to fall through. */
  datatype LoopBool = CanExit | CannotExit

  // Coq: bool_tree (forward-only; no group map; over the pike subset).
  /** `IsTree` restated for `PikeRegex` action stacks, `Forward` direction only, with the
      empty-loop check reduced to the `LoopBool` flag `b` instead of a real `Acheck` input
      comparison. Same tree shapes as `IsTree`; a `least predicate` for the same reason
      (mirrors the alternating action/regex recursion). */
  least predicate BoolTree(rer: RegExpRecord, acts: Actions, inp: Input, b: LoopBool, t: Tree)
  {
    if |acts| == 0 then t == Match
    else
      var cont := acts[1..];
      match acts[0]
      case Acheck(strcheck) =>
        if b == CanExit then
          (match t case Progress(tc) => BoolTree(rer, cont, inp, CanExit, tc) case _ => false)
        else
          t == Mismatch
      case Aclose(gid) =>
        (match t case GroupActionT(g, tc) => g == Close(gid) && BoolTree(rer, cont, inp, b, tc) case _ => false)
      case Areg(r) =>
        match r
        case Epsilon => BoolTree(rer, cont, inp, b, t)
        case Character(cd) =>
          (match ReadChar(rer, cd, inp, Forward)
           case None => t == Mismatch
           case Some(pair) => (match t case Read(c, tc) => c == pair.0 && BoolTree(rer, cont, pair.1, CanExit, tc) case _ => false))
        case Disjunction(r1, r2) =>
          (match t case Choice(ta, tb) => BoolTree(rer, [Areg(r1)] + cont, inp, b, ta) && BoolTree(rer, [Areg(r2)] + cont, inp, b, tb) case _ => false)
        case Sequence(r1, r2) =>
          BoolTree(rer, [Areg(r1), Areg(r2)] + cont, inp, b, t)
        case Quantified(greedy, min, delta, r1) =>
          var gidl := DefGroups(r1);
          if min > 0 then
            (match t case GroupActionT(g, tc) => g == Reset(gidl) && BoolTree(rer, [Areg(r1), Areg(Quantified(greedy, min - 1, delta, r1))] + cont, inp, b, tc) case _ => false)
          else if delta == NN(0) then
            BoolTree(rer, cont, inp, b, t)
          else
            (match t
             case Choice(ta, tb) =>
               var itert := if greedy then ta else tb;
               var skipt := if greedy then tb else ta;
               (match itert
                case GroupActionT(g, ti) =>
                  g == Reset(gidl)
                  && BoolTree(rer, [Areg(r1), Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r1))] + cont, inp, CannotExit, ti)
                  && BoolTree(rer, cont, inp, b, skipt)
                case _ => false)
             case _ => false)
        case Group(gid, r1) =>
          (match t case GroupActionT(g, tc) => g == Open(gid) && BoolTree(rer, [Areg(r1), Aclose(gid)] + cont, inp, b, tc) case _ => false)
        case AnchorR(a) =>
          if AnchorSatisfied(rer, a, inp) then
            (match t case AnchorPass(a2, tc) => a2 == a && BoolTree(rer, cont, inp, b, tc) case _ => false)
          else
            t == Mismatch
        case LookaroundR(_, _) => false
        case Backreference(_) => false
  }

  // Coq: bool_encoding — the boolean encodes whether the current input can exit, relative to the
  // checks in the action stack. Structurally recursive on the action list.
  /** The soundness condition for `b`: it holds exactly when `b` correctly summarizes, for every
      `Acheck` remaining in `act`, whether `str` is still at that check's recorded position
      (`CannotExit`) or has strictly advanced past it (`CanExit`). `BoolTree` is only faithful to
      `IsTree` under an input/action pair satisfying this. */
  predicate BoolEncoding(b: LoopBool, str: Input, act: Actions)
    decreases |act|
  {
    if |act| == 0 then true
    else
      var rest := act[1..];
      match act[0]
      case Areg(_) => BoolEncoding(b, str, rest)
      case Aclose(_) => BoolEncoding(b, str, rest)
      case Acheck(head) =>
        if b == CanExit then SS.StrictSuffix(str, head, Forward) && BoolEncoding(CanExit, str, rest)
        else head == str && (exists bb :: BoolEncoding(bb, str, rest))
  }

  // Coq: encode_next
  /** Pushing an `Areg` action onto the stack doesn't change `BoolEncoding` — regex actions carry
      no `Acheck`. */
  lemma EncodeNext(b: LoopBool, inp: Input, cont: Actions, r: Regex)
    ensures BoolEncoding(b, inp, [Areg(r)] + cont) <==> BoolEncoding(b, inp, cont)
  {
    assert ([Areg(r)] + cont)[0] == Areg(r);
    assert ([Areg(r)] + cont)[1..] == cont;
  }

  // Coq: encode_close
  /** Pushing an `Aclose` action onto the stack doesn't change `BoolEncoding`, for the same reason
      as `EncodeNext`. */
  lemma EncodeClose(b: LoopBool, inp: Input, cont: Actions, g: GroupId)
    ensures BoolEncoding(b, inp, [Aclose(g)] + cont) <==> BoolEncoding(b, inp, cont)
  {
    assert ([Aclose(g)] + cont)[0] == Aclose(g);
    assert ([Aclose(g)] + cont)[1..] == cont;
  }

  // Coq: encoding_different
  /** If the next `Acheck` on the stack was recorded at a different input than the current one,
      `BoolEncoding` forces `b == CanExit` — the position must have already moved past that
      check. */
  lemma EncodingDifferent(b: LoopBool, str: Input, strcheck: Input, cont: Actions)
    requires BoolEncoding(b, str, [Acheck(strcheck)] + cont)
    requires str != strcheck
    ensures b == CanExit
  {
    assert ([Acheck(strcheck)] + cont)[0] == Acheck(strcheck);
    assert ([Acheck(strcheck)] + cont)[1..] == cont;
  }

  // Coq: encoding_same
  /** If the next `Acheck` on the stack was recorded at exactly the current input, `BoolEncoding`
      forces `b == CannotExit` (a strict suffix of itself is impossible, so `CanExit` is ruled
      out). */
  lemma EncodingSame(b: LoopBool, str: Input, cont: Actions)
    requires BoolEncoding(b, str, [Acheck(str)] + cont)
    ensures b == CannotExit
  {
    assert ([Acheck(str)] + cont)[0] == Acheck(str);
    assert ([Acheck(str)] + cont)[1..] == cont;
    if b == CanExit {
      assert SS.StrictSuffix(str, str, Forward);
      SS.SSNeq(str, str, Forward);  // contradiction: strict suffix of itself
    }
  }

  // ===== Axiomatized core theorems (inductions over least predicates / bool_encoding + ss). =====
  // TODO: discharge. See PROGRESS.md Axiom Debt.

  // Coq: true_encoding
  /** Reading a character always makes `CanExit` a valid encoding at the new position: any
      `Acheck` still pending was recorded at or before the old position, and the read moved
      strictly past it. */
  lemma TrueEncoding(str: seq<char>, c: char, pref: seq<char>, cont: Actions, b: LoopBool)
    requires BoolEncoding(b, Input([c] + str, pref), cont)
    ensures BoolEncoding(CanExit, Input(str, [c] + pref), cont)
    decreases cont
  {
    var prevInp := Input([c] + str, pref);
    var newInp := Input(str, [c] + pref);
    assert AdvanceInput(prevInp, Forward) == Some(newInp);
    SS.ReadSuffix(prevInp, Forward, newInp);  // StrictSuffix(newInp, prevInp, Forward)
    if |cont| == 0 {
    } else {
      var rest := cont[1..];
      match cont[0]
      case Areg(_) => TrueEncoding(str, c, pref, rest, b);
      case Aclose(_) => TrueEncoding(str, c, pref, rest, b);
      case Acheck(head) =>
        if b == CanExit {
          SS.StrictSuffixTrans(newInp, prevInp, head, Forward);  // StrictSuffix(newInp, head, Forward)
          TrueEncoding(str, c, pref, rest, CanExit);
        } else {
          var bb :| BoolEncoding(bb, prevInp, rest);
          TrueEncoding(str, c, pref, rest, bb);
        }
    }
  }

  // Coq: encoding_suffix
  /** Given a valid `BoolEncoding`, the current input is either exactly at any `Acheck(chk)`
      still on the stack, or strictly past it — never before it. */
  lemma EncodingSuffix(b: LoopBool, inp: Input, act: Actions, chk: Input)
    requires BoolEncoding(b, inp, act)
    requires Acheck(chk) in act
    ensures inp == chk || SS.StrictSuffix(inp, chk, Forward)
    decreases act
  {
    var rest := act[1..];
    assert act == [act[0]] + rest;
    match act[0]
    case Areg(_) =>
      assert Acheck(chk) in rest;
      EncodingSuffix(b, inp, rest, chk);
    case Aclose(_) =>
      assert Acheck(chk) in rest;
      EncodingSuffix(b, inp, rest, chk);
    case Acheck(head) =>
      if Acheck(chk) in rest {
        if b == CanExit {
          EncodingSuffix(CanExit, inp, rest, chk);
        } else {
          var bb :| BoolEncoding(bb, inp, rest);
          EncodingSuffix(bb, inp, rest, chk);
        }
      } else {
        assert head == chk;  // Acheck(chk) in act but not in rest ⟹ act[0] == Acheck(chk)
      }
  }

  // Fuel-induction version of encode_equal: a pike-action tree computed by ComputeTree (forward),
  // under a valid bool_encoding, is a bool_tree. Mirrors ComputeTree, threading BoolEncoding.
  /** The executable workhorse behind `EncodeEqual`: whatever tree `ComputeTree` produces for a
      `PikeRegex` action stack, under a valid `BoolEncoding`, is also the `BoolTree` for the same
      stack and flag. */
  lemma ComputeBoolTree(rer: RegExpRecord, act: Actions, inp: Input, gm: GroupMap, b: LoopBool, fuel: nat, t: Tree)
    requires PikeActions(act)
    requires BoolEncoding(b, inp, act)
    requires ComputeTree(rer, act, inp, gm, Forward, fuel) == Some(t)
    ensures BoolTree(rer, act, inp, b, t)
    decreases fuel
  {
    var f := fuel - 1;
    if |act| == 0 {
    } else {
      var cont := act[1..];
      PikeActionsTail(act);
      assert act == [act[0]] + cont;
      PikeActionsConsIff(act[0], cont);
      match act[0]
      case Acheck(strcheck) =>
        EncodingSuffix(b, inp, act, strcheck);  // inp == strcheck || StrictSuffix(inp, strcheck, F)
        if SS.IsStrictSuffix(inp, strcheck, Forward) {
          assert SS.StrictSuffix(inp, strcheck, Forward);
          SS.SSNeq(inp, strcheck, Forward);                  // inp != strcheck
          EncodingDifferent(b, inp, strcheck, cont);          // b == CanExit
          assert BoolEncoding(CanExit, inp, cont);
          var sub := ComputeTree(rer, cont, inp, gm, Forward, f);
          ComputeBoolTree(rer, cont, inp, gm, CanExit, f, sub.value);
        } else {
          assert !SS.StrictSuffix(inp, strcheck, Forward);
          assert inp == strcheck;
          EncodingSame(b, inp, cont);                         // b == CannotExit
        }
      case Aclose(gid) =>
        EncodeClose(b, inp, cont, gid);                       // BoolEncoding(b, inp, cont)
        var gm' := GMClose(Idx(inp), gid, gm);
        var sub := ComputeTree(rer, cont, inp, gm', Forward, f);
        ComputeBoolTree(rer, cont, inp, gm', b, f, sub.value);
      case Areg(r) =>
        assert PikeRegex(r);
        match r
        case Epsilon =>
          EncodeNext(b, inp, cont, Epsilon);
          ComputeBoolTree(rer, cont, inp, gm, b, f, t);
        case Character(cd) => {
          EncodeNext(b, inp, cont, Character(cd));            // BoolEncoding(b, inp, cont)
          match ReadChar(rer, cd, inp, Forward) {
            case None =>
            case Some(pair) =>
              assert inp.next == [inp.next[0]] + inp.next[1..];
              assert inp == Input([inp.next[0]] + inp.next[1..], inp.pref);
              assert pair.1 == Input(inp.next[1..], [inp.next[0]] + inp.pref);
              TrueEncoding(inp.next[1..], inp.next[0], inp.pref, cont, b);  // BoolEncoding(CanExit, pair.1, cont)
              var sub := ComputeTree(rer, cont, pair.1, gm, Forward, f);
              ComputeBoolTree(rer, cont, pair.1, gm, CanExit, f, sub.value);
          }
        }
        case Disjunction(r1, r2) =>
          PikeActionsConsIff(Areg(r1), cont);
          PikeActionsConsIff(Areg(r2), cont);
          EncodeNext(b, inp, cont, r1);
          EncodeNext(b, inp, cont, r2);
          var s1 := ComputeTree(rer, [Areg(r1)] + cont, inp, gm, Forward, f);
          var s2 := ComputeTree(rer, [Areg(r2)] + cont, inp, gm, Forward, f);
          ComputeBoolTree(rer, [Areg(r1)] + cont, inp, gm, b, f, s1.value);
          ComputeBoolTree(rer, [Areg(r2)] + cont, inp, gm, b, f, s2.value);
        case Sequence(r1, r2) =>
          var na := SeqList(r1, r2, Forward) + cont;
          assert na == [Areg(r1)] + ([Areg(r2)] + cont);
          assert PikeActions(na) by { PikeActionsConsIff(Areg(r2), cont); PikeActionsConsIff(Areg(r1), [Areg(r2)] + cont); }
          assert BoolEncoding(b, inp, na) by { EncodeNext(b, inp, cont, r2); EncodeNext(b, inp, [Areg(r2)] + cont, r1); }
          var sub := ComputeTree(rer, na, inp, gm, Forward, f);
          ComputeBoolTree(rer, na, inp, gm, b, f, sub.value);
        case Quantified(greedy, min, delta, r1) =>
          if min > 0 {
            // forced iteration: Reset then [body, Quantified(min-1)], flag unchanged
            var gidl := DefGroups(r1);
            var quant := Quantified(greedy, min - 1, delta, r1);
            var na := [Areg(r1), Areg(quant)] + cont;
            var gm' := GMReset(gidl, gm);
            assert PikeActions(na) by {
              assert na == [Areg(r1)] + ([Areg(quant)] + cont);
              assert PikeRegex(quant);
              PikeActionsConsIff(Areg(quant), cont);
              PikeActionsConsIff(Areg(r1), [Areg(quant)] + cont);
            }
            assert BoolEncoding(b, inp, na) by {
              assert na == [Areg(r1)] + ([Areg(quant)] + cont);
              EncodeNext(b, inp, cont, quant);
              EncodeNext(b, inp, [Areg(quant)] + cont, r1);
            }
            var sub := ComputeTree(rer, na, inp, gm', Forward, f);
            ComputeBoolTree(rer, na, inp, gm', b, f, sub.value);
            return;
          }
          if delta == NN(0) {
            // spent: epsilon-continue
            assert BoolEncoding(b, inp, cont) by { EncodeNext(b, inp, cont, Quantified(greedy, min, delta, r1)); }
            var sub := ComputeTree(rer, cont, inp, gm, Forward, f);
            ComputeBoolTree(rer, cont, inp, gm, b, f, sub.value);
            return;
          }
          var gidl := DefGroups(r1);
          var quant := Quantified(greedy, 0, NoiPred(delta), r1);
          var na := [Areg(r1), Acheck(inp), Areg(quant)] + cont;
          var gm' := GMReset(gidl, gm);
          assert PikeRegex(quant);
          assert PikeActions(na) by {
            assert na == [Areg(r1)] + ([Acheck(inp)] + ([Areg(quant)] + cont));
            PikeActionsConsIff(Areg(quant), cont);
            PikeActionsConsIff(Acheck(inp), [Areg(quant)] + cont);
            PikeActionsConsIff(Areg(r1), [Acheck(inp)] + ([Areg(quant)] + cont));
          }
          assert BoolEncoding(b, inp, cont) by { EncodeNext(b, inp, cont, Quantified(greedy, min, delta, r1)); }
          assert BoolEncoding(CannotExit, inp, na) by {
            assert na == [Areg(r1)] + ([Acheck(inp)] + ([Areg(quant)] + cont));
            EncodeNext(b, inp, cont, quant);                               // BoolEncoding(b, inp, [Areg quant]+cont)
            assert ([Acheck(inp)] + ([Areg(quant)] + cont))[0] == Acheck(inp);
            assert ([Acheck(inp)] + ([Areg(quant)] + cont))[1..] == [Areg(quant)] + cont;
            assert BoolEncoding(CannotExit, inp, [Acheck(inp)] + ([Areg(quant)] + cont));  // cons_false, head==inp, witness bb := b
            EncodeNext(CannotExit, inp, [Acheck(inp)] + ([Areg(quant)] + cont), r1);
          }
          var siter := ComputeTree(rer, na, inp, gm', Forward, f);
          var sskip := ComputeTree(rer, cont, inp, gm, Forward, f);
          ComputeBoolTree(rer, na, inp, gm', CannotExit, f, siter.value);
          ComputeBoolTree(rer, cont, inp, gm, b, f, sskip.value);
        case Group(gid, r1) =>
          var na := [Areg(r1), Aclose(gid)] + cont;
          var gm' := GMOpen(Idx(inp), gid, gm);
          assert PikeActions(na) by {
            assert na == [Areg(r1)] + ([Aclose(gid)] + cont);
            PikeActionsConsIff(Aclose(gid), cont);
            PikeActionsConsIff(Areg(r1), [Aclose(gid)] + cont);
          }
          assert BoolEncoding(b, inp, na) by {
            assert na == [Areg(r1)] + ([Aclose(gid)] + cont);
            EncodeClose(b, inp, cont, gid);
            EncodeNext(b, inp, [Aclose(gid)] + cont, r1);
          }
          var sub := ComputeTree(rer, na, inp, gm', Forward, f);
          ComputeBoolTree(rer, na, inp, gm', b, f, sub.value);
        case AnchorR(a) =>
          if AnchorSatisfied(rer, a, inp) {
            EncodeNext(b, inp, cont, AnchorR(a));
            var sub := ComputeTree(rer, cont, inp, gm, Forward, f);
            ComputeBoolTree(rer, cont, inp, gm, b, f, sub.value);
          }
        case LookaroundR(lk, r1) =>
        case Backreference(gid) =>
    }
  }

  // Coq: encode_equal — the key equivalence direction (is_tree ⟹ bool_tree under the encoding).
  /** Whenever `IsTree` produces `t` for a `PikeRegex` action stack, and `b`/`inp` satisfy
      `BoolEncoding` for that stack, `t` is also the `BoolTree` for `acts`/`inp`/`b`. Goes via
      `ComputeTree` and `ComputeBoolTree` since `IsTree` itself isn't executable. */
  lemma EncodeEqual(rer: RegExpRecord, inp: Input, cont: Actions, b: LoopBool, t: Tree, gm: GroupMap)
    requires PikeActions(cont)
    requires BoolEncoding(b, inp, cont)
    requires IsTree(rer, cont, inp, gm, Forward, t)
    ensures BoolTree(rer, cont, inp, b, t)
  {
    var fuel := ActionsFuel(cont, inp, Forward) + 1;
    FunctionalTerminates(rer, cont, inp, gm, Forward, fuel);
    var opt := ComputeTree(rer, cont, inp, gm, Forward, fuel);
    ComputeIsTreeThm(rer, cont, inp, gm, Forward, fuel, opt.value);
    IsTreeDeterm(rer, cont, inp, gm, Forward, t, opt.value);  // t == opt.value
    ComputeBoolTree(rer, cont, inp, gm, b, fuel, opt.value);
  }

  // Coq: subset_semantics — induction over the BoolTree least predicate.
  /** Any tree produced by `BoolTree` for a `PikeActions` stack is a `PikeSubtree` — it only ever
      builds the shapes the PikeVM engine actually supports (no lookaround/anchor/backreference
      nodes). */
  least lemma SubsetSemantics(rer: RegExpRecord, acts: Actions, t: Tree, inp: Input, b: LoopBool)
    requires PikeActions(acts)
    requires BoolTree(rer, acts, inp, b, t)
    ensures PikeSubtree(t)
  {
    if |acts| == 0 {
    } else {
      var cont := acts[1..];
      PikeActionsTail(acts);
      assert acts == [acts[0]] + cont;
      PikeActionsConsIff(acts[0], cont);
      match acts[0]
      case Acheck(strcheck) =>
        if b == CanExit {
          match t
          case Progress(tc) => SubsetSemantics(rer, cont, tc, inp, CanExit);
          case _ =>
        }
      case Aclose(gid) => {
        match t {
          case GroupActionT(g, tc) => SubsetSemantics(rer, cont, tc, inp, b);
          case _ =>
        }
      }
      case Areg(r) =>
        assert PikeRegex(r);
        match r
        case Epsilon => SubsetSemantics(rer, cont, t, inp, b);
        case Character(cd) => {
          match ReadChar(rer, cd, inp, Forward) {
            case None =>
            case Some(pair) =>
              match t {
                case Read(c, tc) => SubsetSemantics(rer, cont, tc, pair.1, CanExit);
                case _ =>
              }
          }
        }
        case Disjunction(r1, r2) => {
          PikeActionsConsIff(Areg(r1), cont);
          PikeActionsConsIff(Areg(r2), cont);
          match t {
            case Choice(ta, tb) =>
              SubsetSemantics(rer, [Areg(r1)] + cont, ta, inp, b);
              SubsetSemantics(rer, [Areg(r2)] + cont, tb, inp, b);
            case _ =>
          }
        }
        case Sequence(r1, r2) => {
          var na := [Areg(r1), Areg(r2)] + cont;
          assert na == [Areg(r1)] + ([Areg(r2)] + cont);
          assert PikeActions(na) by { PikeActionsConsIff(Areg(r2), cont); PikeActionsConsIff(Areg(r1), [Areg(r2)] + cont); }
          SubsetSemantics(rer, na, t, inp, b);
        }
        case Quantified(greedy, min, delta, r1) => {
          var gidl := DefGroups(r1);
          if min > 0 {
            var quant := Quantified(greedy, min - 1, delta, r1);
            var na := [Areg(r1), Areg(quant)] + cont;
            assert PikeActions(na) by {
              assert na == [Areg(r1)] + ([Areg(quant)] + cont);
              assert PikeRegex(quant);
              PikeActionsConsIff(Areg(quant), cont);
              PikeActionsConsIff(Areg(r1), [Areg(quant)] + cont);
            }
            match t {
              case GroupActionT(g, tc) =>
                SubsetSemantics(rer, na, tc, inp, b);
              case _ =>
            }
          } else if delta == NN(0) {
            SubsetSemantics(rer, cont, t, inp, b);
          } else {
            var quant := Quantified(greedy, 0, NoiPred(delta), r1);
            var na := [Areg(r1), Acheck(inp), Areg(quant)] + cont;
            assert PikeRegex(quant);
            assert PikeActions(na) by {
              assert na == [Areg(r1)] + ([Acheck(inp)] + ([Areg(quant)] + cont));
              PikeActionsConsIff(Areg(quant), cont);
              PikeActionsConsIff(Acheck(inp), [Areg(quant)] + cont);
              PikeActionsConsIff(Areg(r1), [Acheck(inp)] + ([Areg(quant)] + cont));
            }
            match t {
              case Choice(ta, tb) =>
                var itert := if greedy then ta else tb;
                var skipt := if greedy then tb else ta;
                match itert {
                  case GroupActionT(g, ti) =>
                    SubsetSemantics(rer, na, ti, inp, CannotExit);
                    SubsetSemantics(rer, cont, skipt, inp, b);
                  case _ =>
                }
              case _ =>
            }
          }
        }
        case Group(gid, r1) => {
          var na := [Areg(r1), Aclose(gid)] + cont;
          assert PikeActions(na) by {
            assert na == [Areg(r1)] + ([Aclose(gid)] + cont);
            PikeActionsConsIff(Aclose(gid), cont);
            PikeActionsConsIff(Areg(r1), [Aclose(gid)] + cont);
          }
          match t {
            case GroupActionT(g, tc) => SubsetSemantics(rer, na, tc, inp, b);
            case _ =>
          }
        }
        case AnchorR(a) =>
          if AnchorSatisfied(rer, a, inp) {
            match t {
              case AnchorPass(a2, tc) => SubsetSemantics(rer, cont, tc, inp, b);
              case _ =>
            }
          }
        case LookaroundR(lk, r1) =>
        case Backreference(gid) =>
    }
  }

  // Coq: bool_tree_determ — recursive determinism over the lex measure (TreeSize, ActionsRegexSize),
  // unfolding both BoolTree hypotheses (the ==> body direction holds for least predicates).
  /** `BoolTree` is deterministic: the same action stack, input, and flag can only produce one
      tree. */
  lemma BoolTreeDeterm(rer: RegExpRecord, acts: Actions, i: Input, b: LoopBool, t1: Tree, t2: Tree)
    requires BoolTree(rer, acts, i, b, t1)
    requires BoolTree(rer, acts, i, b, t2)
    ensures t1 == t2
    decreases TreeSize(t1), ActionsRegexSize(acts)
  {
    if |acts| == 0 {
    } else {
      var cont := acts[1..];
      match acts[0]
      case Acheck(strcheck) =>
        if b == CanExit {
          match t1 { case Progress(tc1) => match t2 { case Progress(tc2) => BoolTreeDeterm(rer, cont, i, CanExit, tc1, tc2); case _ => } case _ => }
        }
      case Aclose(gid) =>
        match t1 { case GroupActionT(g1, tc1) => match t2 { case GroupActionT(g2, tc2) => BoolTreeDeterm(rer, cont, i, b, tc1, tc2); case _ => } case _ => }
      case Areg(r) =>
        match r
        case Epsilon => BoolTreeDeterm(rer, cont, i, b, t1, t2);
        case Character(cd) => {
          match ReadChar(rer, cd, i, Forward) {
            case None =>
            case Some(pair) =>
              match t1 { case Read(c1, tc1) => match t2 { case Read(c2, tc2) => BoolTreeDeterm(rer, cont, pair.1, CanExit, tc1, tc2); case _ => } case _ => }
          }
        }
        case Disjunction(r1, r2) => {
          match t1 { case Choice(ta1, tb1) => match t2 { case Choice(ta2, tb2) => {
            BoolTreeDeterm(rer, [Areg(r1)] + cont, i, b, ta1, ta2);
            BoolTreeDeterm(rer, [Areg(r2)] + cont, i, b, tb1, tb2);
          } case _ => } case _ => }
        }
        case Sequence(r1, r2) => {
          assert ([Areg(r1), Areg(r2)] + cont)[1..] == [Areg(r2)] + cont;
          assert ([Areg(r2)] + cont)[1..] == cont;
          assert acts == [Areg(Sequence(r1, r2))] + cont;
          assert ActionsRegexSize([Areg(r1), Areg(r2)] + cont) == RegexSize(r1) + RegexSize(r2) + ActionsRegexSize(cont);
          assert ActionsRegexSize(acts) == RegexSize(Sequence(r1, r2)) + ActionsRegexSize(cont);
          BoolTreeDeterm(rer, [Areg(r1), Areg(r2)] + cont, i, b, t1, t2);
        }
        case Quantified(greedy, min, delta, r1) => {
          var gidl := DefGroups(r1);
          if min > 0 {
            match t1 { case GroupActionT(g1, tc1) => match t2 { case GroupActionT(g2, tc2) =>
              BoolTreeDeterm(rer, [Areg(r1), Areg(Quantified(greedy, min - 1, delta, r1))] + cont, i, b, tc1, tc2);
            case _ => } case _ => }
          } else if delta == NN(0) {
            BoolTreeDeterm(rer, cont, i, b, t1, t2);
          } else {
            var iterActs := [Areg(r1), Acheck(i), Areg(Quantified(greedy, 0, NoiPred(delta), r1))] + cont;
            match t1 { case Choice(ta1, tb1) => match t2 { case Choice(ta2, tb2) => {
              var itert1 := if greedy then ta1 else tb1;
              var skipt1 := if greedy then tb1 else ta1;
              var itert2 := if greedy then ta2 else tb2;
              var skipt2 := if greedy then tb2 else ta2;
              match itert1 { case GroupActionT(g1, ti1) => match itert2 { case GroupActionT(g2, ti2) => {
                assert TreeSize(ti1) < TreeSize(t1);
                assert TreeSize(skipt1) < TreeSize(t1);
                BoolTreeDeterm(rer, iterActs, i, CannotExit, ti1, ti2);
                BoolTreeDeterm(rer, cont, i, b, skipt1, skipt2);
              } case _ => } case _ => }
            } case _ => } case _ => }
          }
        }
        case Group(gid, r1) => {
          match t1 { case GroupActionT(g1, tc1) => match t2 { case GroupActionT(g2, tc2) =>
            BoolTreeDeterm(rer, [Areg(r1), Aclose(gid)] + cont, i, b, tc1, tc2);
          case _ => } case _ => }
        }
        case AnchorR(a) =>
          if AnchorSatisfied(rer, a, i) {
            match t1 { case AnchorPass(a1, tc1) => match t2 { case AnchorPass(a2, tc2) => BoolTreeDeterm(rer, cont, i, b, tc1, tc2); case _ => } case _ => }
          }
        case LookaroundR(lk, r1) =>
        case Backreference(gid) =>
    }
  }

  // ===== Derived corollaries (proved from the above + Semantics layer). =====

  // Coq: boolean_correct
  /** Starting fresh (empty captures, `CanExit`, nothing else on the stack) `IsTree` for a
      `PikeRegex` implies `BoolTree` — the entry point instance of `EncodeEqual` used by the rest
      of the engine correctness proof. */
  lemma BooleanCorrect(rer: RegExpRecord, r: Regex, inp: Input, t: Tree)
    requires PikeRegex(r)
    requires IsTree(rer, [Areg(r)], inp, Empty, Forward, t)
    ensures BoolTree(rer, [Areg(r)], inp, CanExit, t)
  {
    assert PikeActions([Areg(r)]);
    assert BoolEncoding(CanExit, inp, []);
    EncodeNext(CanExit, inp, [], r);
    assert [Areg(r)] == [Areg(r)] + [];
    EncodeEqual(rer, inp, [Areg(r)], CanExit, t, Empty);
  }

  // Coq: bool_to_istree
  /** The converse of `BooleanCorrect`: a `BoolTree` result (at the fresh initial state) is an
      `IsTree` result. Proved via productivity (`ComputeTr` always yields *some* tree) plus
      `BoolTreeDeterm` to identify it with `t`. */
  lemma BoolToIstree(rer: RegExpRecord, r: Regex, inp: Input, t: Tree)
    requires PikeRegex(r)
    requires BoolTree(rer, [Areg(r)], inp, CanExit, t)
    ensures IsTree(rer, [Areg(r)], inp, Empty, Forward, t)
  {
    // productivity: there is an is_tree t'
    var tprime := ComputeTr(rer, [Areg(r)], inp, Empty, Forward);
    ComputeTrIsTree(rer, [Areg(r)], inp, Empty, Forward);
    BooleanCorrect(rer, r, inp, tprime);
    BoolTreeDeterm(rer, [Areg(r)], inp, CanExit, t, tprime);
  }

  // Coq: booltree_istree_equiv
  /** `BooleanCorrect` + `BoolToIstree` combined: at the fresh initial state, `BoolTree` and
      `IsTree` agree exactly. This is the clean equivalence the rest of the engine bridge
      (`TreeRep`, `PikeEquiv`) builds on. */
  lemma BoolTreeIsTreeEquiv(rer: RegExpRecord, r: Regex, inp: Input, t: Tree)
    requires PikeRegex(r)
    ensures BoolTree(rer, [Areg(r)], inp, CanExit, t) <==> IsTree(rer, [Areg(r)], inp, Empty, Forward, t)
  {
    if BoolTree(rer, [Areg(r)], inp, CanExit, t) { BoolToIstree(rer, r, inp, t); }
    if IsTree(rer, [Areg(r)], inp, Empty, Forward, t) { BooleanCorrect(rer, r, inp, t); }
  }
}
