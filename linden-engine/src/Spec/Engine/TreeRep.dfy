// Mirror of Engine/TreeRep.v.
// `tree_rep t code pc inp b`: the backtracking tree t is represented in `code` starting at pc, for
// input inp and loop-boolean b. The tr_jmp / tr_begin rules keep the same tree at a new pc
// (stuttering), so tree_rep is non-structural — encoded as a least predicate.

/** Relates a backtracking `Tree` to a position in compiled `NFA.Code`: `TreeRep(rer, t, code, pc, inp, b)`
    holds when `t` is exactly the tree that running `code` from `pc` (at input `inp`, loop-flag `b`)
    represents. This is the bridge from `BooleanSemantics.BoolTree` to concrete bytecode positions,
    used to prove the PikeVM's program counter and the tree semantics agree. */
module TreeRep {
  import opened Std.Wrappers
  import opened WarblreRegExpRecord
  import opened WarblrePrimitives   // Direction, Forward
  import opened WarblreNumeric      // NoI, NN, Inf
  import opened Chars
  import opened Groups
  import opened Regex               // Quantified, DefGroups, regex constructors
  import opened Tree
  import opened Semantics
  import opened NFA
  import opened BooleanSemantics
  import opened PikeSubset
  import FS = FunctionalSemantics   // FS.NoiPred

  // Coq: tree_rep
  /** The representation relation itself: one clause per bytecode instruction, matching it against
      the tree shape it must produce (`Accept`↔`Match`, `Fork`↔`Choice`, `Consume`↔`Read`/`Mismatch`,
      `SetRegOpen`/`SetRegClose`/`ResetRegs`↔`GroupActionT`, `EndLoop`↔`Progress`/`Mismatch`). The
      `tr_jmp`/`tr_begin` clauses advance `pc` without changing `t` (bytecode "stuttering"), which is
      why this must be a `least predicate` rather than a structural one. */
  least predicate TreeRep(rer: RegExpRecord, t: Tree, code: Code, pc: Label, inp: Input, b: LoopBool)
  {
    // tr_match
    (GetPc(code, pc) == Some(Accept) && t == Match)
    // tr_jmp
    || (exists nextpc: nat :: GetPc(code, pc) == Some(Jmp(nextpc)) && TreeRep(rer, t, code, nextpc, inp, b))
    // tr_begin
    || (GetPc(code, pc) == Some(BeginLoop) && TreeRep(rer, t, code, pc + 1, inp, CannotExit))
    // tr_choice
    || (t.Choice? && exists pc1: nat, pc2: nat ::
          GetPc(code, pc) == Some(Fork(pc1, pc2))
          && TreeRep(rer, t.t1, code, pc1, inp, b) && TreeRep(rer, t.t2, code, pc2, inp, b))
    // tr_read
    || (t.Read? && exists cd: CharDescr, nextinp: Input ::
          GetPc(code, pc) == Some(Consume(cd))
          && ReadChar(rer, cd, inp, WarblrePrimitives.Forward) == Some((t.c, nextinp))
          && TreeRep(rer, t.t, code, pc + 1, nextinp, CanExit))
    // tr_progress
    || (t.Progress? && b == CanExit && exists nextpc: nat ::
          GetPc(code, pc) == Some(EndLoop(nextpc)) && TreeRep(rer, t.t, code, nextpc, inp, CanExit))
    // tr_open
    || (t.GroupActionT? && t.g.Open? && GetPc(code, pc) == Some(SetRegOpen(t.g.g)) && TreeRep(rer, t.t, code, pc + 1, inp, b))
    // tr_close
    || (t.GroupActionT? && t.g.Close? && GetPc(code, pc) == Some(SetRegClose(t.g.g)) && TreeRep(rer, t.t, code, pc + 1, inp, b))
    // tr_reset
    || (t.GroupActionT? && t.g.Reset? && GetPc(code, pc) == Some(ResetRegs(t.g.gl)) && TreeRep(rer, t.t, code, pc + 1, inp, b))
    // tr_anchorpass
    || (t.AnchorPass? && GetPc(code, pc) == Some(CheckAnchor(t.a))
          && AnchorSatisfied(rer, t.a, inp)
          && TreeRep(rer, t.t, code, pc + 1, inp, b))
    // tr_anchorfail
    || (t == Mismatch && exists a: Anchor ::
          GetPc(code, pc) == Some(CheckAnchor(a)) && !AnchorSatisfied(rer, a, inp))
    // tr_readfail
    || (t == Mismatch && exists cd: CharDescr :: GetPc(code, pc) == Some(Consume(cd)) && ReadChar(rer, cd, inp, WarblrePrimitives.Forward) == None)
    // tr_progressfail
    || (t == Mismatch && b == CannotExit && exists nextpc: nat :: GetPc(code, pc) == Some(EndLoop(nextpc)))
  }

  // ===== Axiomatized (inductions over tree_rep / bool_tree least predicates). See PROGRESS.md. =====

  // Coq: tree_rep_determ — at a fixed pc the instruction is fixed, so both derivations take the same
  // rule. tree_rep is non-structural (tr_jmp/tr_begin), so this is a least lemma over the derivation.
  /** `TreeRep` is functional: a given `(code, pc, inp, b)` represents at most one tree. Proved by
      case analysis on the instruction at `pc`, since it fixes which `TreeRep` clause both derivations
      must have taken. */
  least lemma TreeRepDeterm(rer: RegExpRecord, code: Code, pc: Label, inp: Input, b: LoopBool, t1: Tree, t2: Tree)
    requires TreeRep(rer, t1, code, pc, inp, b)
    requires TreeRep(rer, t2, code, pc, inp, b)
    ensures t1 == t2
  {
    match GetPc(code, pc)
    case Some(Accept) =>            // both tr_match → Match
    case Some(Jmp(np)) =>           // both tr_jmp
      TreeRepDeterm(rer, code, np, inp, b, t1, t2);
    case Some(CheckAnchor(a)) =>    // tr_anchorpass (satisfied) or tr_anchorfail
      if AnchorSatisfied(rer, a, inp) {
        match t1 {
          case AnchorPass(a1, tc1) =>
            match t2 {
              case AnchorPass(a2, tc2) => TreeRepDeterm(rer, code, pc + 1, inp, b, tc1, tc2);
              case _ =>
            }
          case _ =>
        }
      }
    case Some(BeginLoop) =>         // both tr_begin
      TreeRepDeterm(rer, code, pc + 1, inp, CannotExit, t1, t2);
    case Some(Fork(p1, p2)) =>      // both tr_choice
      match t1 { case Choice(ta1, tb1) => match t2 { case Choice(ta2, tb2) => {
        TreeRepDeterm(rer, code, p1, inp, b, ta1, ta2);
        TreeRepDeterm(rer, code, p2, inp, b, tb1, tb2);
      } case _ => } case _ => }
    case Some(Consume(cd)) =>       // tr_read (Some) or tr_readfail (None)
      match ReadChar(rer, cd, inp, WarblrePrimitives.Forward) {
        case None =>                // both Mismatch
        case Some(pair) =>
          match t1 { case Read(c1, tc1) => match t2 { case Read(c2, tc2) => TreeRepDeterm(rer, code, pc + 1, pair.1, CanExit, tc1, tc2); case _ => } case _ => }
      }
    case Some(EndLoop(np)) =>       // tr_progress (CanExit) or tr_progressfail (CannotExit)
      if b == CanExit {
        match t1 { case Progress(tc1) => match t2 { case Progress(tc2) => TreeRepDeterm(rer, code, np, inp, CanExit, tc1, tc2); case _ => } case _ => }
      }
    case Some(SetRegOpen(gid)) =>   // tr_open
      match t1 { case GroupActionT(g1, tc1) => match t2 { case GroupActionT(g2, tc2) => TreeRepDeterm(rer, code, pc + 1, inp, b, tc1, tc2); case _ => } case _ => }
    case Some(SetRegClose(gid)) =>  // tr_close
      match t1 { case GroupActionT(g1, tc1) => match t2 { case GroupActionT(g2, tc2) => TreeRepDeterm(rer, code, pc + 1, inp, b, tc1, tc2); case _ => } case _ => }
    case Some(ResetRegs(gidl)) =>   // tr_reset
      match t1 { case GroupActionT(g1, tc1) => match t2 { case GroupActionT(g2, tc2) => TreeRepDeterm(rer, code, pc + 1, inp, b, tc1, tc2); case _ => } case _ => }
    case Some(KillThread) =>        // no rule has KillThread → both hyps false (vacuous)
    case None =>                    // vacuous
  }

  // ----- jump-fuel-indexed actions_rep (bounds the jump chain so a structural measure exists) -----
  // actions_rep is a least predicate whose jump_bc rule is non-structural (the action list and tree
  // stay fixed, only pc moves). To do the actions_tree_rep induction we extract a numeric bound `n`
  // on the jump chain and make the third lex component decrease for jumps.
  /** A fuel-bounded copy of `NFA.ActionsRep`: identical clauses, but `jump_bc` consumes one unit of
      `n` instead of looping on `pc` alone. Exists purely so inductions have a structural measure to
      decrease across jumps; see `ActionsRepToFuel`/`FuelToActionsRep` for the equivalence with the
      real `ActionsRep`. */
  ghost predicate ActionsRepFuel(acts: Actions, c: Code, pc: Label, n: nat)
    decreases n
  {
    n > 0 &&
    ((|acts| == 0 && GetPc(c, pc) == Some(Accept))                                                          // empty_bc
     || (|acts| > 0 && exists pcmid: nat :: ActionRep(acts[0], c, pc, pcmid) && ActionsRepFuel(acts[1..], c, pcmid, n - 1))  // cons_bc
     || (exists pcstart: nat :: GetPc(c, pc) == Some(Jmp(pcstart)) && ActionsRepFuel(acts, c, pcstart, n - 1)))             // jump_bc
  }

  // Every actions_rep derivation has a finite jump-chain bound.
  /** Every real `NFA.ActionsRep` derivation has *some* finite fuel bound `n` making `ActionsRepFuel`
      hold — i.e. fuel-indexing loses no derivations. */
  least lemma ActionsRepToFuel(acts: Actions, c: Code, pc: Label)
    requires ActionsRep(acts, c, pc)
    ensures exists n: nat :: ActionsRepFuel(acts, c, pc, n)
  {
    if |acts| == 0 && GetPc(c, pc) == Some(Accept) {
      assert ActionsRepFuel(acts, c, pc, 1);
    } else if |acts| > 0 && exists pcmid: nat :: ActionRep(acts[0], c, pc, pcmid) && ActionsRep(acts[1..], c, pcmid) {
      var pcmid: nat :| ActionRep(acts[0], c, pc, pcmid) && ActionsRep(acts[1..], c, pcmid);
      ActionsRepToFuel(acts[1..], c, pcmid);
      var np: nat :| ActionsRepFuel(acts[1..], c, pcmid, np);
      assert ActionsRepFuel(acts, c, pc, np + 1);
    } else {
      var pcstart: nat :| GetPc(c, pc) == Some(Jmp(pcstart)) && ActionsRep(acts, c, pcstart);
      ActionsRepToFuel(acts, c, pcstart);
      var np: nat :| ActionsRepFuel(acts, c, pcstart, np);
      assert ActionsRepFuel(acts, c, pc, np + 1);
    }
  }

  // The fuel-indexed version implies the genuine actions_rep (used to rebuild reps for expanded lists).
  /** The converse of `ActionsRepToFuel`: any fuel-indexed derivation drops its fuel to yield the real
      `NFA.ActionsRep`. Used to rebuild an `ActionsRep` fact after an action list has been expanded. */
  lemma FuelToActionsRep(acts: Actions, c: Code, pc: Label, n: nat)
    requires ActionsRepFuel(acts, c, pc, n)
    ensures ActionsRep(acts, c, pc)
    decreases n
  {
    if |acts| == 0 && GetPc(c, pc) == Some(Accept) {
    } else if |acts| > 0 && exists pcmid: nat :: ActionRep(acts[0], c, pc, pcmid) && ActionsRepFuel(acts[1..], c, pcmid, n - 1) {
      var pcmid: nat :| ActionRep(acts[0], c, pc, pcmid) && ActionsRepFuel(acts[1..], c, pcmid, n - 1);
      FuelToActionsRep(acts[1..], c, pcmid, n - 1);
    } else {
      var pcstart: nat :| GetPc(c, pc) == Some(Jmp(pcstart)) && ActionsRepFuel(acts, c, pcstart, n - 1);
      FuelToActionsRep(acts, c, pcstart, n - 1);
    }
  }

  // Fuel-bounded core of actions_tree_rep. Lex measure (TreeSize, ActionsRegexSize, fuel): jumps
  // decrease the fuel; action-list expansions (Seq/Disj/Quant/Group) decrease TreeSize or
  // ActionsRegexSize and re-extract fresh fuel for the rebuilt rep.
  /** Fuel-bounded core of `ActionsTreeRep`: if `acts` computes tree `t` via `BoolTree` and is
      compiled at `pc` (per the fuel-indexed `ActionsRepFuel`), then `t` is what `code` at `pc`
      represents. This is the technical workhorse that `ActionsTreeRep` packages for callers. */
  /** Minimal-context two-action cons: represents `[a0, a1] + cont` from the
      two step reps and the continuation rep (keeps the seq algebra away from
      the big induction's context). */
  lemma ConsTwoRep(a0: Action, a1: Action, cont: Actions, code: Code, pc0: Label, pc1: Label, pc2: Label)
    requires ActionRep(a0, code, pc0, pc1)
    requires ActionRep(a1, code, pc1, pc2)
    requires ActionsRep(cont, code, pc2)
    ensures ActionsRep([a0, a1] + cont, code, pc0)
  {
    var lq := [a1] + cont;
    assert lq[0] == a1 && lq[1..] == cont;
    assert ActionsRep(lq, code, pc1);
    var ia := [a0] + lq;
    assert ia[0] == a0 && ia[1..] == lq;
    assert ActionsRep(ia, code, pc0);
    assert ia == [a0, a1] + cont;
  }

  lemma ActionsTreeRepF(rer: RegExpRecord, acts: Actions, code: Code, pc: Label, inp: Input, b: LoopBool, t: Tree, n: nat)
    requires PikeActions(acts)
    requires ActionsRepFuel(acts, code, pc, n)
    requires BoolTree(rer, acts, inp, b, t)
    ensures TreeRep(rer, t, code, pc, inp, b)
    decreases TreeSize(t), ActionsRegexSize(acts), n
  {
    if |acts| == 0 && GetPc(code, pc) == Some(Accept) {
      // empty_bc: BoolTree([]) ⇒ t == Match ⇒ tr_match
      assert t == Match;
    } else if exists pcstart: nat :: GetPc(code, pc) == Some(Jmp(pcstart)) && ActionsRepFuel(acts, code, pcstart, n - 1) {
      var pcstart: nat :| GetPc(code, pc) == Some(Jmp(pcstart)) && ActionsRepFuel(acts, code, pcstart, n - 1);
      ActionsTreeRepF(rer, acts, code, pcstart, inp, b, t, n - 1);   // ⇒ TreeRep(t, code, pcstart, ..); tr_jmp
    } else {
      // cons_bc
      var cont := acts[1..];
      var pcmid: nat :| ActionRep(acts[0], code, pc, pcmid) && ActionsRepFuel(cont, code, pcmid, n - 1);
      PikeActionsTail(acts);
      assert acts == [acts[0]] + cont;
      PikeActionsConsIff(acts[0], cont);
      FuelToActionsRep(cont, code, pcmid, n - 1);   // ActionsRep(cont, code, pcmid)
      match acts[0]
      case Acheck(strcheck) =>
        // ActionRep ⇒ GetPc(pc) == EndLoop(pcmid)
        if b == CanExit {
          // t == Progress(tc); tr_progress with nextpc == pcmid
          match t {
            case Progress(tc) =>
              ActionsTreeRepF(rer, cont, code, pcmid, inp, CanExit, tc, n - 1);
            case _ =>
          }
        }
        // else t == Mismatch, b == CannotExit ⇒ tr_progressfail
      case Aclose(gid) =>
        // GetPc(pc) == SetRegClose(gid), pcmid == pc+1; t == GroupActionT(Close(gid), tc); tr_close
        match t {
          case GroupActionT(g, tc) => ActionsTreeRepF(rer, cont, code, pc + 1, inp, b, tc, n - 1);
          case _ =>
        }
      case Areg(r) =>
        assert PikeRegex(r);
        match r
        case Epsilon =>
          // NfaRep(Epsilon) ⇒ pc == pcmid; BoolTree(Areg Eps :: cont) == BoolTree(cont) (same t)
          ActionsTreeRepF(rer, cont, code, pc, inp, b, t, n - 1);
        case Character(cd) => {
          // NfaRep(Character) ⇒ GetPc(pc) == Consume(cd), pcmid == pc+1
          match ReadChar(rer, cd, inp, Forward) {
            case None =>   // t == Mismatch; tr_readfail
            case Some(pair) =>
              match t {
                case Read(c, tc) => ActionsTreeRepF(rer, cont, code, pc + 1, pair.1, CanExit, tc, n - 1);
                case _ =>
              }
          }
        }
        case Disjunction(r1, r2) => {
          PikeActionsConsIff(Areg(r1), cont);
          PikeActionsConsIff(Areg(r2), cont);
          var e1: nat :| GetPc(code, pc) == Some(Fork(pc + 1, e1 + 1)) && NfaRep(r1, code, pc + 1, e1)
                       && GetPc(code, e1) == Some(Jmp(pcmid)) && NfaRep(r2, code, e1 + 1, pcmid);
          match t {
            case Choice(ta, tb) =>
              // left: ActionsRep([Areg r1]+cont, code, pc+1) via the Jmp(e1→pcmid)+cont
              var la := [Areg(r1)] + cont;
              assert ActionsRep(cont, code, e1) by { assert GetPc(code, e1) == Some(Jmp(pcmid)); }   // jump_bc
              assert ActionRep(Areg(r1), code, pc + 1, e1);
              assert la[0] == Areg(r1) && la[1..] == cont;
              assert ActionsRep(la, code, pc + 1);   // cons_bc
              ActionsRepToFuel(la, code, pc + 1);
              var na: nat :| ActionsRepFuel(la, code, pc + 1, na);
              ActionsTreeRepF(rer, la, code, pc + 1, inp, b, ta, na);
              // right: ActionsRep([Areg r2]+cont, code, e1+1)
              var lb := [Areg(r2)] + cont;
              assert ActionRep(Areg(r2), code, e1 + 1, pcmid);
              assert lb[0] == Areg(r2) && lb[1..] == cont;
              assert ActionsRep(lb, code, e1 + 1);   // cons_bc
              ActionsRepToFuel(lb, code, e1 + 1);
              var nb: nat :| ActionsRepFuel(lb, code, e1 + 1, nb);
              ActionsTreeRepF(rer, lb, code, e1 + 1, inp, b, tb, nb);
              // tr_choice (Fork(pc+1, e1+1))
            case _ =>
          }
        }
        case Sequence(r1, r2) => {
          PikeActionsConsIff(Areg(r2), cont);
          PikeActionsConsIff(Areg(r1), [Areg(r2)] + cont);
          assert NfaRep(Sequence(r1, r2), code, pc, pcmid);   // == ActionRep(acts[0], code, pc, pcmid)
          var e1: nat :| NfaRep(r1, code, pc, e1) && NfaRep(r2, code, e1, pcmid);
          var na := [Areg(r1), Areg(r2)] + cont;
          assert na == [Areg(r1)] + ([Areg(r2)] + cont);
          assert ActionRep(Areg(r2), code, e1, pcmid);
          assert ([Areg(r2)] + cont)[0] == Areg(r2) && ([Areg(r2)] + cont)[1..] == cont;
          assert ActionsRep([Areg(r2)] + cont, code, e1);   // cons_bc
          assert ActionRep(Areg(r1), code, pc, e1);
          assert na[0] == Areg(r1) && na[1..] == [Areg(r2)] + cont;
          assert ActionsRep(na, code, pc);                  // cons_bc
          assert ActionsRegexSize(na) < ActionsRegexSize(acts);
          ActionsRepToFuel(na, code, pc);
          var nn: nat :| ActionsRepFuel(na, code, pc, nn);
          ActionsTreeRepF(rer, na, code, pc, inp, b, t, nn);
        }
        case Quantified(greedy, min, delta, r1) => {
          var gidl := DefGroups(r1);
          if min > 0 {
            // FORCED iteration: NfaRepMin(min) unfolds one ResetRegs+body copy
            // at pc; the tree is GroupActionT(Reset(gidl), tc) with the stack
            // [Areg r1, Areg Quantified(min-1, delta)] + cont at pc+1.
            var quant1 := Quantified(greedy, min - 1, delta, r1);
            var em: nat :| NfaRepMin(min, gidl, r1, code, pc, em)
              && (match delta
                  case Inf =>
                    exists e1: nat ::
                      GetPc(code, em) == Some(GreedyFork(greedy, em + 1, e1 + 1))
                      && GetPc(code, em + 1) == Some(BeginLoop)
                      && GetPc(code, em + 2) == Some(ResetRegs(gidl))
                      && NfaRep(r1, code, em + 3, e1)
                      && GetPc(code, e1) == Some(EndLoop(em))
                      && pcmid == e1 + 1
                  case NN(k) => NfaRepOpt(k, greedy, gidl, r1, code, em, pcmid));
            // NfaRepMin at min > 0 unfolds one forced copy
            var eb: nat :| GetPc(code, pc) == Some(ResetRegs(gidl))
              && NfaRep(r1, code, pc + 1, eb)
              && NfaRepMin(min - 1, gidl, r1, code, eb, em);
            match delta {
              case Inf =>
                var e1: nat :| GetPc(code, em) == Some(GreedyFork(greedy, em + 1, e1 + 1))
                  && GetPc(code, em + 1) == Some(BeginLoop)
                  && GetPc(code, em + 2) == Some(ResetRegs(gidl))
                  && NfaRep(r1, code, em + 3, e1)
                  && GetPc(code, e1) == Some(EndLoop(em))
                  && pcmid == e1 + 1;
                NfaRepQuantIntroInf(greedy, min - 1, r1, code, eb, em, e1, pcmid);
              case NN(k) =>
                NfaRepQuantIntroNN(greedy, min - 1, k, r1, code, eb, em, pcmid);
            }
            assert NfaRep(quant1, code, eb, pcmid);
            match t {
              case GroupActionT(g, tc) =>
                PikeActionsConsIff(Areg(quant1), cont);
                PikeActionsConsIff(Areg(r1), [Areg(quant1)] + cont);
                FuelToActionsRep(cont, code, pcmid, n - 1);   // ActionsRep(cont, pcmid)
                assert ActionRep(Areg(quant1), code, eb, pcmid);
                assert ActionRep(Areg(r1), code, pc + 1, eb);
                ConsTwoRep(Areg(r1), Areg(quant1), cont, code, pc + 1, eb, pcmid);
                var ia := [Areg(r1), Areg(quant1)] + cont;   // BoolTree's forced list
                ActionsRepToFuel(ia, code, pc + 1);
                var ni: nat :| ActionsRepFuel(ia, code, pc + 1, ni);
                assert TreeSize(tc) < TreeSize(t);
                ActionsTreeRepF(rer, ia, code, pc + 1, inp, b, tc, ni);
                // TreeRep(tc, pc+1) -> tr_reset at pc (ResetRegs carries the Reset node)
              case _ =>
            }
          } else {
            match delta {
            case Inf =>
              var quant := Quantified(greedy, 0, FS.NoiPred(delta), r1);
              assert quant == Quantified(greedy, 0, Inf, r1) == Quantified(greedy, min, delta, r1);
              var e1: nat :| GetPc(code, pc) == Some(GreedyFork(greedy, pc + 1, e1 + 1)) && GetPc(code, pc + 1) == Some(BeginLoop)
                           && GetPc(code, pc + 2) == Some(ResetRegs(gidl)) && NfaRep(r1, code, pc + 3, e1)
                           && GetPc(code, e1) == Some(EndLoop(pc)) && pcmid == e1 + 1;
              match t {
                case Choice(ta, tb) =>
                  var itert := if greedy then ta else tb;
                  var skipt := if greedy then tb else ta;
                  match itert {
                    case GroupActionT(g, ti) =>
                      // skip branch: BoolTree(cont) == skipt at pcmid == e1+1
                      ActionsTreeRepF(rer, cont, code, e1 + 1, inp, b, skipt, n - 1);
                      // iter branch: build ActionsRep of [Areg r1, Acheck(inp), Areg quant] + cont at pc+3
                      PikeActionsConsIff(Areg(quant), cont);
                      PikeActionsConsIff(Acheck(inp), [Areg(quant)] + cont);
                      PikeActionsConsIff(Areg(r1), [Acheck(inp)] + ([Areg(quant)] + cont));
                      // [Areg quant]+cont at pc: the back-edge lands on the same star block
                      var lq := [Areg(quant)] + cont;
                      assert ActionRep(Areg(quant), code, pc, pcmid);   // quant == the same regex
                      assert lq[0] == Areg(quant) && lq[1..] == cont;
                      assert ActionsRep(lq, code, pc);   // cons_bc (cont at pcmid==e1+1)
                      // [Acheck(inp), Areg quant]+cont at e1: EndLoop(pc)
                      var lc := [Acheck(inp)] + lq;
                      assert ActionRep(Acheck(inp), code, e1, pc);   // GetPc(e1)==EndLoop(pc)
                      assert lc[0] == Acheck(inp) && lc[1..] == lq;
                      assert ActionsRep(lc, code, e1);   // cons_bc
                      // [Areg r1, Acheck(inp), Areg quant]+cont at pc+3
                      var ia := [Areg(r1)] + lc;
                      assert ActionRep(Areg(r1), code, pc + 3, e1);   // NfaRep(r1, pc+3, e1)
                      assert ia[0] == Areg(r1) && ia[1..] == lc;
                      assert ActionsRep(ia, code, pc + 3);   // cons_bc
                      assert ia == [Areg(r1), Acheck(inp), Areg(quant)] + cont;   // match BoolTree's iter list
                      ActionsRepToFuel(ia, code, pc + 3);
                      var ni: nat :| ActionsRepFuel(ia, code, pc + 3, ni);
                      assert TreeSize(ti) < TreeSize(t);
                      ActionsTreeRepF(rer, ia, code, pc + 3, inp, CannotExit, ti, ni);
                      // TreeRep(ti, pc+3, CannotExit) -> tr_reset (pc+2) -> tr_begin (pc+1) -> itert at pc+1
                      // skipt at e1+1; tr_choice with GreedyFork(greedy, pc+1, e1+1)
                    case _ =>
                  }
                case _ =>
              }
            case NN(k) =>
              var em: nat := NfaRepQuantInvNN(greedy, min, k, r1, code, pc, pcmid);
              assert em == pc;   // min == 0: the forced chain is empty
              assert NfaRepOpt(k, greedy, gidl, r1, code, pc, pcmid);
              if k == 0 {
                // spent quantifier: no code, epsilon-continue with cont
                assert pc == pcmid;
                assert ActionsRegexSize(cont) < ActionsRegexSize(acts);
                ActionsTreeRepF(rer, cont, code, pcmid, inp, b, t, n - 1);
              } else {
                // one bounded layer: fork skips to the common end pcmid
                var quant := Quantified(greedy, 0, FS.NoiPred(delta), r1);
                assert quant == Quantified(greedy, 0, NN(k - 1), r1);
                var e1: nat :| GetPc(code, pc) == Some(GreedyFork(greedy, pc + 1, pcmid))
                  && GetPc(code, pc + 1) == Some(BeginLoop)
                  && GetPc(code, pc + 2) == Some(ResetRegs(gidl))
                  && NfaRep(r1, code, pc + 3, e1)
                  && GetPc(code, e1) == Some(EndLoop(e1 + 1))
                  && NfaRepOpt(k - 1, greedy, gidl, r1, code, e1 + 1, pcmid);
                match t {
                  case Choice(ta, tb) =>
                    var itert := if greedy then ta else tb;
                    var skipt := if greedy then tb else ta;
                    match itert {
                      case GroupActionT(g, ti) =>
                        // skip branch: cont at the common end pcmid
                        ActionsTreeRepF(rer, cont, code, pcmid, inp, b, skipt, n - 1);
                        // iter branch at pc+3 with the NN(k-1) continuation at e1+1
                        PikeActionsConsIff(Areg(quant), cont);
                        PikeActionsConsIff(Acheck(inp), [Areg(quant)] + cont);
                        PikeActionsConsIff(Areg(r1), [Acheck(inp)] + ([Areg(quant)] + cont));
                        FuelToActionsRep(cont, code, pcmid, n - 1);   // ActionsRep(cont, pcmid)
                        var lq := [Areg(quant)] + cont;
                        assert NfaRepMin(0, gidl, r1, code, e1 + 1, e1 + 1);
                        NfaRepQuantIntroNN(greedy, 0, k - 1, r1, code, e1 + 1, e1 + 1, pcmid);
                        assert ActionRep(Areg(quant), code, e1 + 1, pcmid);
                        assert lq[0] == Areg(quant) && lq[1..] == cont;
                        assert ActionsRep(lq, code, e1 + 1);   // cons_bc
                        var lc := [Acheck(inp)] + lq;
                        assert ActionRep(Acheck(inp), code, e1, e1 + 1);   // EndLoop(e1+1)
                        assert lc[0] == Acheck(inp) && lc[1..] == lq;
                        assert ActionsRep(lc, code, e1);   // cons_bc
                        var ia := [Areg(r1)] + lc;
                        assert ActionRep(Areg(r1), code, pc + 3, e1);
                        assert ia[0] == Areg(r1) && ia[1..] == lc;
                        assert ActionsRep(ia, code, pc + 3);   // cons_bc
                        assert ia == [Areg(r1), Acheck(inp), Areg(quant)] + cont;
                        ActionsRepToFuel(ia, code, pc + 3);
                        var ni: nat :| ActionsRepFuel(ia, code, pc + 3, ni);
                        assert TreeSize(ti) < TreeSize(t);
                        ActionsTreeRepF(rer, ia, code, pc + 3, inp, CannotExit, ti, ni);
                        // tr_reset (pc+2) -> tr_begin (pc+1); tr_choice with GreedyFork(greedy, pc+1, pcmid)
                      case _ =>
                    }
                  case _ =>
                }
              }
            }
          }
        }
        case Group(gid, r1) => {
          PikeActionsConsIff(Aclose(gid), cont);
          PikeActionsConsIff(Areg(r1), [Aclose(gid)] + cont);
          var e1: nat :| GetPc(code, pc) == Some(SetRegOpen(gid)) && NfaRep(r1, code, pc + 1, e1)
                       && GetPc(code, e1) == Some(SetRegClose(gid)) && pcmid == e1 + 1;
          match t {
            case GroupActionT(g, tc) =>
              var lc := [Aclose(gid)] + cont;
              assert ActionRep(Aclose(gid), code, e1, e1 + 1);   // GetPc(e1)==SetRegClose(gid), e1+1==e1+1
              assert lc[0] == Aclose(gid) && lc[1..] == cont;
              assert ActionsRep(lc, code, e1);   // cons_bc (cont at pcmid==e1+1)
              var ga := [Areg(r1)] + lc;
              assert ActionRep(Areg(r1), code, pc + 1, e1);
              assert ga[0] == Areg(r1) && ga[1..] == lc;
              assert ActionsRep(ga, code, pc + 1);   // cons_bc
              assert ga == [Areg(r1), Aclose(gid)] + cont;   // match BoolTree's expanded list
              ActionsRepToFuel(ga, code, pc + 1);
              var ng: nat :| ActionsRepFuel(ga, code, pc + 1, ng);
              ActionsTreeRepF(rer, ga, code, pc + 1, inp, b, tc, ng);
              // tr_open (GetPc(pc)==SetRegOpen(gid))
            case _ =>
          }
        }
        case AnchorR(a) => {
          // NfaRep(AnchorR) => GetPc(pc) == CheckAnchor(a), pcmid == pc + 1
          if AnchorSatisfied(rer, a, inp) {
            match t {
              case AnchorPass(a2, tc) =>
                ActionsTreeRepF(rer, cont, code, pc + 1, inp, b, tc, n - 1);  // tr_anchorpass
              case _ =>
            }
          }
          // else t == Mismatch; tr_anchorfail
        }
        case LookaroundR(lk, r1) =>   // not pike
        case Backreference(gid) =>    // not pike
    }
  }

  // Coq: actions_tree_rep — now PROVED (fuel-extraction + the lex induction above).
  /** The key bridge lemma: if `acts` is compiled at `pc` (`NFA.ActionsRep`), is a `PikeSubset.PikeActions`
      list, and `BoolTree` says `acts` computes tree `t`, then `t` is exactly what `code` at `pc`
      represents (`TreeRep`). Connects the boolean-encoded semantics to concrete bytecode positions. */
  lemma ActionsTreeRep(rer: RegExpRecord, acts: Actions, code: Code, pc: Label, inp: Input, b: LoopBool, t: Tree)
    requires PikeActions(acts)
    requires ActionsRep(acts, code, pc)
    requires BoolTree(rer, acts, inp, b, t)
    ensures TreeRep(rer, t, code, pc, inp, b)
  {
    ActionsRepToFuel(acts, code, pc);
    var n: nat :| ActionsRepFuel(acts, code, pc, n);
    ActionsTreeRepF(rer, acts, code, pc, inp, b, t, n);
  }

  // Coq: actions_rep_unicity (proved from the two above)
  /** Two *different* action lists compiled at the same `pc` must compute the same tree via `BoolTree`
      — the bytecode position alone determines the result, regardless of which source action list
      produced it. Follows from `ActionsTreeRep` plus `TreeRepDeterm`. */
  lemma ActionsRepUnicity(rer: RegExpRecord, a1: Actions, a2: Actions, code: Code, pc: Label, t1: Tree, t2: Tree, inp: Input, b: LoopBool)
    requires PikeActions(a1) && PikeActions(a2)
    requires ActionsRep(a1, code, pc) && ActionsRep(a2, code, pc)
    requires BoolTree(rer, a1, inp, b, t1) && BoolTree(rer, a2, inp, b, t2)
    ensures t1 == t2
  {
    ActionsTreeRep(rer, a1, code, pc, inp, b, t1);
    ActionsTreeRep(rer, a2, code, pc, inp, b, t2);
    TreeRepDeterm(rer, code, pc, inp, b, t1, t2);
  }
}
