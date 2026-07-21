// Phase +C3b: WalkOk entries — compiled code satisfies the walk guard.
//
// The construction consumes WalkOk; this file supplies it for the actual
// compiled bytecode, by structural induction over the RegElk-side compiler
// adherence NfaRepRE (which, unlike NfaRepL, has NO loop-view arm: every
// block shape is pinned, so the guard demands are either vacuous or
// discharged by the block layout). The two back edges — the star's back-Jmp
// and the do-while's backward fork — are coinductive knots, handled by plain
// nat induction on the WalkOkF fuel: the knot re-enters the same
// configuration at strictly smaller fuel.
//
// The composition lemma WalkOkCompF is continuation-passing: "if the
// continuation is walk-guarded at the block's exit (at every fuel below n,
// for every guard bit), then [Areg(Translate(re))] + cont is walk-guarded at
// the block's entry at fuel n". Chain lemmas mirror NfaRepMinRE/NfaRepOptRE;
// rest lemmas establish the iteration continuations sitting at EndLoop /
// backward-fork positions, where the knots live.
include "WalkOk.dfy"

/** Phase +C3b — `WalkOk` entries: `WalkOkEntry` establishes the walk guard
    for `compile_to_bytecode` output at every guard bit, via the
    continuation-passing composition lemma `WalkOkCompF` over `NfaRepRE`. */
module LindenElkWalkOkEntry {
  import opened Std.Wrappers
  import LC = Chars
  import L = Regex
  import LN = WarblreNumeric
  import LS = Semantics
  import FS = FunctionalSemantics
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import T = LindenElkTranslate
  import NR = LindenElkNfaRep
  import AR = LindenElkActionsRep
  import WO = LindenElkWalkOk

  // ===========================================================================
  // Transparent shapes and the head-pin trichotomy
  // ===========================================================================

  /** Walk-transparent Linden regexes: their `WalkOkRegF` case demands only
      the tail at the SAME pc (no instruction consulted) — exactly the shapes
      whose compiled block can be empty. */
  predicate TransparentL(r: L.Regex) {
    match r
    case Epsilon => true
    case Sequence(r1, r2) => TransparentL(r1) && TransparentL(r2)
    case Quantified(_, min, delta, _) => min == 0 && delta == LN.NN(0)
    case _ => false
  }

  /** If a compiled block starts ON a `Jmp`, the block is empty and its
      translation is walk-transparent: every non-empty shape pins a non-`Jmp`
      instruction at its head. */
  lemma NfaRepREPins(re: R.regex, c: RB.code, pc1: nat, pc2: nat)
    requires NR.PlusFragmentRE(re) && T.TransWf(re)
    requires NR.NfaRepRE(re, c, pc1, pc2)
    requires NR.GetPcRE(c, pc1).Some? && NR.GetPcRE(c, pc1).value.Jmp?
    ensures pc1 == pc2 && TransparentL(T.Translate(re))
    decreases CP.rsize(re)
  {
    match re
    case Re_empty =>
    case Re_character(_) =>      // pins Consume: vacuous
    case Re_anchor(_) =>         // pins AnchorAssertion: vacuous
    case Re_alt(_, _) =>         // pins Fork: vacuous
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, c, pc1, e1) && NR.NfaRepRE(r2, c, e1, pc2);
      NfaRepREPins(r1, c, pc1, e1);
      NfaRepREPins(r2, c, e1, pc2);
    case Re_capture(_, _) =>     // pins SetRegisterToCP: vacuous
    case Re_lookaround(_, _, _) =>
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        // pins Fork: vacuous
      } else if q.max.Some? {
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid, r1, c, pc1, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid, r1, c, em, pc2);
        if mn > 0 {
          // the forced chain pins SetQuantToClock: vacuous
          var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qid, false))
            && NR.NfaRepRE(r1, c, pc1 + 1, e1) && NR.NfaRepMinRE(mn - 1, qid, r1, c, e1, em);
        } else if kx > 0 {
          // the first layer pins Fork: vacuous
          assert em == pc1;
          var e1: nat :| NR.GetPcRE(c, pc1) == Some(if q.greedy then RB.Fork(pc1 + 1, pc2) else RB.Fork(pc2, pc1 + 1))
            && NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qid, false))
            && NR.GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
            && NR.NfaRepRE(r1, c, pc1 + 3, e1)
            && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
            && NR.NfaRepOptRE(kx - 1, q.greedy, qid, r1, c, e1 + 1, pc2);
        } else {
          // spent {0,0}: no code — transparent
          assert em == pc1 && pc2 == pc1;
          assert T.TrDelta(q) == LN.NN(0);
          assert T.Translate(re) == L.Quantified(q.greedy, 0, LN.NN(0), T.Translate(r1));
        }
      } else {
        // the do-while chain head pins SetQuantToClock: vacuous
        var mn1 := (q.min - 1) as nat;
        var em: nat :| NR.NfaRepMinRE(mn1, qid, r1, c, pc1, em)
          && NR.GetPcRE(c, em) == Some(RB.SetQuantToClock(qid, false))
          && (exists e1: nat ::
                NR.NfaRepRE(r1, c, em + 1, e1)
                && NR.GetPcRE(c, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
                && pc2 == e1 + 1);
        if mn1 > 0 {
          var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qid, false))
            && NR.NfaRepRE(r1, c, pc1 + 1, e1) && NR.NfaRepMinRE(mn1 - 1, qid, r1, c, e1, em);
        } else {
          assert em == pc1;
        }
      }
  }

  // ===========================================================================
  // Structural helpers: transparent cons and Jmp routing
  // ===========================================================================

  /** Prepending a walk-transparent `Areg` preserves the guard: its only
      demands are the tail at the same pc (and through any `Jmp` sitting
      there, which the tail's own guard already routes). */
  lemma WalkOkConsTransparent(m: nat, r: L.Regex, cont: LS.Actions, c: RB.code, pc: nat, g: bool)
    requires TransparentL(r)
    requires forall mm: nat {:trigger WO.WalkOkF(cont, c, pc, g, mm)} :: mm < m ==> WO.WalkOkF(cont, c, pc, g, mm)
    ensures WO.WalkOkF([LS.Areg(r)] + cont, c, pc, g, m)
    decreases m, LS.RegexSize(r)
  {
    if m == 0 { return; }
    var tgt := [LS.Areg(r)] + cont;
    assert tgt[0] == LS.Areg(r) && tgt[1..] == cont;
    // the Jmp routing conjunct
    if NR.GetPcRE(c, pc).Some? && NR.GetPcRE(c, pc).value.Jmp? {
      var np := NR.GetPcRE(c, pc).value.jl;
      if np >= 0 {
        forall mm: nat {:trigger WO.WalkOkF(cont, c, np as nat, g, mm)} | mm < m - 1
          ensures WO.WalkOkF(cont, c, np as nat, g, mm)
        {
          assert WO.WalkOkF(cont, c, pc, g, mm + 1);
        }
        WalkOkConsTransparent(m - 1, r, cont, c, np as nat, g);
      }
    }
    // the head conjunct, by transparent shape
    match r
    case Epsilon =>
      assert WO.WalkOkF(cont, c, pc, g, m - 1);
      assert WO.WalkOkRegF(r, cont, c, pc, g, m);
    case Sequence(r1, r2) =>
      forall mm: nat {:trigger WO.WalkOkF([LS.Areg(r2)] + cont, c, pc, g, mm)} | mm < m - 1
        ensures WO.WalkOkF([LS.Areg(r2)] + cont, c, pc, g, mm)
      {
        WalkOkConsTransparent(mm, r2, cont, c, pc, g);
      }
      WalkOkConsTransparent(m - 1, r1, [LS.Areg(r2)] + cont, c, pc, g);
      assert [LS.Areg(r1)] + ([LS.Areg(r2)] + cont) == [LS.Areg(r1), LS.Areg(r2)] + cont;
      assert WO.WalkOkF([LS.Areg(r1), LS.Areg(r2)] + cont, c, pc, g, m - 1);
      assert WO.WalkOkRegF(r, cont, c, pc, g, m);
    case Quantified(greedy, min, delta, r1) =>
      assert min == 0 && delta == LN.NN(0);
      assert WO.WalkOkF(cont, c, pc, g, m - 1);
      assert WO.WalkOkRegF(r, cont, c, pc, g, m);
    assert WO.WalkOkF(tgt, c, pc, g, m);
  }

  /** A list sitting on a `Jmp` is guarded whenever it is guarded at the
      target: non-transparent heads pin other instructions (vacuous at a
      `Jmp`), transparent heads unfold in place and route recursively. */
  lemma WalkOkAtJmp(m: nat, acts: LS.Actions, c: RB.code, pcj: nat, np: nat, g: bool)
    requires NR.GetPcRE(c, pcj) == Some(RB.Jmp(np))
    requires forall mm: nat {:trigger WO.WalkOkF(acts, c, np, g, mm)} :: mm < m ==> WO.WalkOkF(acts, c, np, g, mm)
    ensures WO.WalkOkF(acts, c, pcj, g, m)
    decreases m
  {
    if m == 0 { return; }
    // the Jmp routing conjunct: directly the hypothesis
    assert WO.WalkOkF(acts, c, np, g, m - 1);
    if |acts| == 0 { return; }
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // EndLoop / backfork guards: vacuous at a Jmp
      assert !AR.BackForkAt(c, pcj);
    case Aclose(_) =>   // SetRegisterToCP guard: vacuous
    case Areg(r) =>
      match r
      case Epsilon =>
        forall mm: nat {:trigger WO.WalkOkF(cont, c, np, g, mm)} | mm < m - 1
          ensures WO.WalkOkF(cont, c, np, g, mm)
        {
          assert WO.WalkOkF(acts, c, np, g, mm + 1);
          assert WO.WalkOkRegF(r, cont, c, np, g, mm + 1);
        }
        WalkOkAtJmp(m - 1, cont, c, pcj, np, g);
        assert WO.WalkOkRegF(r, cont, c, pcj, g, m);
      case Sequence(r1, r2) =>
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        forall mm: nat {:trigger WO.WalkOkF(na, c, np, g, mm)} | mm < m - 1
          ensures WO.WalkOkF(na, c, np, g, mm)
        {
          assert WO.WalkOkF(acts, c, np, g, mm + 1);
          assert WO.WalkOkRegF(r, cont, c, np, g, mm + 1);
        }
        WalkOkAtJmp(m - 1, na, c, pcj, np, g);
        assert WO.WalkOkRegF(r, cont, c, pcj, g, m);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          forall mm: nat {:trigger WO.WalkOkF(cont, c, np, g, mm)} | mm < m - 1
            ensures WO.WalkOkF(cont, c, np, g, mm)
          {
            assert WO.WalkOkF(acts, c, np, g, mm + 1);
            assert WO.WalkOkRegF(r, cont, c, np, g, mm + 1);
          }
          WalkOkAtJmp(m - 1, cont, c, pcj, np, g);
          assert WO.WalkOkRegF(r, cont, c, pcj, g, m);
        } else {
          // min>0 pins SetQuantToClock; min==0 layers/stars pin Fork: vacuous
          assert WO.WalkOkRegF(r, cont, c, pcj, g, m);
        }
      case Character(_) =>
        assert WO.WalkOkRegF(r, cont, c, pcj, g, m);
      case AnchorR(_) =>
        assert WO.WalkOkRegF(r, cont, c, pcj, g, m);
      case Disjunction(_, _) =>
        assert WO.WalkOkRegF(r, cont, c, pcj, g, m);
      case Group(_, _) =>
        assert WO.WalkOkRegF(r, cont, c, pcj, g, m);
      case LookaroundR(_, _) =>
      case Backreference(_) =>
  }

  // ===========================================================================
  // The composition lemma and its chain/rest companions
  // ===========================================================================

  /** Continuation-passing composition: a walk-guarded continuation at the
      block's exit makes `[Areg(Translate(re))] + cont` walk-guarded at the
      block's entry. Structural on `re`; the knots (star back-Jmp, do-while
      backward fork) recurse at strictly smaller fuel via the rest lemmas. */
  lemma WalkOkCompF(n: nat, re: R.regex, c: RB.code, pc1: nat, pc2: nat, cont: LS.Actions, g: bool)
    requires NR.PlusFragmentRE(re) && T.TransWf(re)
    requires NR.NfaRepRE(re, c, pc1, pc2)
    requires forall gp: bool, mm: nat {:trigger WO.WalkOkF(cont, c, pc2, gp, mm)} :: mm < n ==> WO.WalkOkF(cont, c, pc2, gp, mm)
    ensures WO.WalkOkF([LS.Areg(T.Translate(re))] + cont, c, pc1, g, n)
    decreases n, CP.rsize(re), 2
  {
    if n == 0 { return; }
    var trre := T.Translate(re);
    var tgt := [LS.Areg(trre)] + cont;
    assert tgt[0] == LS.Areg(trre) && tgt[1..] == cont;
    match re
    case Re_empty =>
      assert pc1 == pc2 && trre == L.Epsilon;
      if NR.GetPcRE(c, pc1).Some? && NR.GetPcRE(c, pc1).value.Jmp? {
        var np := NR.GetPcRE(c, pc1).value.jl;
        if np >= 0 {
          forall mm: nat {:trigger WO.WalkOkF(cont, c, np as nat, g, mm)} | mm < n - 1
            ensures WO.WalkOkF(cont, c, np as nat, g, mm)
          {
            assert WO.WalkOkF(cont, c, pc1, g, mm + 1);
          }
          WalkOkConsTransparent(n - 1, trre, cont, c, np as nat, g);
        }
      }
      assert WO.WalkOkF(cont, c, pc1, g, n - 1);
      assert WO.WalkOkRegF(trre, cont, c, pc1, g, n);
      assert WO.WalkOkF(tgt, c, pc1, g, n);
    case Re_character(ch) =>
      assert NR.GetPcRE(c, pc1) == Some(RB.Consume(T.ExpectationOf(ch))) && pc2 == pc1 + 1;
      assert WO.WalkOkF(cont, c, pc1 + 1, true, n - 1);
      assert WO.WalkOkRegF(trre, cont, c, pc1, g, n);
      assert WO.WalkOkF(tgt, c, pc1, g, n);
    case Re_anchor(a) =>
      assert NR.GetPcRE(c, pc1) == Some(RB.AnchorAssertion(a)) && pc2 == pc1 + 1;
      assert trre == L.AnchorR(T.TrAnchor(a));
      assert WO.WalkOkF(cont, c, pc1 + 1, g, n - 1);
      assert WO.WalkOkRegF(trre, cont, c, pc1, g, n);
      assert WO.WalkOkF(tgt, c, pc1, g, n);
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc2))
        && NR.NfaRepRE(r2, c, e1 + 1, pc2);
      assert trre == L.Disjunction(T.Translate(r1), T.Translate(r2));
      // right branch straight to the join
      WalkOkCompF(n - 1, r2, c, e1 + 1, pc2, cont, g);
      // left branch exits onto the join Jmp
      forall gp: bool, mm: nat {:trigger WO.WalkOkF(cont, c, e1, gp, mm)} | mm < n - 1
        ensures WO.WalkOkF(cont, c, e1, gp, mm)
      {
        WalkOkAtJmp(mm, cont, c, e1, pc2, gp);
      }
      WalkOkCompF(n - 1, r1, c, pc1 + 1, e1, cont, g);
      assert WO.WalkOkRegF(trre, cont, c, pc1, g, n);
      assert WO.WalkOkF(tgt, c, pc1, g, n);
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, c, pc1, e1) && NR.NfaRepRE(r2, c, e1, pc2);
      var tr1 := T.Translate(r1);
      var tr2 := T.Translate(r2);
      assert trre == L.Sequence(tr1, tr2);
      forall gp: bool, mm: nat {:trigger WO.WalkOkF([LS.Areg(tr2)] + cont, c, e1, gp, mm)} | mm < n - 1
        ensures WO.WalkOkF([LS.Areg(tr2)] + cont, c, e1, gp, mm)
      {
        WalkOkCompF(mm, r2, c, e1, pc2, cont, gp);
      }
      WalkOkCompF(n - 1, r1, c, pc1, e1, [LS.Areg(tr2)] + cont, g);
      assert [LS.Areg(tr1)] + ([LS.Areg(tr2)] + cont) == [LS.Areg(tr1), LS.Areg(tr2)] + cont;
      assert WO.WalkOkF([LS.Areg(tr1), LS.Areg(tr2)] + cont, c, pc1, g, n - 1);
      // the Jmp corner: both blocks empty and transparent
      if NR.GetPcRE(c, pc1).Some? && NR.GetPcRE(c, pc1).value.Jmp? {
        NfaRepREPins(r1, c, pc1, e1);
        NfaRepREPins(r2, c, e1, pc2);
        var np := NR.GetPcRE(c, pc1).value.jl;
        if np >= 0 {
          forall mm: nat {:trigger WO.WalkOkF(cont, c, np as nat, g, mm)} | mm < n - 1
            ensures WO.WalkOkF(cont, c, np as nat, g, mm)
          {
            assert WO.WalkOkF(cont, c, pc1, g, mm + 1);
          }
          WalkOkConsTransparent(n - 1, trre, cont, c, np as nat, g);
        }
      }
      assert WO.WalkOkRegF(trre, cont, c, pc1, g, n);
      assert WO.WalkOkF(tgt, c, pc1, g, n);
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pc2 == e1 + 1;
      var tr1 := T.Translate(r1);
      var gid: nat := cid as nat;
      assert trre == L.Group(gid, tr1);
      var rest := [LS.Aclose(gid)] + cont;
      forall gp: bool, mm: nat {:trigger WO.WalkOkF(rest, c, e1, gp, mm)} | mm < n - 1
        ensures WO.WalkOkF(rest, c, e1, gp, mm)
      {
        if mm > 0 {
          assert rest[0] == LS.Aclose(gid) && rest[1..] == cont;
          assert WO.WalkOkF(cont, c, e1 + 1, gp, mm - 1);
        }
      }
      WalkOkCompF(n - 1, r1, c, pc1 + 1, e1, rest, g);
      assert [LS.Areg(tr1)] + rest == [LS.Areg(tr1), LS.Aclose(gid)] + cont;
      assert WO.WalkOkF([LS.Areg(tr1), LS.Aclose(gid)] + cont, c, pc1 + 1, g, n - 1);
      assert WO.WalkOkRegF(trre, cont, c, pc1, g, n);
      assert WO.WalkOkF(tgt, c, pc1, g, n);
    case Re_lookaround(_, _, _) =>
      // excluded by PlusFragmentRE
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        // the star
        var e1: nat :| NR.GetPcRE(c, pc1) == Some(if q.greedy then RB.Fork(pc1 + 1, e1 + 2) else RB.Fork(e1 + 2, pc1 + 1))
          && NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, c, pc1 + 3, e1)
          && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(pc1))
          && pc2 == e1 + 2;
        var tr1 := T.Translate(r1);
        assert T.TrDelta(q) == LN.Inf;
        assert trre == L.Quantified(q.greedy, 0, LN.Inf, tr1);
        assert FS.NoiPred(LN.Inf) == LN.Inf;
        // the iteration lists, for every recorded input
        forall chk: LC.Input
          ensures WO.WalkOkF([LS.Areg(tr1), LS.Acheck(chk), LS.Areg(trre)] + cont, c, pc1 + 3, false, n - 1)
        {
          var rest := [LS.Acheck(chk), LS.Areg(trre)] + cont;
          forall gp: bool, mm: nat {:trigger WO.WalkOkF(rest, c, e1, gp, mm)} | mm < n - 1
            ensures WO.WalkOkF(rest, c, e1, gp, mm)
          {
            WalkOkStarRestF(mm, re, c, pc1, pc2, e1, cont, gp, chk);
          }
          WalkOkCompF(n - 1, r1, c, pc1 + 3, e1, rest, false);
          assert [LS.Areg(tr1)] + rest == [LS.Areg(tr1), LS.Acheck(chk), LS.Areg(trre)] + cont;
        }
        // the skip
        assert WO.WalkOkF(cont, c, pc2, g, n - 1);
        assert WO.WalkOkRegF(trre, cont, c, pc1, g, n);
        assert WO.WalkOkF(tgt, c, pc1, g, n);
      } else if q.max.Some? {
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid, r1, c, pc1, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid, r1, c, em, pc2);
        assert T.TrDelta(q) == LN.NN(kx);
        assert trre == L.Quantified(q.greedy, mn, LN.NN(kx), T.Translate(r1));
        assert CP.rsize(r1) < CP.rsize(re);
        WalkOkMinChainF(n, mn, kx, q.greedy, qid, r1, c, pc1, em, pc2, cont, g);
      } else {
        var mn := q.min as nat;
        var em: nat :| NR.NfaRepMinRE(mn - 1, qid, r1, c, pc1, em)
          && NR.GetPcRE(c, em) == Some(RB.SetQuantToClock(qid, false))
          && (exists e1: nat ::
                NR.NfaRepRE(r1, c, em + 1, e1)
                && NR.GetPcRE(c, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
                && pc2 == e1 + 1);
        var e1: nat :| NR.NfaRepRE(r1, c, em + 1, e1)
          && NR.GetPcRE(c, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pc2 == e1 + 1;
        assert T.TrDelta(q) == LN.Inf;
        assert trre == L.Quantified(q.greedy, mn, LN.Inf, T.Translate(r1));
        assert CP.rsize(r1) < CP.rsize(re);
        WalkOkPlusChainF(n, mn, q.greedy, qid, r1, c, pc1, em, e1, pc2, cont, g);
      }
  }

  /** The forced-copy chain of a BOUNDED quantifier: `[Areg r1{k, k+kx}] + cont`
      is guarded at each copy head; bottoms out in the optional layers. */
  lemma WalkOkMinChainF(n: nat, k: nat, kx: nat, greedy: bool, qid: R.quantid, r1: R.regex,
                        c: RB.code, pc1: nat, em: nat, pc2: nat, cont: LS.Actions, g: bool)
    requires NR.PlusFragmentRE(r1) && T.TransWf(r1)
    requires NR.NfaRepMinRE(k, qid, r1, c, pc1, em)
    requires NR.NfaRepOptRE(kx, greedy, qid, r1, c, em, pc2)
    requires forall gp: bool, mm: nat {:trigger WO.WalkOkF(cont, c, pc2, gp, mm)} :: mm < n ==> WO.WalkOkF(cont, c, pc2, gp, mm)
    ensures WO.WalkOkF([LS.Areg(L.Quantified(greedy, k, LN.NN(kx), T.Translate(r1)))] + cont, c, pc1, g, n)
    decreases n, CP.rsize(r1), 1
  {
    if n == 0 { return; }
    var tr1 := T.Translate(r1);
    var qk := L.Quantified(greedy, k, LN.NN(kx), tr1);
    var tgt := [LS.Areg(qk)] + cont;
    assert tgt[0] == LS.Areg(qk) && tgt[1..] == cont;
    if k == 0 {
      assert pc1 == em;
      WalkOkOptChainF(n, kx, greedy, qid, r1, c, pc1, pc2, cont, g);
    } else {
      var e1b: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qid, false))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1b)
        && NR.NfaRepMinRE(k - 1, qid, r1, c, e1b, em);
      var qk1 := L.Quantified(greedy, k - 1, LN.NN(kx), tr1);
      forall gp: bool, mm: nat {:trigger WO.WalkOkF([LS.Areg(qk1)] + cont, c, e1b, gp, mm)} | mm < n - 1
        ensures WO.WalkOkF([LS.Areg(qk1)] + cont, c, e1b, gp, mm)
      {
        WalkOkMinChainF(mm, k - 1, kx, greedy, qid, r1, c, e1b, em, pc2, cont, gp);
      }
      WalkOkCompF(n - 1, r1, c, pc1 + 1, e1b, [LS.Areg(qk1)] + cont, g);
      assert [LS.Areg(tr1)] + ([LS.Areg(qk1)] + cont) == [LS.Areg(tr1), LS.Areg(qk1)] + cont;
      assert WO.WalkOkF([LS.Areg(tr1), LS.Areg(qk1)] + cont, c, pc1 + 1, g, n - 1);
      assert WO.WalkOkRegF(qk, cont, c, pc1, g, n);
      assert WO.WalkOkF(tgt, c, pc1, g, n);
    }
  }

  /** The optional-layer chain: `[Areg r1{0, k}] + cont` is guarded at each
      layer's fork (a forward decision point); the spent bottom is
      transparent. */
  lemma WalkOkOptChainF(n: nat, k: nat, greedy: bool, qid: R.quantid, r1: R.regex,
                        c: RB.code, pc1: nat, pc2: nat, cont: LS.Actions, g: bool)
    requires NR.PlusFragmentRE(r1) && T.TransWf(r1)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, c, pc1, pc2)
    requires forall gp: bool, mm: nat {:trigger WO.WalkOkF(cont, c, pc2, gp, mm)} :: mm < n ==> WO.WalkOkF(cont, c, pc2, gp, mm)
    ensures WO.WalkOkF([LS.Areg(L.Quantified(greedy, 0, LN.NN(k), T.Translate(r1)))] + cont, c, pc1, g, n)
    decreases n, CP.rsize(r1), 0
  {
    if n == 0 { return; }
    var tr1 := T.Translate(r1);
    var qk := L.Quantified(greedy, 0, LN.NN(k), tr1);
    var tgt := [LS.Areg(qk)] + cont;
    assert tgt[0] == LS.Areg(qk) && tgt[1..] == cont;
    if k == 0 {
      // spent: transparent
      assert pc1 == pc2;
      if NR.GetPcRE(c, pc1).Some? && NR.GetPcRE(c, pc1).value.Jmp? {
        var np := NR.GetPcRE(c, pc1).value.jl;
        if np >= 0 {
          forall mm: nat {:trigger WO.WalkOkF(cont, c, np as nat, g, mm)} | mm < n - 1
            ensures WO.WalkOkF(cont, c, np as nat, g, mm)
          {
            assert WO.WalkOkF(cont, c, pc1, g, mm + 1);
          }
          WalkOkConsTransparent(n - 1, qk, cont, c, np as nat, g);
        }
      }
      assert WO.WalkOkF(cont, c, pc1, g, n - 1);
      assert WO.WalkOkRegF(qk, cont, c, pc1, g, n);
      assert WO.WalkOkF(tgt, c, pc1, g, n);
    } else {
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(if greedy then RB.Fork(pc1 + 1, pc2) else RB.Fork(pc2, pc1 + 1))
        && NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, c, pc1 + 3, e1)
        && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
        && NR.NfaRepOptRE(k - 1, greedy, qid, r1, c, e1 + 1, pc2);
      var qk1 := L.Quantified(greedy, 0, LN.NN(k - 1), tr1);
      assert FS.NoiPred(LN.NN(k)) == LN.NN(k - 1);
      // the iteration lists
      forall chk: LC.Input
        ensures WO.WalkOkF([LS.Areg(tr1), LS.Acheck(chk), LS.Areg(qk1)] + cont, c, pc1 + 3, false, n - 1)
      {
        var rest := [LS.Acheck(chk), LS.Areg(qk1)] + cont;
        forall gp: bool, mm: nat {:trigger WO.WalkOkF(rest, c, e1, gp, mm)} | mm < n - 1
          ensures WO.WalkOkF(rest, c, e1, gp, mm)
        {
          WalkOkOptRestF(mm, k - 1, greedy, qid, r1, c, e1, pc2, cont, gp, chk);
        }
        WalkOkCompF(n - 1, r1, c, pc1 + 3, e1, rest, false);
        assert [LS.Areg(tr1)] + rest == [LS.Areg(tr1), LS.Acheck(chk), LS.Areg(qk1)] + cont;
      }
      // the skip
      assert WO.WalkOkF(cont, c, pc2, g, n - 1);
      assert WO.WalkOkRegF(qk, cont, c, pc1, g, n);
      assert WO.WalkOkF(tgt, c, pc1, g, n);
    }
  }

  /** A bounded layer's iteration continuation `[Acheck, Areg r1{0,k}] + cont`
      sitting at the layer's `EndLoop`: the check falls through onto the next
      layer's chain. */
  lemma WalkOkOptRestF(m: nat, k: nat, greedy: bool, qid: R.quantid, r1: R.regex,
                       c: RB.code, e1: nat, pc2: nat, cont: LS.Actions, gp: bool, chk: LC.Input)
    requires NR.PlusFragmentRE(r1) && T.TransWf(r1)
    requires NR.GetPcRE(c, e1) == Some(RB.EndLoop)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, c, e1 + 1, pc2)
    requires forall gp2: bool, mm: nat {:trigger WO.WalkOkF(cont, c, pc2, gp2, mm)} :: mm < m ==> WO.WalkOkF(cont, c, pc2, gp2, mm)
    ensures WO.WalkOkF([LS.Acheck(chk), LS.Areg(L.Quantified(greedy, 0, LN.NN(k), T.Translate(r1)))] + cont, c, e1, gp, m)
    decreases m, CP.rsize(r1), 0
  {
    if m == 0 { return; }
    var qk := L.Quantified(greedy, 0, LN.NN(k), T.Translate(r1));
    var tgt := [LS.Acheck(chk), LS.Areg(qk)] + cont;
    assert tgt[0] == LS.Acheck(chk) && tgt[1..] == [LS.Areg(qk)] + cont;
    assert !AR.BackForkAt(c, e1);
    WalkOkOptChainF(m - 1, k, greedy, qid, r1, c, e1 + 1, pc2, cont, true);
    assert WO.WalkOkF([LS.Areg(qk)] + cont, c, e1 + 1, true, m - 1);
    assert WO.WalkOkF(tgt, c, e1, gp, m);
  }

  /** The star's iteration continuation `[Acheck, Areg r1*] + cont` sitting at
      the star's `EndLoop`: the check falls through onto the back-Jmp, and the
      KNOT re-enters the star head at strictly smaller fuel. */
  lemma WalkOkStarRestF(m: nat, re: R.regex, c: RB.code, pc1: nat, pc2: nat, e1: nat,
                        cont: LS.Actions, gp: bool, chk: LC.Input)
    requires NR.PlusFragmentRE(re) && T.TransWf(re)
    requires NR.NfaRepRE(re, c, pc1, pc2)
    requires NR.GetPcRE(c, e1) == Some(RB.EndLoop)
    requires NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(pc1))
    requires forall gp2: bool, mm: nat {:trigger WO.WalkOkF(cont, c, pc2, gp2, mm)} :: mm < m ==> WO.WalkOkF(cont, c, pc2, gp2, mm)
    ensures WO.WalkOkF([LS.Acheck(chk), LS.Areg(T.Translate(re))] + cont, c, e1, gp, m)
    decreases m, CP.rsize(re), 0
  {
    if m == 0 { return; }
    var trre := T.Translate(re);
    var tgt := [LS.Acheck(chk), LS.Areg(trre)] + cont;
    assert tgt[0] == LS.Acheck(chk) && tgt[1..] == [LS.Areg(trre)] + cont;
    assert !AR.BackForkAt(c, e1);
    // the fall-through lands on the back-Jmp: route to the star head (KNOT)
    forall mm: nat {:trigger WO.WalkOkF([LS.Areg(trre)] + cont, c, pc1, true, mm)} | mm < m - 1
      ensures WO.WalkOkF([LS.Areg(trre)] + cont, c, pc1, true, mm)
    {
      forall gp2: bool, mm2: nat {:trigger WO.WalkOkF(cont, c, pc2, gp2, mm2)} | mm2 < mm
        ensures WO.WalkOkF(cont, c, pc2, gp2, mm2)
      {
        assert WO.WalkOkF(cont, c, pc2, gp2, mm2);
      }
      WalkOkCompF(mm, re, c, pc1, pc2, cont, true);
    }
    WalkOkAtJmp(m - 1, [LS.Areg(trre)] + cont, c, e1 + 1, pc1, true);
    assert WO.WalkOkF([LS.Areg(trre)] + cont, c, e1 + 1, true, m - 1);
    assert WO.WalkOkF(tgt, c, e1, gp, m);
  }

  /** The do-while chain: `[Areg r1{k,}] + cont` is guarded at each copy head;
      the `k == 1` bottom is the SEAM (the checked continuation demanded by
      the walk guard's seam case), whose rest sits at the backward fork. */
  lemma WalkOkPlusChainF(n: nat, k: nat, greedy: bool, qid: R.quantid, r1: R.regex,
                         c: RB.code, pc1: nat, em: nat, e1: nat, pc2: nat, cont: LS.Actions, g: bool)
    requires k >= 1
    requires NR.PlusFragmentRE(r1) && T.TransWf(r1)
    requires NR.NfaRepMinRE(k - 1, qid, r1, c, pc1, em)
    requires NR.GetPcRE(c, em) == Some(RB.SetQuantToClock(qid, false))
    requires NR.NfaRepRE(r1, c, em + 1, e1)
    requires NR.GetPcRE(c, e1) == Some(if greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
    requires pc2 == e1 + 1
    requires forall gp: bool, mm: nat {:trigger WO.WalkOkF(cont, c, pc2, gp, mm)} :: mm < n ==> WO.WalkOkF(cont, c, pc2, gp, mm)
    ensures WO.WalkOkF([LS.Areg(L.Quantified(greedy, k, LN.Inf, T.Translate(r1)))] + cont, c, pc1, g, n)
    decreases n, CP.rsize(r1), 1
  {
    if n == 0 { return; }
    var tr1 := T.Translate(r1);
    var qk := L.Quantified(greedy, k, LN.Inf, tr1);
    var tgt := [LS.Areg(qk)] + cont;
    assert tgt[0] == LS.Areg(qk) && tgt[1..] == cont;
    if k > 1 {
      var e1b: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qid, false))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1b)
        && NR.NfaRepMinRE(k - 2, qid, r1, c, e1b, em);
      var qk1 := L.Quantified(greedy, k - 1, LN.Inf, tr1);
      forall gp: bool, mm: nat {:trigger WO.WalkOkF([LS.Areg(qk1)] + cont, c, e1b, gp, mm)} | mm < n - 1
        ensures WO.WalkOkF([LS.Areg(qk1)] + cont, c, e1b, gp, mm)
      {
        WalkOkPlusChainF(mm, k - 1, greedy, qid, r1, c, e1b, em, e1, pc2, cont, gp);
      }
      WalkOkCompF(n - 1, r1, c, pc1 + 1, e1b, [LS.Areg(qk1)] + cont, g);
      assert [LS.Areg(tr1)] + ([LS.Areg(qk1)] + cont) == [LS.Areg(tr1), LS.Areg(qk1)] + cont;
      assert WO.WalkOkF([LS.Areg(tr1), LS.Areg(qk1)] + cont, c, pc1 + 1, g, n - 1);
      assert WO.WalkOkRegF(qk, cont, c, pc1, g, n);
      assert WO.WalkOkF(tgt, c, pc1, g, n);
    } else {
      // k == 1: the SEAM — the stamp is at pc1
      assert pc1 == em;
      var q0L := L.Quantified(greedy, 0, LN.Inf, tr1);
      forall chk: LC.Input
        ensures WO.WalkOkF([LS.Areg(tr1), LS.Acheck(chk), LS.Areg(q0L)] + cont, c, pc1 + 1, g, n - 1)
      {
        var rest := [LS.Acheck(chk), LS.Areg(q0L)] + cont;
        forall gp: bool, mm: nat {:trigger WO.WalkOkF(rest, c, e1, gp, mm)} | mm < n - 1
          ensures WO.WalkOkF(rest, c, e1, gp, mm)
        {
          WalkOkDoWhileRestF(mm, greedy, qid, r1, c, em, e1, pc2, cont, gp, chk);
        }
        WalkOkCompF(n - 1, r1, c, em + 1, e1, rest, g);
        assert [LS.Areg(tr1)] + rest == [LS.Areg(tr1), LS.Acheck(chk), LS.Areg(q0L)] + cont;
      }
      assert WO.WalkOkRegF(qk, cont, c, pc1, g, n);
      assert WO.WalkOkF(tgt, c, pc1, g, n);
    }
  }

  /** The do-while's iteration continuation `[Acheck, Areg r1*] + cont`
      sitting AT the backward fork: the check dissolves (zero-width), the
      loop-view star's demands are the KNOT (the same checked continuation at
      strictly smaller fuel) and the skip onto the exit arm. */
  lemma WalkOkDoWhileRestF(m: nat, greedy: bool, qid: R.quantid, r1: R.regex,
                           c: RB.code, em: nat, e1: nat, pc2: nat, cont: LS.Actions, gp: bool, chk: LC.Input)
    requires NR.PlusFragmentRE(r1) && T.TransWf(r1)
    requires NR.NfaRepRE(r1, c, em + 1, e1)
    requires NR.GetPcRE(c, e1) == Some(if greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
    requires pc2 == e1 + 1
    requires forall gp2: bool, mm: nat {:trigger WO.WalkOkF(cont, c, pc2, gp2, mm)} :: mm < m ==> WO.WalkOkF(cont, c, pc2, gp2, mm)
    ensures WO.WalkOkF([LS.Acheck(chk), LS.Areg(L.Quantified(greedy, 0, LN.Inf, T.Translate(r1)))] + cont, c, e1, gp, m)
    decreases m, CP.rsize(r1), 0
  {
    if m == 0 { return; }
    var tr1 := T.Translate(r1);
    var q0L := L.Quantified(greedy, 0, LN.Inf, tr1);
    var tgt := [LS.Acheck(chk), LS.Areg(q0L)] + cont;
    assert tgt[0] == LS.Acheck(chk) && tgt[1..] == [LS.Areg(q0L)] + cont;
    NR.NfaRepIncrRE(r1, c, em + 1, e1);
    assert em < e1;
    assert AR.BackForkAt(c, e1);
    assert FS.NoiPred(LN.Inf) == LN.Inf;
    // the dissolved check exposes the loop-view star at the fork
    if m >= 2 {
      var lv := [LS.Areg(q0L)] + cont;
      assert lv[0] == LS.Areg(q0L) && lv[1..] == cont;
      // the KNOT: the checked iteration lists at strictly smaller fuel
      forall chk2: LC.Input
        ensures WO.WalkOkF([LS.Areg(tr1), LS.Acheck(chk2), LS.Areg(q0L)] + cont, c, em + 1, true, m - 2)
      {
        var rest := [LS.Acheck(chk2), LS.Areg(q0L)] + cont;
        forall gp2: bool, mm: nat {:trigger WO.WalkOkF(rest, c, e1, gp2, mm)} | mm < m - 2
          ensures WO.WalkOkF(rest, c, e1, gp2, mm)
        {
          WalkOkDoWhileRestF(mm, greedy, qid, r1, c, em, e1, pc2, cont, gp2, chk2);
        }
        WalkOkCompF(m - 2, r1, c, em + 1, e1, rest, true);
        assert [LS.Areg(tr1)] + rest == [LS.Areg(tr1), LS.Acheck(chk2), LS.Areg(q0L)] + cont;
      }
      // the skip onto the exit arm
      assert WO.WalkOkF(cont, c, pc2, true, m - 2);
      assert WO.WalkOkRegF(q0L, cont, c, e1, true, m - 1);
      assert WO.WalkOkF(lv, c, e1, true, m - 1);
    } else {
      assert WO.WalkOkF([LS.Areg(q0L)] + cont, c, e1, true, m - 1);
    }
    assert WO.WalkOkF(tgt, c, e1, gp, m);
  }

  // ===========================================================================
  // The entry theorem
  // ===========================================================================

  /** Compiled plus-fragment code satisfies the walk guard for the entry
      continuation `[Areg(Translate(re))]` at pc 0, at every guard bit. */
  lemma WalkOkEntry(re: R.regex)
    requires NR.PlusFragmentRE(re) && T.TransWf(re)
    ensures forall g: bool ::
      WO.WalkOk([LS.Areg(T.Translate(re))], CP.compile_to_bytecode(re), 0, g)
  {
    var code := CP.compile_to_bytecode(re);
    var next := CP.compile(re, 0, CP.Progress).1;
    NR.CompileToBytecodeRepPlus(re);
    assert NR.NfaRepRE(re, code, 0, next as nat);
    assert NR.GetPcRE(code, next as nat) == Some(RB.Accept);
    forall g: bool
      ensures WO.WalkOk([LS.Areg(T.Translate(re))], code, 0, g)
    {
      var nil: LS.Actions := [];
      forall n: nat {:trigger WO.WalkOkF([LS.Areg(T.Translate(re))], code, 0, g, n)}
        ensures WO.WalkOkF([LS.Areg(T.Translate(re))], code, 0, g, n)
      {
        forall gp: bool, mm: nat {:trigger WO.WalkOkF(nil, code, next as nat, gp, mm)} | mm < n
          ensures WO.WalkOkF(nil, code, next as nat, gp, mm)
        {
          assert |nil| == 0;
        }
        WalkOkCompF(n, re, code, 0, next as nat, nil, g);
        assert [LS.Areg(T.Translate(re))] + nil == [LS.Areg(T.Translate(re))];
      }
    }
  }
}
