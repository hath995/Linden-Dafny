// §2.5b STAGE 2, RUNG E (engine side) — the ReconstructNulled code and the null
// interpreter.
//
// `FReconstructPlus` fills in the captures of a nulled greedy CIN `+` by running
// ONE epsilon closure (`FNullInterp` = `FAdvanceEpsilon`, no consumption) over
// `compile_reconstruct_nulled(body)` from the stamped position. That code is a
// LOOP-FREE DAG (characters compile to `Fail`, quantifiers to a clock-mark or
// the nested stamp, captures to the two `SetRegisterToCP`, lookarounds to the
// oracle gates), so the closure is a priority DFS whose FIRST accepting path is
// the body's top-priority zero-width path — exactly `TR.FirstEmptyPathR`, which
// the tree tower's stamp rule (rung B) chains.
//
// This module states that correspondence at the REGISTER level:
//   * `NfaRepNulledRE` — the layout of ReconstructNulled code, + compiler
//     adherence (`CompileNfaRepNulledRE`);
//   * `NulledWrites(qm, re, inp)` — the register writes of the first empty path
//     (the `Write`-level twin of `FirstEmptyPathR`; nested CIN-greedy `+`s
//     contribute their stamp only — `FNulledChildren` chains their own path);
//   * `NulledRunRE` — THE structural theorem: the closure entering a region at
//     its head leaves it (a) at the region's exit with `NulledWrites` applied at
//     strictly increasing clocks, or (b) with no thread at all, pending
//     alternatives inside the region being JUNK (every path dies inside the
//     region or lands on an already-processed pc), so the `processed` dedup
//     only ever drops threads whose future is known to fail;
//   * `NullInterpNulled` — the top-level statement over `FNullInterp`.
// The readout (`GmOfLive` of the reconstructed registers) is the second file.
module LindenElkNulledRecon {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import RA = Anchors
  import T = LindenElkTranslate
  import NUL = LindenElkNullable
  import NR = LindenElkNfaRep
  import AR = LindenElkActionsRep
  import TR = LindenElkTreeRep
  import LC = Chars
  import LCdn = Cdn

  // ===========================================================================
  // 1. The layout of ReconstructNulled code (mirror of `CP.compile(_, _,
  //    ReconstructNulled)`, cf. `NR.NfaRepRE` for Progress mode).
  // ===========================================================================

  ghost predicate PositiveLk(la: R.lookaround) { la.Lookahead? || la.Lookbehind? }

  /** The CDN-greedy `+` (`CheckNullable`) stays out of the fragment. */
  ghost predicate NoCdnPlusRE(re: R.regex)
    decreases re
  {
    match re
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => NoCdnPlusRE(r1) && NoCdnPlusRE(r2)
    case Re_con(r1, r2) => NoCdnPlusRE(r1) && NoCdnPlusRE(r2)
    case Re_quant(nul, qid, q, r1) =>
      !(q.min != 0 && q.max == None && nul == R.CDNullable && q.greedy) && NoCdnPlusRE(r1)
    case Re_capture(_, r1) => NoCdnPlusRE(r1)
    case Re_lookaround(_, _, r1) => NoCdnPlusRE(r1)
  }

  ghost predicate NfaRepNulledRE(re: R.regex, c: RB.code, pc1: nat, pc2: nat)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty => pc1 == pc2
    case Re_character(_) => pc2 == pc1 + 1 && NR.GetPcRE(c, pc1) == Some(RB.Fail)
    case Re_anchor(a) => pc2 == pc1 + 1 && NR.GetPcRE(c, pc1) == Some(RB.AnchorAssertion(a))
    case Re_alt(r1, r2) =>
      exists e1: nat ::
        NR.GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
        && NfaRepNulledRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc2))
        && NfaRepNulledRE(r2, c, e1 + 1, pc2)
    case Re_con(r1, r2) =>
      exists e1: nat :: NfaRepNulledRE(r1, c, pc1, e1) && NfaRepNulledRE(r2, c, e1, pc2)
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 then pc1 == pc2
      else if nul == R.NonNullable then pc2 == pc1 + 1 && NR.GetPcRE(c, pc1) == Some(RB.Fail)
      else if q.max == None && nul == R.CINullable && q.greedy then
        pc2 == pc1 + 1 && NR.GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qid, true))
      else if q.max == None && nul == R.CDNullable && q.greedy then
        pc2 == pc1 + 2 && NR.GetPcRE(c, pc1) == Some(RB.CheckNullable(qid))
        && NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qid, true))
      else
        NR.GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qid, false))
        && NfaRepNulledRE(r1, c, pc1 + 1, pc2)
    case Re_capture(cid, r1) =>
      exists e1: nat ::
        NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NfaRepNulledRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pc2 == e1 + 1
    case Re_lookaround(lid, la, _) =>
      pc2 == pc1 + 1
      && NR.GetPcRE(c, pc1) == Some(if PositiveLk(la) then RB.CheckOracle(lid) else RB.NegCheckOracle(lid))
  }

  /** Appending code after the region keeps the layout. */
  lemma NfaRepNulledExtend(re: R.regex, c: RB.code, start: nat, endl: nat, suffix: RB.code)
    requires NfaRepNulledRE(re, c, start, endl)
    ensures NfaRepNulledRE(re, c + suffix, start, endl)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) => NR.GetSuffixRE(c, suffix, start, RB.Fail);
    case Re_anchor(a) => NR.GetSuffixRE(c, suffix, start, RB.AnchorAssertion(a));
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(c, start) == Some(RB.Fork(start + 1, e1 + 1))
                     && NfaRepNulledRE(r1, c, start + 1, e1)
                     && NR.GetPcRE(c, e1) == Some(RB.Jmp(endl))
                     && NfaRepNulledRE(r2, c, e1 + 1, endl);
      NR.GetSuffixRE(c, suffix, start, RB.Fork(start + 1, e1 + 1));
      NfaRepNulledExtend(r1, c, start + 1, e1, suffix);
      NR.GetSuffixRE(c, suffix, e1, RB.Jmp(endl));
      NfaRepNulledExtend(r2, c, e1 + 1, endl, suffix);
    case Re_con(r1, r2) =>
      var e1: nat :| NfaRepNulledRE(r1, c, start, e1) && NfaRepNulledRE(r2, c, e1, endl);
      NfaRepNulledExtend(r1, c, start, e1, suffix);
      NfaRepNulledExtend(r2, c, e1, endl, suffix);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 {
      } else if nul == R.NonNullable {
        NR.GetSuffixRE(c, suffix, start, RB.Fail);
      } else if q.max == None && nul == R.CINullable && q.greedy {
        NR.GetSuffixRE(c, suffix, start, RB.SetQuantToClock(qid, true));
      } else if q.max == None && nul == R.CDNullable && q.greedy {
        NR.GetSuffixRE(c, suffix, start, RB.CheckNullable(qid));
        NR.GetSuffixRE(c, suffix, start + 1, RB.SetQuantToClock(qid, true));
      } else {
        NR.GetSuffixRE(c, suffix, start, RB.SetQuantToClock(qid, false));
        NfaRepNulledExtend(r1, c, start + 1, endl, suffix);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(c, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
                     && NfaRepNulledRE(r1, c, start + 1, e1)
                     && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
                     && endl == e1 + 1;
      NR.GetSuffixRE(c, suffix, start, RB.SetRegisterToCP(CP.start_reg(cid)));
      NfaRepNulledExtend(r1, c, start + 1, e1, suffix);
      NR.GetSuffixRE(c, suffix, e1, RB.SetRegisterToCP(CP.end_reg(cid)));
    case Re_lookaround(lid, la, _) =>
      NR.GetSuffixRE(c, suffix, start, if PositiveLk(la) then RB.CheckOracle(lid) else RB.NegCheckOracle(lid));
  }

  /** Label arithmetic of the ReconstructNulled compiler. */
  lemma FreshNulledRE(re: R.regex, start: nat, tl: CP.treelist, next: int)
    requires CP.compile(re, start, CP.ReconstructNulled) == (tl, next)
    ensures next == start + |NR.Flat(tl)|
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      var (l1, f1) := CP.compile(r1, start + 1, CP.ReconstructNulled);
      var (l2, f2) := CP.compile(r2, f1 + 1, CP.ReconstructNulled);
      FreshNulledRE(r1, start + 1, l1, f1);
      FreshNulledRE(r2, (f1 + 1) as nat, l2, f2);
      NR.ChainFour(CP.Leaf([RB.Fork(start + 1, f1 + 1)]), l1, CP.Leaf([RB.Jmp(f2)]), l2);
    case Re_con(r1, r2) =>
      var (l1, f1) := CP.compile(r1, start, CP.ReconstructNulled);
      var (l2, f2) := CP.compile(r2, f1, CP.ReconstructNulled);
      FreshNulledRE(r1, start, l1, f1);
      FreshNulledRE(r2, f1 as nat, l2, f2);
      NR.FlattenApp(l1, NR.Flat(l2));
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 {
      } else if nul == R.NonNullable {
      } else if q.max == None && nul == R.CINullable && q.greedy {
      } else if q.max == None && nul == R.CDNullable && q.greedy {
      } else {
        var (l1, f1) := CP.compile(r1, start + 1, CP.ReconstructNulled);
        FreshNulledRE(r1, start + 1, l1, f1);
        NR.FlattenApp(CP.Leaf([RB.SetQuantToClock(qid, false)]), NR.Flat(l1));
        assert NR.Flat(tl) == [RB.SetQuantToClock(qid, false)] + NR.Flat(l1);
      }
    case Re_capture(cid, r1) =>
      var (l1, f1) := CP.compile(r1, start + 1, CP.ReconstructNulled);
      FreshNulledRE(r1, start + 1, l1, f1);
      NR.ChainThree(CP.Leaf([RB.SetRegisterToCP(CP.start_reg(cid))]), l1, CP.Leaf([RB.SetRegisterToCP(CP.end_reg(cid))]));
    case Re_lookaround(_, _, _) =>
  }

  /** One unfolding of the compiler at an alternation (ReconstructNulled mode). */
  lemma CompileAltShape(r1: R.regex, r2: R.regex, start: nat)
    ensures var (l1, f1) := CP.compile(r1, start + 1, CP.ReconstructNulled);
            var (l2, f2) := CP.compile(r2, f1 + 1, CP.ReconstructNulled);
            CP.compile(R.Re_alt(r1, r2), start, CP.ReconstructNulled)
              == (CP.chain([CP.Leaf([RB.Fork(start + 1, f1 + 1)]), l1, CP.Leaf([RB.Jmp(f2)]), l2]), f2)
  {}

  /** The alt arm's assembly, in a context holding only the two sub-layouts. */
  lemma AltAssemble(re: R.regex, r1: R.regex, r2: R.regex, start: nat, tl: CP.treelist, next: int, prev: RB.code,
                    l1: CP.treelist, f1: int, l2: CP.treelist, f2: int)
    requires re == R.Re_alt(r1, r2)
    requires start == |prev| && f1 >= start + 1 && f2 >= f1 + 1 && next == f2
    requires tl == CP.chain([CP.Leaf([RB.Fork(start + 1, f1 + 1)]), l1, CP.Leaf([RB.Jmp(f2)]), l2])
    requires f1 == start + 1 + |NR.Flat(l1)| && f2 == f1 + 1 + |NR.Flat(l2)|
    requires NfaRepNulledRE(r1, prev + [RB.Fork(start + 1, f1 + 1)] + NR.Flat(l1), start + 1, f1 as nat)
    requires NfaRepNulledRE(r2, prev + [RB.Fork(start + 1, f1 + 1)] + NR.Flat(l1) + [RB.Jmp(f2)] + NR.Flat(l2), (f1 + 1) as nat, f2 as nat)
    ensures NfaRepNulledRE(re, prev + NR.Flat(tl), start, next as nat)
  {
    hide *;
    var fk := CP.Leaf([RB.Fork(start + 1, f1 + 1)]);
    var jp := CP.Leaf([RB.Jmp(f2)]);
    NR.ChainFour(fk, l1, jp, l2);
    assert NR.Flat(fk) == [RB.Fork(start + 1, f1 + 1)] && NR.Flat(jp) == [RB.Jmp(f2)] by {
      reveal NR.Flat, CP.tl_flatten;
    }
    var code := prev + NR.Flat(tl);
    assert NR.Flat(tl) == [RB.Fork(start + 1, f1 + 1)] + NR.Flat(l1) + [RB.Jmp(f2)] + NR.Flat(l2);
    var pre1 := prev + [RB.Fork(start + 1, f1 + 1)];
    NfaRepNulledExtend(r1, pre1 + NR.Flat(l1), start + 1, f1 as nat, [RB.Jmp(f2)] + NR.Flat(l2));
    assert (pre1 + NR.Flat(l1)) + ([RB.Jmp(f2)] + NR.Flat(l2)) == code;
    var pre2 := prev + [RB.Fork(start + 1, f1 + 1)] + NR.Flat(l1) + [RB.Jmp(f2)];
    assert pre2 + NR.Flat(l2) == code;
    assert NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, f1 + 1)) by {
      reveal NR.GetPcRE;
      assert code[start] == NR.Flat(tl)[0] == RB.Fork(start + 1, f1 + 1);
    }
    assert NR.GetPcRE(code, f1 as nat) == Some(RB.Jmp(f2)) by {
      reveal NR.GetPcRE;
      assert code[f1] == pre2[f1] == RB.Jmp(f2);
    }
    assert NfaRepNulledRE(re, code, start, next as nat) by {
      reveal NfaRepNulledRE;
    }
  }

  /** Compiler adherence: `compile(re, start, ReconstructNulled)` placed after
      `prev` (of length `start`) lays out `NfaRepNulledRE(re, ·, start, next)`. */
  lemma CompileNfaRepNulledRE(re: R.regex, start: nat, tl: CP.treelist, next: int, prev: RB.code)
    requires CP.compile(re, start, CP.ReconstructNulled) == (tl, next)
    requires start == |prev|
    ensures next >= 0 && NfaRepNulledRE(re, prev + NR.Flat(tl), start, next as nat)
    decreases CP.rsize(re), 1
  {
    FreshNulledRE(re, start, tl, next);
    match re
    case Re_empty =>
      assert prev + NR.Flat(tl) == prev;
    case Re_character(_) =>
      assert NR.Flat(tl) == [RB.Fail];
      NR.GetFirstRE(NR.Flat(tl), prev);
    case Re_anchor(a) =>
      assert NR.Flat(tl) == [RB.AnchorAssertion(a)];
      NR.GetFirstRE(NR.Flat(tl), prev);
    case Re_lookaround(lid, la, _) =>
      assert NR.Flat(tl) == [if PositiveLk(la) then RB.CheckOracle(lid) else RB.NegCheckOracle(lid)];
      NR.GetFirstRE(NR.Flat(tl), prev);
    case Re_alt(r1, r2) =>
      assert {:split_here} true;
      CompileAltShape(r1, r2, start);
      hide CP.compile;
      var (l1, f1) := CP.compile(r1, start + 1, CP.ReconstructNulled);
      var (l2, f2) := CP.compile(r2, f1 + 1, CP.ReconstructNulled);
      var fk := CP.Leaf([RB.Fork(start + 1, f1 + 1)]);
      var jp := CP.Leaf([RB.Jmp(f2)]);
      assert tl == CP.chain([fk, l1, jp, l2]) && next == f2;
      FreshNulledRE(r1, start + 1, l1, f1);
      FreshNulledRE(r2, (f1 + 1) as nat, l2, f2);
      var pre1 := prev + [RB.Fork(start + 1, f1 + 1)];
      assert {:split_here} true;
      CompileNfaRepNulledRE(r1, start + 1, l1, f1, pre1);
      assert {:split_here} true;
      var pre2 := prev + [RB.Fork(start + 1, f1 + 1)] + NR.Flat(l1) + [RB.Jmp(f2)];
      assert |pre2| == f1 + 1;
      CompileNfaRepNulledRE(r2, (f1 + 1) as nat, l2, f2, pre2);
      assert {:split_here} true;
      AltAssemble(re, r1, r2, start, tl, next, prev, l1, f1, l2, f2);
    case Re_con(r1, r2) =>
      assert {:split_here} true;
      var (l1, f1) := CP.compile(r1, start, CP.ReconstructNulled);
      var (l2, f2) := CP.compile(r2, f1, CP.ReconstructNulled);
      FreshNulledRE(r1, start, l1, f1);
      FreshNulledRE(r2, f1 as nat, l2, f2);
      NR.FlattenApp(l1, NR.Flat(l2));
      assert NR.Flat(tl) == NR.Flat(l1) + NR.Flat(l2);
      CompileNfaRepNulledRE(r1, start, l1, f1, prev);
      NfaRepNulledExtend(r1, prev + NR.Flat(l1), start, f1 as nat, NR.Flat(l2));
      assert (prev + NR.Flat(l1)) + NR.Flat(l2) == prev + NR.Flat(tl);
      assert |prev + NR.Flat(l1)| == f1;
      CompileNfaRepNulledRE(r2, f1 as nat, l2, f2, prev + NR.Flat(l1));
      assert NfaRepNulledRE(r1, prev + NR.Flat(tl), start, f1 as nat)
          && NfaRepNulledRE(r2, prev + NR.Flat(tl), f1 as nat, f2 as nat);
    case Re_quant(nul, qid, q, r1) =>
      assert {:split_here} true;
      if q.min == 0 {
        assert prev + NR.Flat(tl) == prev;
      } else if nul == R.NonNullable {
        assert NR.Flat(tl) == [RB.Fail];
        NR.GetFirstRE(NR.Flat(tl), prev);
      } else if q.max == None && nul == R.CINullable && q.greedy {
        assert NR.Flat(tl) == [RB.SetQuantToClock(qid, true)];
        NR.GetFirstRE(NR.Flat(tl), prev);
      } else if q.max == None && nul == R.CDNullable && q.greedy {
        assert NR.Flat(tl) == [RB.CheckNullable(qid), RB.SetQuantToClock(qid, true)];
        NR.GetPrefixRE(NR.Flat(tl), 0, prev);
        NR.GetPrefixRE(NR.Flat(tl), 1, prev);
      } else {
        var (l1, f1) := CP.compile(r1, start + 1, CP.ReconstructNulled);
        FreshNulledRE(r1, start + 1, l1, f1);
        NR.FlattenApp(CP.Leaf([RB.SetQuantToClock(qid, false)]), NR.Flat(l1));
        assert NR.Flat(tl) == [RB.SetQuantToClock(qid, false)] + NR.Flat(l1);
        var pre1 := prev + [RB.SetQuantToClock(qid, false)];
        CompileNfaRepNulledRE(r1, start + 1, l1, f1, pre1);
        assert pre1 + NR.Flat(l1) == prev + NR.Flat(tl);
        NR.GetFirstRE(NR.Flat(tl), prev);
        assert NR.GetPcRE(prev + NR.Flat(tl), start) == Some(RB.SetQuantToClock(qid, false));
        assert NfaRepNulledRE(r1, prev + NR.Flat(tl), start + 1, f1 as nat);
      }
    case Re_capture(cid, r1) =>
      assert {:split_here} true;
      var (l1, f1) := CP.compile(r1, start + 1, CP.ReconstructNulled);
      FreshNulledRE(r1, start + 1, l1, f1);
      var op := [RB.SetRegisterToCP(CP.start_reg(cid))];
      var cl := [RB.SetRegisterToCP(CP.end_reg(cid))];
      NR.ChainThree(CP.Leaf(op), l1, CP.Leaf(cl));
      assert NR.Flat(tl) == op + NR.Flat(l1) + cl;
      var pre1 := prev + op;
      CompileNfaRepNulledRE(r1, start + 1, l1, f1, pre1);
      NfaRepNulledExtend(r1, pre1 + NR.Flat(l1), start + 1, f1 as nat, cl);
      assert (pre1 + NR.Flat(l1)) + cl == prev + NR.Flat(tl);
      NR.GetFirstRE(NR.Flat(tl), prev);
      assert |pre1 + NR.Flat(l1)| == f1;
      NR.GetFirstRE(cl, pre1 + NR.Flat(l1));
      assert NR.GetPcRE(prev + NR.Flat(tl), start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
          && NfaRepNulledRE(r1, prev + NR.Flat(tl), start + 1, f1 as nat)
          && NR.GetPcRE(prev + NR.Flat(tl), f1 as nat) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
          && next == f1 + 1;
  }

  /** `compile_reconstruct_nulled(re)` = the region `[0, n)` followed by `Accept`. */
  lemma CompileReconstructNulledLayout(re: R.regex)
    ensures var c := CP.compile_reconstruct_nulled(re);
      var n := |c| - 1;
      n >= 0 && NfaRepNulledRE(re, c, 0, n as nat) && c[n] == RB.Accept
  {
    var (tl, next) := CP.compile(re, 0, CP.ReconstructNulled);
    FreshNulledRE(re, 0, tl, next);
    CompileNfaRepNulledRE(re, 0, tl, next, []);
    NR.FlattenApp(tl, [RB.Accept]);
    assert CP.compile_reconstruct_nulled(re) == NR.Flat(tl) + [RB.Accept];
    assert [] + NR.Flat(tl) == NR.Flat(tl);
    NfaRepNulledExtend(re, NR.Flat(tl), 0, next as nat, [RB.Accept]);
  }

  // ===========================================================================
  // 2. Shape facts of the region: forward-only jumps, no consuming/looping/
  //    oracle-writing instruction, successors inside the region.
  // ===========================================================================

  ghost predicate ForwardOnly(c: RB.code) {
    forall p: nat :: p < |c| ==>
      (c[p].Jmp? ==> c[p].jl > p) && (c[p].Fork? ==> c[p].fl1 > p && c[p].fl2 > p)
  }

  /** The instruction kinds ReconstructNulled code may contain (under `NoCdnPlusRE`). */
  ghost predicate NulledInstr(i: RB.instruction) {
    i.Fail? || i.Jmp? || i.Fork? || i.SetRegisterToCP? || i.SetQuantToClock?
    || i.CheckOracle? || i.NegCheckOracle? || i.AnchorAssertion?
  }

  /** Every pc of the region holds a `NulledInstr` whose successors stay in
      `[pc1, pc2]`, strictly forward. */
  ghost predicate RegionShape(c: RB.code, pc1: nat, pc2: nat) {
    forall p: nat :: pc1 <= p < pc2 ==>
      p < |c| && NulledInstr(c[p])
      && (c[p].Jmp? ==> p < c[p].jl <= pc2)
      && (c[p].Fork? ==> p < c[p].fl1 <= pc2 && p < c[p].fl2 <= pc2)
      && (!c[p].Jmp? && !c[p].Fork? && !c[p].Fail? ==> p + 1 <= pc2)
  }

  lemma RegionShapeRE(re: R.regex, c: RB.code, pc1: nat, pc2: nat)
    requires NfaRepNulledRE(re, c, pc1, pc2)
    requires NoCdnPlusRE(re)
    ensures pc1 <= pc2 && RegionShape(c, pc1, pc2)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
                     && NfaRepNulledRE(r1, c, pc1 + 1, e1)
                     && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc2))
                     && NfaRepNulledRE(r2, c, e1 + 1, pc2);
      RegionShapeRE(r1, c, pc1 + 1, e1);
      RegionShapeRE(r2, c, e1 + 1, pc2);
    case Re_con(r1, r2) =>
      var e1: nat :| NfaRepNulledRE(r1, c, pc1, e1) && NfaRepNulledRE(r2, c, e1, pc2);
      RegionShapeRE(r1, c, pc1, e1);
      RegionShapeRE(r2, c, e1, pc2);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 {
      } else if nul == R.NonNullable {
      } else if q.max == None && nul == R.CINullable && q.greedy {
      } else if q.max == None && nul == R.CDNullable && q.greedy {
        assert false;
      } else {
        RegionShapeRE(r1, c, pc1 + 1, pc2);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
                     && NfaRepNulledRE(r1, c, pc1 + 1, e1)
                     && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
                     && pc2 == e1 + 1;
      RegionShapeRE(r1, c, pc1 + 1, e1);
  }

  /** The whole reconstruct code is forward-only and free of consuming,
      looping, CDN and oracle-writing instructions. */
  lemma ReconstructCodeShape(re: R.regex)
    requires NoCdnPlusRE(re)
    ensures var c := CP.compile_reconstruct_nulled(re);
      ForwardOnly(c) && |c| >= 1 && c[|c| - 1] == RB.Accept
      && (forall p: nat :: p < |c| - 1 ==> NulledInstr(c[p]))
  {
    var c := CP.compile_reconstruct_nulled(re);
    CompileReconstructNulledLayout(re);
    var n := (|c| - 1) as nat;
    RegionShapeRE(re, c, 0, n);
    forall p: nat | p < |c|
      ensures (c[p].Jmp? ==> c[p].jl > p) && (c[p].Fork? ==> c[p].fl1 > p && c[p].fl2 > p)
    {
      if p < n { assert RegionShape(c, 0, n); }
    }
  }

  // ===========================================================================
  // 3. The register writes of the first empty path (twin of `FirstEmptyPathR`).
  // ===========================================================================

  datatype Write = WCap(reg: int) | WLook(lid: int) | WQuant(qid: int, b: bool)

  /** The writes performed by the first accepting path of `re`'s ReconstructNulled
      code at `inp`, with the oracle bits `qm.ov`. A nested CIN-greedy `+` writes
      its stamp only (its own path is chained later by `FNulledChildren`); a
      generic forced quantifier is entered ONCE (clock-mark + body). */
  ghost function NulledWrites(qm: AR.QMap, re: R.regex, inp: LC.Input): Option<seq<Write>>
    decreases re
  {
    match re
    case Re_empty => Some([])
    case Re_character(_) => None
    case Re_anchor(a) => if RA.is_satisfied(a, TR.CtxOf(inp), RA.Forward) then Some([]) else None
    case Re_alt(r1, r2) =>
      (match NulledWrites(qm, r1, inp)
       case Some(w) => Some(w)
       case None => NulledWrites(qm, r2, inp))
    case Re_con(r1, r2) =>
      (match NulledWrites(qm, r1, inp)
       case None => None
       case Some(w1) =>
         (match NulledWrites(qm, r2, inp)
          case None => None
          case Some(w2) => Some(w1 + w2)))
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 then Some([])
      else if nul == R.NonNullable then None
      else if q.max == None && nul == R.CINullable && q.greedy then Some([WQuant(qid, true)])
      else if q.max == None && nul == R.CDNullable && q.greedy then None
      else
        (match NulledWrites(qm, r1, inp)
         case None => None
         case Some(w1) => Some([WQuant(qid, false)] + w1))
    case Re_capture(cid, r1) =>
      (match NulledWrites(qm, r1, inp)
       case None => None
       case Some(w) => Some([WCap(CP.start_reg(cid))] + w + [WCap(CP.end_reg(cid))]))
    case Re_lookaround(lid, la, _) =>
      var bit := LOr.view_get_oracle(qm.ov, TR.CpOf(inp), lid);
      if PositiveLk(la) then (if bit then Some([WLook(lid)]) else None)
      else (if bit then None else Some([]))
  }

  // ===========================================================================
  // 4. Registers as a fold of writes at strictly increasing clocks.
  // ===========================================================================

  type Regs3 = (AReg.Regs, AReg.Regs, AReg.Regs)

  ghost function RegsOf(t: AI.Thread): Regs3 { (t.capture_regs, t.look_regs, t.quant_regs) }

  ghost function ApplyWrite(w: Write, cp: int, clk: int, rg: Regs3): Regs3 {
    match w
    case WCap(reg) => (AReg.set_reg(rg.0, reg, Some(cp), clk), rg.1, rg.2)
    case WLook(l) => (rg.0, AReg.set_reg(rg.1, l, Some(cp), clk), rg.2)
    case WQuant(q, b) => (rg.0, rg.1, AReg.set_reg(rg.2, q, if b then Some(cp) else None, clk))
  }

  ghost function ApplyWrites(ws: seq<Write>, cp: int, clks: seq<int>, rg: Regs3): Regs3
    requires |clks| == |ws|
    decreases |ws|
  {
    if |ws| == 0 then rg
    else ApplyWrites(ws[1..], cp, clks[1..], ApplyWrite(ws[0], cp, clks[0], rg))
  }

  ghost predicate Incr(clks: seq<int>) {
    forall i, j :: 0 <= i < j < |clks| ==> clks[i] < clks[j]
  }

  ghost predicate ClksIn(clks: seq<int>, lo: int, hi: int) {
    forall i :: 0 <= i < |clks| ==> lo < clks[i] <= hi
  }

  /** `rg` is `rg0` with the writes `ws` applied at strictly increasing clocks
      in `(clk0, C]`. */
  ghost predicate RegsFrom(rg: Regs3, ws: seq<Write>, cp: int, rg0: Regs3, clk0: int, C: int) {
    clk0 <= C
    && exists clks: seq<int> :: |clks| == |ws| && Incr(clks) && ClksIn(clks, clk0, C)
                                && rg == ApplyWrites(ws, cp, clks, rg0)
  }

  lemma ApplyWritesSnoc(ws: seq<Write>, w: Write, cp: int, clks: seq<int>, k: int, rg: Regs3)
    requires |clks| == |ws|
    ensures ApplyWrites(ws + [w], cp, clks + [k], rg) == ApplyWrite(w, cp, k, ApplyWrites(ws, cp, clks, rg))
    decreases |ws|
  {
    if |ws| == 0 {
      assert ws + [w] == [w];
      assert clks + [k] == [k];
    } else {
      assert (ws + [w])[0] == ws[0] && (ws + [w])[1..] == ws[1..] + [w];
      assert (clks + [k])[0] == clks[0] && (clks + [k])[1..] == clks[1..] + [k];
      ApplyWritesSnoc(ws[1..], w, cp, clks[1..], k, ApplyWrite(ws[0], cp, clks[0], rg));
    }
  }

  lemma RegsFromWrite(rg: Regs3, ws: seq<Write>, cp: int, rg0: Regs3, clk0: int, C: int, w: Write, k: int)
    requires RegsFrom(rg, ws, cp, rg0, clk0, C)
    requires C < k
    ensures RegsFrom(ApplyWrite(w, cp, k, rg), ws + [w], cp, rg0, clk0, k)
  {
    var clks: seq<int> :| |clks| == |ws| && Incr(clks) && ClksIn(clks, clk0, C)
                          && rg == ApplyWrites(ws, cp, clks, rg0);
    var clks' := clks + [k];
    ApplyWritesSnoc(ws, w, cp, clks, k, rg0);
    assert Incr(clks') by {
      forall i, j | 0 <= i < j < |clks'| ensures clks'[i] < clks'[j] {
        if j == |clks| { assert clks'[i] == clks[i] && clks[i] <= C < k; }
      }
    }
    assert ClksIn(clks', clk0, k) by {
      forall i | 0 <= i < |clks'| ensures clk0 < clks'[i] <= k {
        if i < |clks| { assert clks'[i] == clks[i]; } else { assert clks'[i] == k; }
      }
    }
    assert |clks'| == |ws + [w]|;
    assert ApplyWrite(w, cp, k, rg) == ApplyWrites(ws + [w], cp, clks', rg0);
  }

  lemma RegsFromWeaken(rg: Regs3, ws: seq<Write>, cp: int, rg0: Regs3, clk0: int, C: int, C': int)
    requires RegsFrom(rg, ws, cp, rg0, clk0, C) && C <= C'
    ensures RegsFrom(rg, ws, cp, rg0, clk0, C')
  {
    var clks: seq<int> :| |clks| == |ws| && Incr(clks) && ClksIn(clks, clk0, C)
                          && rg == ApplyWrites(ws, cp, clks, rg0);
    assert ClksIn(clks, clk0, C');
  }

  lemma RegsFromNil(rg0: Regs3, cp: int, clk0: int, C: int)
    requires clk0 <= C
    ensures RegsFrom(rg0, [], cp, rg0, clk0, C)
  {
    var clks: seq<int> := [];
    assert rg0 == ApplyWrites([], cp, clks, rg0);
  }

  // ===========================================================================
  // 5. Junk: pending alternatives whose every path dies inside the region or
  //    lands on a pc that is already processed.
  // ===========================================================================

  ghost function Measure(c: RB.code, pc: nat): nat { if pc < |c| then |c| - pc else 0 }

  /** Every enabled path from `pc` dies STRICTLY BEFORE `B` (never reaches `B`,
      never accepts). */
  ghost predicate Dead(c: RB.code, pc: nat, B: nat, cp: int, ctx: RA.char_context, ov: LOr.OracleView)
    requires ForwardOnly(c)
    decreases Measure(c, pc)
  {
    pc < B && pc < |c| &&
    match c[pc]
    case Fail => true
    case Jmp(x) => Dead(c, x as nat, B, cp, ctx, ov)
    case Fork(x, y) => Dead(c, x as nat, B, cp, ctx, ov) && Dead(c, y as nat, B, cp, ctx, ov)
    case SetRegisterToCP(_) => Dead(c, pc + 1, B, cp, ctx, ov)
    case SetQuantToClock(_, _) => Dead(c, pc + 1, B, cp, ctx, ov)
    case CheckOracle(l) => !LOr.view_get_oracle(ov, cp, l) || Dead(c, pc + 1, B, cp, ctx, ov)
    case NegCheckOracle(l) => LOr.view_get_oracle(ov, cp, l) || Dead(c, pc + 1, B, cp, ctx, ov)
    case AnchorAssertion(a) => !RA.is_satisfied(a, ctx, RA.Forward) || Dead(c, pc + 1, B, cp, ctx, ov)
    case _ => false
  }

  /** Every enabled path from `pc` either dies before `q` or reaches exactly `q`. */
  ghost predicate Junk(c: RB.code, pc: nat, q: nat, cp: int, ctx: RA.char_context, ov: LOr.OracleView)
    requires ForwardOnly(c)
    decreases Measure(c, pc)
  {
    pc == q
    || (pc < q && pc < |c| &&
        match c[pc]
        case Fail => true
        case Jmp(x) => Junk(c, x as nat, q, cp, ctx, ov)
        case Fork(x, y) => Junk(c, x as nat, q, cp, ctx, ov) && Junk(c, y as nat, q, cp, ctx, ov)
        case SetRegisterToCP(_) => Junk(c, pc + 1, q, cp, ctx, ov)
        case SetQuantToClock(_, _) => Junk(c, pc + 1, q, cp, ctx, ov)
        case CheckOracle(l) => !LOr.view_get_oracle(ov, cp, l) || Junk(c, pc + 1, q, cp, ctx, ov)
        case NegCheckOracle(l) => LOr.view_get_oracle(ov, cp, l) || Junk(c, pc + 1, q, cp, ctx, ov)
        case AnchorAssertion(a) => !RA.is_satisfied(a, ctx, RA.Forward) || Junk(c, pc + 1, q, cp, ctx, ov)
        case _ => false)
  }

  lemma DeadWeaken(c: RB.code, pc: nat, B: nat, B': nat, cp: int, ctx: RA.char_context, ov: LOr.OracleView)
    requires ForwardOnly(c)
    requires Dead(c, pc, B, cp, ctx, ov) && B <= B'
    ensures Dead(c, pc, B', cp, ctx, ov)
    decreases Measure(c, pc)
  {
    match c[pc]
    case Fail =>
    case Jmp(x) => DeadWeaken(c, x as nat, B, B', cp, ctx, ov);
    case Fork(x, y) => DeadWeaken(c, x as nat, B, B', cp, ctx, ov); DeadWeaken(c, y as nat, B, B', cp, ctx, ov);
    case SetRegisterToCP(_) => DeadWeaken(c, pc + 1, B, B', cp, ctx, ov);
    case SetQuantToClock(_, _) => DeadWeaken(c, pc + 1, B, B', cp, ctx, ov);
    case CheckOracle(l) => if LOr.view_get_oracle(ov, cp, l) { DeadWeaken(c, pc + 1, B, B', cp, ctx, ov); }
    case NegCheckOracle(l) => if !LOr.view_get_oracle(ov, cp, l) { DeadWeaken(c, pc + 1, B, B', cp, ctx, ov); }
    case AnchorAssertion(a) => if RA.is_satisfied(a, ctx, RA.Forward) { DeadWeaken(c, pc + 1, B, B', cp, ctx, ov); }
    case _ =>
  }

  /** `Junk(p, q1)` then `Junk(q1, q2)` gives `Junk(p, q2)` (`q1 <= q2`). */
  lemma JunkTrans(c: RB.code, pc: nat, q1: nat, q2: nat, cp: int, ctx: RA.char_context, ov: LOr.OracleView)
    requires ForwardOnly(c)
    requires Junk(c, pc, q1, cp, ctx, ov) && Junk(c, q1, q2, cp, ctx, ov) && q1 <= q2
    ensures Junk(c, pc, q2, cp, ctx, ov)
    decreases Measure(c, pc)
  {
    if pc == q1 {
    } else {
      match c[pc]
      case Fail =>
      case Jmp(x) => JunkTrans(c, x as nat, q1, q2, cp, ctx, ov);
      case Fork(x, y) => JunkTrans(c, x as nat, q1, q2, cp, ctx, ov); JunkTrans(c, y as nat, q1, q2, cp, ctx, ov);
      case SetRegisterToCP(_) => JunkTrans(c, pc + 1, q1, q2, cp, ctx, ov);
      case SetQuantToClock(_, _) => JunkTrans(c, pc + 1, q1, q2, cp, ctx, ov);
      case CheckOracle(l) => if LOr.view_get_oracle(ov, cp, l) { JunkTrans(c, pc + 1, q1, q2, cp, ctx, ov); }
      case NegCheckOracle(l) => if !LOr.view_get_oracle(ov, cp, l) { JunkTrans(c, pc + 1, q1, q2, cp, ctx, ov); }
      case AnchorAssertion(a) => if RA.is_satisfied(a, ctx, RA.Forward) { JunkTrans(c, pc + 1, q1, q2, cp, ctx, ov); }
      case _ =>
    }
  }

  /** Every path through a region reaches its exit or dies inside it. */
  lemma RegionJunkRE(re: R.regex, c: RB.code, pc1: nat, pc2: nat, cp: int, ctx: RA.char_context, ov: LOr.OracleView)
    requires ForwardOnly(c)
    requires NfaRepNulledRE(re, c, pc1, pc2)
    requires NoCdnPlusRE(re)
    ensures Junk(c, pc1, pc2, cp, ctx, ov)
    decreases CP.rsize(re), 1
  {
    RegionShapeRE(re, c, pc1, pc2);
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
                     && NfaRepNulledRE(r1, c, pc1 + 1, e1)
                     && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc2))
                     && NfaRepNulledRE(r2, c, e1 + 1, pc2);
      RegionShapeRE(r1, c, pc1 + 1, e1);
      RegionShapeRE(r2, c, e1 + 1, pc2);
      RegionJunkRE(r1, c, pc1 + 1, e1, cp, ctx, ov);
      assert Junk(c, e1, pc2, cp, ctx, ov);
      JunkTrans(c, pc1 + 1, e1, pc2, cp, ctx, ov);
      RegionJunkRE(r2, c, e1 + 1, pc2, cp, ctx, ov);
    case Re_con(r1, r2) =>
      var e1: nat :| NfaRepNulledRE(r1, c, pc1, e1) && NfaRepNulledRE(r2, c, e1, pc2);
      RegionShapeRE(r1, c, pc1, e1);
      RegionShapeRE(r2, c, e1, pc2);
      RegionJunkRE(r1, c, pc1, e1, cp, ctx, ov);
      RegionJunkRE(r2, c, e1, pc2, cp, ctx, ov);
      JunkTrans(c, pc1, e1, pc2, cp, ctx, ov);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 {
      } else if nul == R.NonNullable {
      } else if q.max == None && nul == R.CINullable && q.greedy {
      } else if q.max == None && nul == R.CDNullable && q.greedy {
        assert false;
      } else {
        RegionJunkRE(r1, c, pc1 + 1, pc2, cp, ctx, ov);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
                     && NfaRepNulledRE(r1, c, pc1 + 1, e1)
                     && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
                     && pc2 == e1 + 1;
      RegionShapeRE(r1, c, pc1 + 1, e1);
      RegionJunkRE(r1, c, pc1 + 1, e1, cp, ctx, ov);
      assert Junk(c, e1, pc2, cp, ctx, ov);
      JunkTrans(c, pc1 + 1, e1, pc2, cp, ctx, ov);
  }

  /** A pending thread is junk w.r.t. the region exit `hi`: dead before `hi`,
      or every path reaches an already-processed `q <= hi` (or dies). */
  ghost predicate JunkOk(c: RB.code, th: AI.Thread, processed: AI.Bpcset, hi: nat,
                         cp: int, ctx: RA.char_context, ov: LOr.OracleView)
    requires ForwardOnly(c)
  {
    th.pc >= 0
    && (Dead(c, th.pc as nat, hi, cp, ctx, ov)
        || exists q: nat :: q <= hi && Junk(c, th.pc as nat, q, cp, ctx, ov) && AI.bpc_mem(processed, q, false))
  }

  ghost predicate ProcMono(p1: AI.Bpcset, p2: AI.Bpcset) {
    forall pc: int, eb: bool :: AI.bpc_mem(p1, pc, eb) ==> AI.bpc_mem(p2, pc, eb)
  }

  lemma JunkOkMono(c: RB.code, th: AI.Thread, p1: AI.Bpcset, p2: AI.Bpcset, hi: nat, hi': nat,
                   cp: int, ctx: RA.char_context, ov: LOr.OracleView)
    requires ForwardOnly(c)
    requires JunkOk(c, th, p1, hi, cp, ctx, ov) && ProcMono(p1, p2) && hi <= hi'
    ensures JunkOk(c, th, p2, hi', cp, ctx, ov)
  {
    if Dead(c, th.pc as nat, hi, cp, ctx, ov) {
      DeadWeaken(c, th.pc as nat, hi, hi', cp, ctx, ov);
    }
  }

  // ===========================================================================
  // 6. One-step unfoldings of `FAdvanceEpsilon` (the reconstruct instructions).
  // ===========================================================================

  ghost function Bump(s: AI.VmState, t: AI.Thread): AI.VmState {
    s.(clock := s.clock + 1, processed := AI.bpc_add(s.processed, t.pc, t.exit_allowed))
  }

  ghost predicate Sized(c: RB.code, s: AI.VmState) {
    |s.processed.true_set| == |c| && |s.processed.false_set| == |c|
  }

  lemma StepDrop(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: RA.direction, t: AI.Thread, ac: seq<AI.Thread>)
    requires Sized(c, s) && s.active == [t] + ac
    requires AI.bpc_mem(s.processed, t.pc, t.exit_allowed)
    ensures AI.FAdvanceEpsilon(c, s, ov, dir) == AI.FAdvanceEpsilon(c, s.(active := ac), ov, dir)
  {
    assert s.active[0] == t && s.active[1..] == ac;
  }

  lemma StepFail(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: RA.direction, t: AI.Thread, ac: seq<AI.Thread>)
    requires Sized(c, s) && s.active == [t] + ac
    requires !AI.bpc_mem(s.processed, t.pc, t.exit_allowed)
    requires RB.get_instr(c, t.pc) == RB.Fail
    ensures AI.FAdvanceEpsilon(c, s, ov, dir) == AI.FAdvanceEpsilon(c, Bump(s, t).(active := ac), ov, dir)
  {
    assert s.active[0] == t && s.active[1..] == ac;
  }

  lemma StepAccept(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: RA.direction, t: AI.Thread, ac: seq<AI.Thread>)
    requires Sized(c, s) && s.active == [t] + ac
    requires !AI.bpc_mem(s.processed, t.pc, t.exit_allowed)
    requires RB.get_instr(c, t.pc) == RB.Accept
    ensures AI.FAdvanceEpsilon(c, s, ov, dir) == (Bump(s, t).(active := [], bestmatch := Some(t)), ov)
  {
    assert s.active[0] == t && s.active[1..] == ac;
  }

  lemma StepJmp(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: RA.direction, t: AI.Thread, ac: seq<AI.Thread>, x: int)
    requires Sized(c, s) && s.active == [t] + ac
    requires !AI.bpc_mem(s.processed, t.pc, t.exit_allowed)
    requires RB.get_instr(c, t.pc) == RB.Jmp(x)
    ensures AI.FAdvanceEpsilon(c, s, ov, dir) == AI.FAdvanceEpsilon(c, Bump(s, t).(active := [t.(pc := x)] + ac), ov, dir)
  {
    assert s.active[0] == t && s.active[1..] == ac;
  }

  lemma StepFork(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: RA.direction, t: AI.Thread, ac: seq<AI.Thread>, x: int, y: int)
    requires Sized(c, s) && s.active == [t] + ac
    requires !AI.bpc_mem(s.processed, t.pc, t.exit_allowed)
    requires RB.get_instr(c, t.pc) == RB.Fork(x, y)
    ensures AI.FAdvanceEpsilon(c, s, ov, dir)
         == AI.FAdvanceEpsilon(c, Bump(s, t).(active := [AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed), t.(pc := y)] + ac), ov, dir)
  {
    assert s.active[0] == t && s.active[1..] == ac;
  }

  lemma StepSetReg(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: RA.direction, t: AI.Thread, ac: seq<AI.Thread>, reg: int)
    requires Sized(c, s) && s.active == [t] + ac
    requires !AI.bpc_mem(s.processed, t.pc, t.exit_allowed)
    requires RB.get_instr(c, t.pc) == RB.SetRegisterToCP(reg)
    ensures AI.FAdvanceEpsilon(c, s, ov, dir)
         == AI.FAdvanceEpsilon(c, Bump(s, t).(active := [t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s.cp), s.clock + 1), pc := t.pc + 1)] + ac), ov, dir)
  {
    assert s.active[0] == t && s.active[1..] == ac;
  }

  lemma StepSetQuant(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: RA.direction, t: AI.Thread, ac: seq<AI.Thread>, q: int, b: bool)
    requires Sized(c, s) && s.active == [t] + ac
    requires !AI.bpc_mem(s.processed, t.pc, t.exit_allowed)
    requires RB.get_instr(c, t.pc) == RB.SetQuantToClock(q, b)
    ensures AI.FAdvanceEpsilon(c, s, ov, dir)
         == AI.FAdvanceEpsilon(c, Bump(s, t).(active := [t.(quant_regs := AReg.set_reg(t.quant_regs, q, if b then Some(s.cp) else None, s.clock + 1), pc := t.pc + 1)] + ac), ov, dir)
  {
    assert s.active[0] == t && s.active[1..] == ac;
  }

  lemma StepCheckOracle(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: RA.direction, t: AI.Thread, ac: seq<AI.Thread>, l: int)
    requires Sized(c, s) && s.active == [t] + ac
    requires !AI.bpc_mem(s.processed, t.pc, t.exit_allowed)
    requires RB.get_instr(c, t.pc) == RB.CheckOracle(l)
    ensures LOr.view_get_oracle(ov, s.cp, l) ==>
      AI.FAdvanceEpsilon(c, s, ov, dir)
      == AI.FAdvanceEpsilon(c, Bump(s, t).(active := [t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s.cp), s.clock + 1))] + ac), ov, dir)
    ensures !LOr.view_get_oracle(ov, s.cp, l) ==>
      AI.FAdvanceEpsilon(c, s, ov, dir) == AI.FAdvanceEpsilon(c, Bump(s, t).(active := ac), ov, dir)
  {
    assert s.active[0] == t && s.active[1..] == ac;
  }

  lemma StepNegCheckOracle(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: RA.direction, t: AI.Thread, ac: seq<AI.Thread>, l: int)
    requires Sized(c, s) && s.active == [t] + ac
    requires !AI.bpc_mem(s.processed, t.pc, t.exit_allowed)
    requires RB.get_instr(c, t.pc) == RB.NegCheckOracle(l)
    ensures LOr.view_get_oracle(ov, s.cp, l) ==>
      AI.FAdvanceEpsilon(c, s, ov, dir) == AI.FAdvanceEpsilon(c, Bump(s, t).(active := ac), ov, dir)
    ensures !LOr.view_get_oracle(ov, s.cp, l) ==>
      AI.FAdvanceEpsilon(c, s, ov, dir) == AI.FAdvanceEpsilon(c, Bump(s, t).(active := [t.(pc := t.pc + 1)] + ac), ov, dir)
  {
    assert s.active[0] == t && s.active[1..] == ac;
  }

  lemma StepAnchor(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: RA.direction, t: AI.Thread, ac: seq<AI.Thread>, a: R.anchor)
    requires Sized(c, s) && s.active == [t] + ac
    requires !AI.bpc_mem(s.processed, t.pc, t.exit_allowed)
    requires RB.get_instr(c, t.pc) == RB.AnchorAssertion(a)
    ensures RA.is_satisfied(a, s.context, dir) ==>
      AI.FAdvanceEpsilon(c, s, ov, dir) == AI.FAdvanceEpsilon(c, Bump(s, t).(active := [t.(pc := t.pc + 1)] + ac), ov, dir)
    ensures !RA.is_satisfied(a, s.context, dir) ==>
      AI.FAdvanceEpsilon(c, s, ov, dir) == AI.FAdvanceEpsilon(c, Bump(s, t).(active := ac), ov, dir)
  {
    assert s.active[0] == t && s.active[1..] == ac;
  }

  // ---- bookkeeping facts about `Bump` ----

  lemma BumpFacts(c: RB.code, s: AI.VmState, t: AI.Thread)
    requires Sized(c, s)
    ensures Sized(c, Bump(s, t))
    ensures ProcMono(s.processed, Bump(s, t).processed)
    ensures forall pc: int, eb: bool :: !(pc == t.pc && eb == t.exit_allowed) ==>
              AI.bpc_mem(Bump(s, t).processed, pc, eb) == AI.bpc_mem(s.processed, pc, eb)
    ensures 0 <= t.pc < |c| ==> AI.bpc_mem(Bump(s, t).processed, t.pc, t.exit_allowed)
    ensures AI.unprocessed(Bump(s, t).processed) <= AI.unprocessed(s.processed)
    ensures 0 <= t.pc < |c| && !AI.bpc_mem(s.processed, t.pc, t.exit_allowed)
              ==> AI.unprocessed(Bump(s, t).processed) < AI.unprocessed(s.processed)
  {
    AI.UnprocessedAdd(s.processed, t.pc, t.exit_allowed);
  }

  // ===========================================================================
  // 7. Junk elimination: running junk threads only marks pcs in `[lo, hi)`,
  //    never accepts, and leaves the rest of the list to run.
  // ===========================================================================

  /** The state-shape facts a phase of the closure preserves. */
  ghost predicate SameFrame(s: AI.VmState, s': AI.VmState) {
    s'.cp == s.cp && s'.context == s.context && s'.bestmatch == s.bestmatch
    && s'.blocked == s.blocked && s'.isblocked == s.isblocked && s'.cdn == s.cdn
    && s'.clock >= s.clock
  }

  ghost predicate ProcAgreeOutside(p1: AI.Bpcset, p2: AI.Bpcset, lo: nat, hi: nat) {
    (forall pc: int :: !(lo <= pc < hi) ==> AI.bpc_mem(p1, pc, false) == AI.bpc_mem(p2, pc, false))
    && (forall pc: int :: AI.bpc_mem(p1, pc, true) == AI.bpc_mem(p2, pc, true))
  }

  lemma JunkSkip(c: RB.code, s: AI.VmState, ov: LOr.OracleView, junk: seq<AI.Thread>, rest: seq<AI.Thread>,
                 lo: nat, hi: nat)
      returns (s': AI.VmState)
    requires ForwardOnly(c) && Sized(c, s)
    requires s.active == junk + rest
    requires forall th <- junk :: !th.exit_allowed && lo <= th.pc <= hi
                                  && JunkOk(c, th, s.processed, hi, s.cp, s.context, ov)
    requires s.bestmatch == None
    ensures Sized(c, s')
    ensures AI.FAdvanceEpsilon(c, s, ov, RA.Forward) == AI.FAdvanceEpsilon(c, s', ov, RA.Forward)
    ensures s'.active == rest && SameFrame(s, s')
    ensures ProcMono(s.processed, s'.processed) && ProcAgreeOutside(s.processed, s'.processed, lo, hi)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |junk| == 0 {
      s' := s;
      assert s.active == rest;
      return;
    }
    var t := junk[0];
    var ac := junk[1..] + rest;
    assert s.active == [t] + ac;
    var pc: nat := t.pc as nat;
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      StepDrop(c, s, ov, RA.Forward, t, ac);
      var s1 := s.(active := ac);
      s' := JunkSkip(c, s1, ov, junk[1..], rest, lo, hi);
      return;
    }
    // t is processed: it is not at `hi` (a junk thread at `hi` is Junk(hi, hi)
    // with hi processed), so pc < hi, and its instruction is a NulledInstr
    // whose successors are junk again.
    var s1 := Bump(s, t);
    BumpFacts(c, s, t);
    assert JunkOk(c, t, s.processed, hi, s.cp, s.context, ov);
    assert pc < hi && pc < |c| by {
      if Dead(c, pc, hi, s.cp, s.context, ov) {
      } else {
        var q: nat :| q <= hi && Junk(c, pc, q, s.cp, s.context, ov) && AI.bpc_mem(s.processed, q, false);
        assert pc != q;
      }
    }
    assert ProcMono(s.processed, s1.processed);
    assert forall th <- junk[1..] :: JunkOk(c, th, s1.processed, hi, s.cp, s.context, ov) by {
      forall th <- junk[1..] ensures JunkOk(c, th, s1.processed, hi, s.cp, s.context, ov) {
        assert th in junk;
        JunkOkMono(c, th, s.processed, s1.processed, hi, hi, s.cp, s.context, ov);
      }
    }
    // successor junk-ness
    var i := c[pc];
    assert RB.get_instr(c, t.pc) == i;
    match i {
      case Fail =>
        StepFail(c, s, ov, RA.Forward, t, ac);
        s' := JunkSkip(c, s1.(active := ac), ov, junk[1..], rest, lo, hi);
      case Jmp(x) =>
        StepJmp(c, s, ov, RA.Forward, t, ac, x);
        var t2 := t.(pc := x);
        assert JunkOk(c, t2, s1.processed, hi, s.cp, s.context, ov) && lo <= t2.pc <= hi by {
          if Dead(c, pc, hi, s.cp, s.context, ov) {
            assert Dead(c, x as nat, hi, s.cp, s.context, ov);
          } else {
            var q: nat :| q <= hi && Junk(c, pc, q, s.cp, s.context, ov) && AI.bpc_mem(s.processed, q, false);
            assert Junk(c, x as nat, q, s.cp, s.context, ov);
          }
        }
        s' := JunkSkip(c, s1.(active := [t2] + ac), ov, [t2] + junk[1..], rest, lo, hi);
      case Fork(x, y) =>
        StepFork(c, s, ov, RA.Forward, t, ac, x, y);
        var tx := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
        var ty := t.(pc := y);
        assert JunkOk(c, tx, s1.processed, hi, s.cp, s.context, ov) && lo <= tx.pc <= hi
            && JunkOk(c, ty, s1.processed, hi, s.cp, s.context, ov) && lo <= ty.pc <= hi by {
          if Dead(c, pc, hi, s.cp, s.context, ov) {
            assert Dead(c, x as nat, hi, s.cp, s.context, ov) && Dead(c, y as nat, hi, s.cp, s.context, ov);
          } else {
            var q: nat :| q <= hi && Junk(c, pc, q, s.cp, s.context, ov) && AI.bpc_mem(s.processed, q, false);
            assert Junk(c, x as nat, q, s.cp, s.context, ov) && Junk(c, y as nat, q, s.cp, s.context, ov);
          }
        }
        s' := JunkSkip(c, s1.(active := [tx, ty] + ac), ov, [tx, ty] + junk[1..], rest, lo, hi);
      case SetRegisterToCP(reg) =>
        StepSetReg(c, s, ov, RA.Forward, t, ac, reg);
        var t2 := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s.cp), s.clock + 1), pc := t.pc + 1);
        assert JunkOk(c, t2, s1.processed, hi, s.cp, s.context, ov) && lo <= t2.pc <= hi by {
          if Dead(c, pc, hi, s.cp, s.context, ov) {
            assert Dead(c, pc + 1, hi, s.cp, s.context, ov);
          } else {
            var q: nat :| q <= hi && Junk(c, pc, q, s.cp, s.context, ov) && AI.bpc_mem(s.processed, q, false);
            assert Junk(c, pc + 1, q, s.cp, s.context, ov);
          }
        }
        s' := JunkSkip(c, s1.(active := [t2] + ac), ov, [t2] + junk[1..], rest, lo, hi);
      case SetQuantToClock(q0, b) =>
        StepSetQuant(c, s, ov, RA.Forward, t, ac, q0, b);
        var t2 := t.(quant_regs := AReg.set_reg(t.quant_regs, q0, if b then Some(s.cp) else None, s.clock + 1), pc := t.pc + 1);
        assert JunkOk(c, t2, s1.processed, hi, s.cp, s.context, ov) && lo <= t2.pc <= hi by {
          if Dead(c, pc, hi, s.cp, s.context, ov) {
            assert Dead(c, pc + 1, hi, s.cp, s.context, ov);
          } else {
            var q: nat :| q <= hi && Junk(c, pc, q, s.cp, s.context, ov) && AI.bpc_mem(s.processed, q, false);
            assert Junk(c, pc + 1, q, s.cp, s.context, ov);
          }
        }
        s' := JunkSkip(c, s1.(active := [t2] + ac), ov, [t2] + junk[1..], rest, lo, hi);
      case CheckOracle(l) =>
        StepCheckOracle(c, s, ov, RA.Forward, t, ac, l);
        if LOr.view_get_oracle(ov, s.cp, l) {
          var t2 := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s.cp), s.clock + 1));
          assert JunkOk(c, t2, s1.processed, hi, s.cp, s.context, ov) && lo <= t2.pc <= hi by {
            if Dead(c, pc, hi, s.cp, s.context, ov) {
              assert Dead(c, pc + 1, hi, s.cp, s.context, ov);
            } else {
              var q: nat :| q <= hi && Junk(c, pc, q, s.cp, s.context, ov) && AI.bpc_mem(s.processed, q, false);
              assert Junk(c, pc + 1, q, s.cp, s.context, ov);
            }
          }
          s' := JunkSkip(c, s1.(active := [t2] + ac), ov, [t2] + junk[1..], rest, lo, hi);
        } else {
          s' := JunkSkip(c, s1.(active := ac), ov, junk[1..], rest, lo, hi);
        }
      case NegCheckOracle(l) =>
        StepNegCheckOracle(c, s, ov, RA.Forward, t, ac, l);
        if LOr.view_get_oracle(ov, s.cp, l) {
          s' := JunkSkip(c, s1.(active := ac), ov, junk[1..], rest, lo, hi);
        } else {
          var t2 := t.(pc := t.pc + 1);
          assert JunkOk(c, t2, s1.processed, hi, s.cp, s.context, ov) && lo <= t2.pc <= hi by {
            if Dead(c, pc, hi, s.cp, s.context, ov) {
              assert Dead(c, pc + 1, hi, s.cp, s.context, ov);
            } else {
              var q: nat :| q <= hi && Junk(c, pc, q, s.cp, s.context, ov) && AI.bpc_mem(s.processed, q, false);
              assert Junk(c, pc + 1, q, s.cp, s.context, ov);
            }
          }
          s' := JunkSkip(c, s1.(active := [t2] + ac), ov, [t2] + junk[1..], rest, lo, hi);
        }
      case AnchorAssertion(a) =>
        StepAnchor(c, s, ov, RA.Forward, t, ac, a);
        if RA.is_satisfied(a, s.context, RA.Forward) {
          var t2 := t.(pc := t.pc + 1);
          assert JunkOk(c, t2, s1.processed, hi, s.cp, s.context, ov) && lo <= t2.pc <= hi by {
            if Dead(c, pc, hi, s.cp, s.context, ov) {
              assert Dead(c, pc + 1, hi, s.cp, s.context, ov);
            } else {
              var q: nat :| q <= hi && Junk(c, pc, q, s.cp, s.context, ov) && AI.bpc_mem(s.processed, q, false);
              assert Junk(c, pc + 1, q, s.cp, s.context, ov);
            }
          }
          s' := JunkSkip(c, s1.(active := [t2] + ac), ov, [t2] + junk[1..], rest, lo, hi);
        } else {
          s' := JunkSkip(c, s1.(active := ac), ov, junk[1..], rest, lo, hi);
        }
      case _ =>
        // excluded by Dead/Junk at a processed pc
        assert false by {
          if Dead(c, pc, hi, s.cp, s.context, ov) {
          } else {
            var q: nat :| q <= hi && Junk(c, pc, q, s.cp, s.context, ov) && AI.bpc_mem(s.processed, q, false);
          }
        }
    }
  }

  // ===========================================================================
  // 8. THE STRUCTURAL THEOREM.
  // ===========================================================================

  /** Pending threads behind the region's head: at or after the region's exit,
      junk w.r.t. the HEAD (dead before it, or bound for a processed pc at or
      before it), or bound for the head itself (processed by the first step). */
  ghost predicate RestOk(c: RB.code, rest: seq<AI.Thread>, processed: AI.Bpcset, pc1: nat, pc2: nat,
                         cp: int, ctx: RA.char_context, ov: LOr.OracleView)
    requires ForwardOnly(c)
  {
    forall th <- rest :: !th.exit_allowed && th.pc >= 0
      && (th.pc >= pc2 as int
          || JunkOk(c, th, processed, pc1, cp, ctx, ov)
          || Junk(c, th.pc as nat, pc1, cp, ctx, ov))
  }

  lemma HeadUnvisited(c: RB.code, s: AI.VmState, t: AI.Thread, pc1: nat, pc2: nat)
    requires t.pc == pc1 as int && !t.exit_allowed && pc1 < pc2
    requires forall p: nat :: pc1 <= p < pc2 ==> !AI.bpc_mem(s.processed, p, false)
    ensures !AI.bpc_mem(s.processed, t.pc, t.exit_allowed)
  {
    assert !AI.bpc_mem(s.processed, pc1, false);
  }

  lemma NulledRunRE(qm: AR.QMap, re: R.regex, inp: LC.Input, c: RB.code, pc1: nat, pc2: nat,
                    s: AI.VmState, ov: LOr.OracleView, t: AI.Thread, rest: seq<AI.Thread>, ws: seq<Write>,
                    rg0: Regs3, clk0: int)
      returns (s': AI.VmState, t': AI.Thread, junk: seq<AI.Thread>)
    requires NoCdnPlusRE(re)
    requires NfaRepNulledRE(re, c, pc1, pc2)
    requires ForwardOnly(c) && Sized(c, s)
    requires s.active == [t] + rest
    requires t.pc == pc1 as int && !t.exit_allowed
    requires RegsFrom(RegsOf(t), ws, s.cp, rg0, clk0, s.clock)
    requires forall p: nat :: pc1 <= p < pc2 ==> !AI.bpc_mem(s.processed, p, false)
    requires RestOk(c, rest, s.processed, pc1, pc2, s.cp, s.context, ov)
    requires s.bestmatch == None
    requires s.cp == TR.CpOf(inp) as int && s.context == TR.CtxOf(inp)
    requires ov == qm.ov
    ensures Sized(c, s')
    ensures AI.FAdvanceEpsilon(c, s, ov, RA.Forward) == AI.FAdvanceEpsilon(c, s', ov, RA.Forward)
    ensures SameFrame(s, s')
    ensures ProcMono(s.processed, s'.processed) && ProcAgreeOutside(s.processed, s'.processed, pc1, pc2)
    ensures pc1 < pc2 ==> AI.bpc_mem(s'.processed, pc1, false)
    ensures forall th <- junk :: !th.exit_allowed && pc1 as int <= th.pc <= pc2 as int
    ensures NulledWrites(qm, re, inp).Some? ==>
              s'.active == [t'] + junk + rest && t'.pc == pc2 as int && !t'.exit_allowed
              && RegsFrom(RegsOf(t'), ws + NulledWrites(qm, re, inp).value, s.cp, rg0, clk0, s'.clock)
              && (forall th <- junk :: JunkOk(c, th, s'.processed, pc2, s.cp, s.context, ov)
                                       || Junk(c, th.pc as nat, pc2, s.cp, s.context, ov))
    ensures NulledWrites(qm, re, inp).None? ==>
              s'.active == junk + rest
              && (forall th <- junk :: JunkOk(c, th, s'.processed, pc2, s.cp, s.context, ov))
    decreases CP.rsize(re), 1
  {
    var cp := s.cp;
    var ctx := s.context;
    match re {
      case Re_empty =>
        s' := s; t' := t; junk := [];
        assert ws + [] == ws;
        assert [t'] + junk + rest == s.active;
      case Re_character(_) =>
        HeadUnvisited(c, s, t, pc1, pc2);
        StepFail(c, s, ov, RA.Forward, t, rest);
        BumpFacts(c, s, t);
        s' := Bump(s, t).(active := rest); t' := t; junk := [];
        assert ProcAgreeOutside(s.processed, s'.processed, pc1, pc2);
      case Re_anchor(a) =>
        HeadUnvisited(c, s, t, pc1, pc2);
        StepAnchor(c, s, ov, RA.Forward, t, rest, a);
        BumpFacts(c, s, t);
        if RA.is_satisfied(a, ctx, RA.Forward) {
          t' := t.(pc := t.pc + 1);
          s' := Bump(s, t).(active := [t'] + rest); junk := [];
          RegsFromWeaken(RegsOf(t), ws, cp, rg0, clk0, s.clock, s'.clock);
          assert ws + [] == ws;
        } else {
          s' := Bump(s, t).(active := rest); t' := t; junk := [];
        }
      case Re_lookaround(lid, la, _) =>
        HeadUnvisited(c, s, t, pc1, pc2);
        BumpFacts(c, s, t);
        var bit := LOr.view_get_oracle(ov, cp, lid);
        assert bit == LOr.view_get_oracle(qm.ov, TR.CpOf(inp), lid);
        if PositiveLk(la) {
          StepCheckOracle(c, s, ov, RA.Forward, t, rest, lid);
          if bit {
            t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, lid, Some(cp), s.clock + 1));
            s' := Bump(s, t).(active := [t'] + rest); junk := [];
            RegsFromWrite(RegsOf(t), ws, cp, rg0, clk0, s.clock, WLook(lid), s.clock + 1);
            assert RegsOf(t') == ApplyWrite(WLook(lid), cp, s.clock + 1, RegsOf(t));
          } else {
            s' := Bump(s, t).(active := rest); t' := t; junk := [];
          }
        } else {
          StepNegCheckOracle(c, s, ov, RA.Forward, t, rest, lid);
          if bit {
            s' := Bump(s, t).(active := rest); t' := t; junk := [];
          } else {
            t' := t.(pc := t.pc + 1);
            s' := Bump(s, t).(active := [t'] + rest); junk := [];
            RegsFromWeaken(RegsOf(t), ws, cp, rg0, clk0, s.clock, s'.clock);
            assert ws + [] == ws;
          }
        }
      case Re_quant(nul, qid, q, r1) =>
        assert {:split_here} true;
        if q.min == 0 {
          s' := s; t' := t; junk := [];
          assert ws + [] == ws;
          assert [t'] + junk + rest == s.active;
        } else if nul == R.NonNullable {
          HeadUnvisited(c, s, t, pc1, pc2);
          StepFail(c, s, ov, RA.Forward, t, rest);
          BumpFacts(c, s, t);
          s' := Bump(s, t).(active := rest); t' := t; junk := [];
        } else if q.max == None && nul == R.CINullable && q.greedy {
          HeadUnvisited(c, s, t, pc1, pc2);
          StepSetQuant(c, s, ov, RA.Forward, t, rest, qid, true);
          BumpFacts(c, s, t);
          t' := t.(quant_regs := AReg.set_reg(t.quant_regs, qid, Some(cp), s.clock + 1), pc := t.pc + 1);
          s' := Bump(s, t).(active := [t'] + rest); junk := [];
          RegsFromWrite(RegsOf(t), ws, cp, rg0, clk0, s.clock, WQuant(qid, true), s.clock + 1);
          assert RegsOf(t') == ApplyWrite(WQuant(qid, true), cp, s.clock + 1, RegsOf(t));
        } else if q.max == None && nul == R.CDNullable && q.greedy {
          assert false;
        } else {
          NfaRepNulledMono(r1, c, pc1 + 1, pc2);
          HeadUnvisited(c, s, t, pc1, pc2);
          StepSetQuant(c, s, ov, RA.Forward, t, rest, qid, false);
          BumpFacts(c, s, t);
          var t2 := t.(quant_regs := AReg.set_reg(t.quant_regs, qid, None, s.clock + 1), pc := t.pc + 1);
          var s2 := Bump(s, t).(active := [t2] + rest);
          RegsFromWrite(RegsOf(t), ws, cp, rg0, clk0, s.clock, WQuant(qid, false), s.clock + 1);
          assert RegsOf(t2) == ApplyWrite(WQuant(qid, false), cp, s.clock + 1, RegsOf(t));
          var ws2 := ws + [WQuant(qid, false)];
          RestOkShift(c, rest, s.processed, s2.processed, pc1, pc2, pc1 + 1, pc2, cp, ctx, ov);
          var s3, t3, junk1 := NulledRunRE(qm, r1, inp, c, pc1 + 1, pc2, s2, ov, t2, rest, ws2, rg0, clk0);
          s' := s3; t' := t3; junk := junk1;
          match NulledWrites(qm, r1, inp) {
            case Some(w1) =>
              assert NulledWrites(qm, re, inp) == Some([WQuant(qid, false)] + w1);
              assert ws2 + w1 == ws + ([WQuant(qid, false)] + w1);
            case None =>
              assert NulledWrites(qm, re, inp) == None;
          }
        }
      case Re_capture(cid, r1) =>
        assert {:split_here} true;
        var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
                       && NfaRepNulledRE(r1, c, pc1 + 1, e1)
                       && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
                       && pc2 == e1 + 1;
        NfaRepNulledMono(r1, c, pc1 + 1, e1);
        HeadUnvisited(c, s, t, pc1, pc2);
        StepSetReg(c, s, ov, RA.Forward, t, rest, CP.start_reg(cid));
        BumpFacts(c, s, t);
        var t2 := t.(capture_regs := AReg.set_reg(t.capture_regs, CP.start_reg(cid), Some(cp), s.clock + 1), pc := t.pc + 1);
        var s2 := Bump(s, t).(active := [t2] + rest);
        RegsFromWrite(RegsOf(t), ws, cp, rg0, clk0, s.clock, WCap(CP.start_reg(cid)), s.clock + 1);
        assert RegsOf(t2) == ApplyWrite(WCap(CP.start_reg(cid)), cp, s.clock + 1, RegsOf(t));
        var ws2 := ws + [WCap(CP.start_reg(cid))];
        RestOkShift(c, rest, s.processed, s2.processed, pc1, pc2, pc1 + 1, e1, cp, ctx, ov);
        var s3, t3, junk1 := NulledRunRE(qm, r1, inp, c, pc1 + 1, e1, s2, ov, t2, rest, ws2, rg0, clk0);
        match NulledWrites(qm, r1, inp) {
          case Some(w1) =>
            assert s3.active == [t3] + junk1 + rest && t3.pc == e1 as int;
            assert !AI.bpc_mem(s3.processed, t3.pc, t3.exit_allowed) by {
              assert !(pc1 + 1 <= e1 < e1);
              assert AI.bpc_mem(s3.processed, e1, false) == AI.bpc_mem(s2.processed, e1, false);
              assert e1 != pc1;
              assert AI.bpc_mem(s2.processed, e1, false) == AI.bpc_mem(s.processed, e1, false);
              assert !AI.bpc_mem(s.processed, e1, false);
              assert t3.pc == e1 as int && !t3.exit_allowed;
            }
            var ac3 := junk1 + rest;
            assert s3.active == [t3] + ac3;
            StepSetReg(c, s3, ov, RA.Forward, t3, ac3, CP.end_reg(cid));
            BumpFacts(c, s3, t3);
            t' := t3.(capture_regs := AReg.set_reg(t3.capture_regs, CP.end_reg(cid), Some(cp), s3.clock + 1), pc := t3.pc + 1);
            s' := Bump(s3, t3).(active := [t'] + ac3);
            junk := junk1;
            RegsFromWrite(RegsOf(t3), ws2 + w1, cp, rg0, clk0, s3.clock, WCap(CP.end_reg(cid)), s3.clock + 1);
            assert RegsOf(t') == ApplyWrite(WCap(CP.end_reg(cid)), cp, s3.clock + 1, RegsOf(t3));
            assert NulledWrites(qm, re, inp) == Some([WCap(CP.start_reg(cid))] + w1 + [WCap(CP.end_reg(cid))]);
            assert (ws2 + w1) + [WCap(CP.end_reg(cid))] == ws + ([WCap(CP.start_reg(cid))] + w1 + [WCap(CP.end_reg(cid))]);
            forall th <- junk ensures JunkOk(c, th, s'.processed, pc2, cp, ctx, ov) {
              if JunkOk(c, th, s3.processed, e1, cp, ctx, ov) {
                JunkOkMono(c, th, s3.processed, s'.processed, e1, pc2, cp, ctx, ov);
              } else {
                assert Junk(c, th.pc as nat, e1, cp, ctx, ov);
                assert AI.bpc_mem(s'.processed, e1, false);
              }
            }
          case None =>
            s' := s3; t' := t3; junk := junk1;
            forall th <- junk ensures JunkOk(c, th, s'.processed, pc2, cp, ctx, ov) {
              JunkOkMono(c, th, s3.processed, s'.processed, e1, pc2, cp, ctx, ov);
            }
        }
      case Re_con(r1, r2) =>
        assert {:split_here} true;
        var e1: nat :| NfaRepNulledRE(r1, c, pc1, e1) && NfaRepNulledRE(r2, c, e1, pc2);
        NfaRepNulledMono(r1, c, pc1, e1);
        NfaRepNulledMono(r2, c, e1, pc2);
        assert RestOk(c, rest, s.processed, pc1, e1, cp, ctx, ov);
        var s3, t3, junk1 := NulledRunRE(qm, r1, inp, c, pc1, e1, s, ov, t, rest, ws, rg0, clk0);
        // the head is processed unless r1's region is empty (then it is r2's head)
        assert pc1 < e1 ==> AI.bpc_mem(s3.processed, pc1, false);
        match NulledWrites(qm, r1, inp) {
          case Some(w1) =>
            var rest2 := junk1 + rest;
            assert s3.active == [t3] + rest2;
            assert RestOk(c, rest2, s3.processed, e1, pc2, cp, ctx, ov) by {
              forall th <- rest2 ensures !th.exit_allowed && th.pc >= 0
                  && (th.pc >= pc2 as int || JunkOk(c, th, s3.processed, e1, cp, ctx, ov)
                      || Junk(c, th.pc as nat, e1, cp, ctx, ov))
              {
                if th in junk1 {
                } else {
                  assert th in rest;
                  if th.pc >= pc2 as int {
                  } else if JunkOk(c, th, s.processed, pc1, cp, ctx, ov) {
                    JunkOkMono(c, th, s.processed, s3.processed, pc1, e1, cp, ctx, ov);
                  } else {
                    assert Junk(c, th.pc as nat, pc1, cp, ctx, ov);
                    if pc1 < e1 {
                      assert AI.bpc_mem(s3.processed, pc1, false);
                      assert JunkOk(c, th, s3.processed, e1, cp, ctx, ov);
                    } else {
                      assert pc1 == e1;
                    }
                  }
                }
              }
            }
            var s5, t5, junk2 := NulledRunRE(qm, r2, inp, c, e1, pc2, s3, ov, t3, rest2, ws + w1, rg0, clk0);
            s' := s5; t' := t5; junk := junk2 + junk1;
            assert ProcAgreeOutside(s.processed, s'.processed, pc1, pc2);
            assert pc1 < pc2 ==> AI.bpc_mem(s'.processed, pc1, false) by {
              if pc1 < e1 { } else { assert pc1 == e1; }
            }
            match NulledWrites(qm, r2, inp) {
              case Some(w2) =>
                assert NulledWrites(qm, re, inp) == Some(w1 + w2);
                assert (ws + w1) + w2 == ws + (w1 + w2);
                assert s5.active == [t5] + junk2 + rest2 == [t5] + (junk2 + junk1) + rest;
                forall th <- junk ensures JunkOk(c, th, s'.processed, pc2, cp, ctx, ov)
                                          || Junk(c, th.pc as nat, pc2, cp, ctx, ov)
                {
                  if th in junk2 {
                  } else {
                    assert th in junk1;
                    if JunkOk(c, th, s3.processed, e1, cp, ctx, ov) {
                      JunkOkMono(c, th, s3.processed, s'.processed, e1, pc2, cp, ctx, ov);
                    } else {
                      assert Junk(c, th.pc as nat, e1, cp, ctx, ov);
                      if e1 < pc2 {
                        assert AI.bpc_mem(s'.processed, e1, false);
                        assert JunkOk(c, th, s'.processed, pc2, cp, ctx, ov);
                      } else {
                        assert e1 == pc2;
                      }
                    }
                  }
                }
              case None =>
                assert NulledWrites(qm, re, inp) == None;
                assert s5.active == junk2 + rest2 == (junk2 + junk1) + rest;
                // r2 is not empty (else NulledWrites(r2) == Some([])), so e1 < pc2
                // and the first step of r2's run processed e1.
                assert e1 < pc2 by {
                  if e1 == pc2 { NulledWritesEmptyRegion(qm, r2, inp, c, e1); }
                }
                assert AI.bpc_mem(s'.processed, e1, false);
                forall th <- junk ensures JunkOk(c, th, s'.processed, pc2, cp, ctx, ov) {
                  if th in junk2 {
                  } else {
                    assert th in junk1;
                    if JunkOk(c, th, s3.processed, e1, cp, ctx, ov) {
                      JunkOkMono(c, th, s3.processed, s'.processed, e1, pc2, cp, ctx, ov);
                    } else {
                      assert Junk(c, th.pc as nat, e1, cp, ctx, ov);
                      assert JunkOk(c, th, s'.processed, pc2, cp, ctx, ov);
                    }
                  }
                }
            }
          case None =>
            s' := s3; t' := t3; junk := junk1;
            assert NulledWrites(qm, re, inp) == None;
            // r1 is not empty (else NulledWrites(r1) == Some([])), so pc1 < e1 <= pc2
            assert pc1 < e1 by {
              if pc1 == e1 { NulledWritesEmptyRegion(qm, r1, inp, c, pc1); }
            }
            forall th <- junk ensures JunkOk(c, th, s'.processed, pc2, cp, ctx, ov) {
              JunkOkMono(c, th, s3.processed, s'.processed, e1, pc2, cp, ctx, ov);
            }
        }
      case Re_alt(r1, r2) =>
        assert {:split_here} true;
        var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
                       && NfaRepNulledRE(r1, c, pc1 + 1, e1)
                       && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc2))
                       && NfaRepNulledRE(r2, c, e1 + 1, pc2);
        RegionShapeRE(r1, c, pc1 + 1, e1);
        RegionShapeRE(r2, c, e1 + 1, pc2);
        HeadUnvisited(c, s, t, pc1, pc2);
        StepFork(c, s, ov, RA.Forward, t, rest, pc1 + 1, e1 + 1);
        BumpFacts(c, s, t);
        var tx := AI.Thread(pc1 + 1, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
        var ty := t.(pc := e1 + 1);
        var s2 := Bump(s, t).(active := [tx, ty] + rest);
        var rest1 := [ty] + rest;
        assert s2.active == [tx] + rest1;
        RegsFromWeaken(RegsOf(t), ws, cp, rg0, clk0, s.clock, s2.clock);
        assert RegsOf(tx) == RegsOf(t);
        RestOkShift(c, rest, s.processed, s2.processed, pc1, pc2, pc1 + 1, e1, cp, ctx, ov);
        assert RestOk(c, rest1, s2.processed, pc1 + 1, e1, cp, ctx, ov) by {
          forall th <- rest1 ensures !th.exit_allowed && th.pc >= 0
              && (th.pc >= e1 as int || JunkOk(c, th, s2.processed, pc1 + 1, cp, ctx, ov)
                  || Junk(c, th.pc as nat, pc1 + 1, cp, ctx, ov))
          {
            if th == ty {
            } else {
              assert th in rest;
            }
          }
        }
        var s3, t3, junk1 := NulledRunRE(qm, r1, inp, c, pc1 + 1, e1, s2, ov, tx, rest1, ws, rg0, clk0);
        match NulledWrites(qm, r1, inp) {
          case Some(w1) =>
            assert NulledWrites(qm, re, inp) == Some(w1);
            assert s3.active == [t3] + junk1 + rest1 && t3.pc == e1 as int;
            assert !AI.bpc_mem(s3.processed, t3.pc, t3.exit_allowed) by {
              assert !(pc1 + 1 <= e1 < e1);
              assert AI.bpc_mem(s3.processed, e1, false) == AI.bpc_mem(s2.processed, e1, false);
              assert e1 != pc1;
              assert AI.bpc_mem(s2.processed, e1, false) == AI.bpc_mem(s.processed, e1, false);
              assert !AI.bpc_mem(s.processed, e1, false);
              assert t3.pc == e1 as int && !t3.exit_allowed;
            }
            var ac3 := junk1 + rest1;
            assert s3.active == [t3] + ac3;
            StepJmp(c, s3, ov, RA.Forward, t3, ac3, pc2);
            BumpFacts(c, s3, t3);
            t' := t3.(pc := pc2);
            s' := Bump(s3, t3).(active := [t'] + ac3);
            junk := junk1 + [ty];
            assert [t'] + ac3 == [t'] + junk + rest;
            RegsFromWeaken(RegsOf(t3), ws + w1, cp, rg0, clk0, s3.clock, s'.clock);
            RegionJunkRE(r2, c, e1 + 1, pc2, cp, ctx, ov);
            forall th <- junk ensures !th.exit_allowed && pc1 as int <= th.pc <= pc2 as int
                && (JunkOk(c, th, s'.processed, pc2, cp, ctx, ov) || Junk(c, th.pc as nat, pc2, cp, ctx, ov))
            {
              if th == ty {
                assert Junk(c, e1 + 1, pc2, cp, ctx, ov);
              } else {
                assert th in junk1;
                if JunkOk(c, th, s3.processed, e1, cp, ctx, ov) {
                  JunkOkMono(c, th, s3.processed, s'.processed, e1, pc2, cp, ctx, ov);
                } else {
                  assert Junk(c, th.pc as nat, e1, cp, ctx, ov);
                  assert AI.bpc_mem(s'.processed, e1, false);
                  assert JunkOk(c, th, s'.processed, pc2, cp, ctx, ov);
                }
              }
            }
          case None =>
            assert NulledWrites(qm, re, inp) == NulledWrites(qm, r2, inp);
            assert s3.active == junk1 + rest1 == junk1 + ([ty] + rest);
            // skip the junk of r1's region, then run r2 from ty
            var s4 := JunkSkip(c, s3, ov, junk1, rest1, pc1 + 1, e1);
            assert s4.active == [ty] + rest;
            assert RegsFrom(RegsOf(ty), ws, cp, rg0, clk0, s4.clock) by {
              RegsFromWeaken(RegsOf(t), ws, cp, rg0, clk0, s.clock, s4.clock);
            }
            assert forall p: nat :: e1 + 1 <= p < pc2 ==> !AI.bpc_mem(s4.processed, p, false) by {
              forall p: nat | e1 + 1 <= p < pc2 ensures !AI.bpc_mem(s4.processed, p, false) {
                assert AI.bpc_mem(s4.processed, p, false) == AI.bpc_mem(s3.processed, p, false);
                assert AI.bpc_mem(s3.processed, p, false) == AI.bpc_mem(s2.processed, p, false);
                assert AI.bpc_mem(s2.processed, p, false) == AI.bpc_mem(s.processed, p, false);
              }
            }
            assert AI.bpc_mem(s4.processed, pc1, false);
            RestOkShift(c, rest, s.processed, s4.processed, pc1, pc2, e1 + 1, pc2, cp, ctx, ov);
            var s5, t5, junk2 := NulledRunRE(qm, r2, inp, c, e1 + 1, pc2, s4, ov, ty, rest, ws, rg0, clk0);
            s' := s5; t' := t5; junk := junk2;
            assert ProcAgreeOutside(s.processed, s'.processed, pc1, pc2);
        }
    }
  }

  /** Once the head `pc1` is processed, `RestOk` at `(pc1, pc2)` transfers to
      any later head `pc1' >= pc1` and earlier exit `pc2' <= pc2`: the junk
      bound only grows, the head-bound threads now aim at a processed pc. */
  lemma RestOkShift(c: RB.code, rest: seq<AI.Thread>, p1: AI.Bpcset, p2: AI.Bpcset,
                    pc1: nat, pc2: nat, pc1': nat, pc2': nat, cp: int, ctx: RA.char_context, ov: LOr.OracleView)
    requires ForwardOnly(c)
    requires RestOk(c, rest, p1, pc1, pc2, cp, ctx, ov)
    requires ProcMono(p1, p2) && AI.bpc_mem(p2, pc1, false) && pc1 <= pc1' && pc2' <= pc2
    ensures RestOk(c, rest, p2, pc1', pc2', cp, ctx, ov)
  {
    forall th <- rest ensures !th.exit_allowed && th.pc >= 0
        && (th.pc >= pc2' as int || JunkOk(c, th, p2, pc1', cp, ctx, ov) || Junk(c, th.pc as nat, pc1', cp, ctx, ov))
    {
      if th.pc >= pc2 as int {
      } else if JunkOk(c, th, p1, pc1, cp, ctx, ov) {
        JunkOkMono(c, th, p1, p2, pc1, pc1', cp, ctx, ov);
      } else {
        assert Junk(c, th.pc as nat, pc1, cp, ctx, ov);
        assert JunkOk(c, th, p2, pc1', cp, ctx, ov);
      }
    }
  }

  lemma NulledWritesEmptyRegion(qm: AR.QMap, re: R.regex, inp: LC.Input, c: RB.code, pc: nat)
    requires NfaRepNulledRE(re, c, pc, pc)
    ensures NulledWrites(qm, re, inp) == Some([])
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(c, pc) == Some(RB.Fork(pc + 1, e1 + 1))
                     && NfaRepNulledRE(r1, c, pc + 1, e1)
                     && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc))
                     && NfaRepNulledRE(r2, c, e1 + 1, pc);
      NfaRepNulledMono(r1, c, pc + 1, e1);
      NfaRepNulledMono(r2, c, e1 + 1, pc);
    case Re_con(r1, r2) =>
      var e1: nat :| NfaRepNulledRE(r1, c, pc, e1) && NfaRepNulledRE(r2, c, e1, pc);
      NfaRepNulledMono(r1, c, pc, e1);
      NfaRepNulledMono(r2, c, e1, pc);
      NulledWritesEmptyRegion(qm, r1, inp, c, pc);
      NulledWritesEmptyRegion(qm, r2, inp, c, pc);
      var e: seq<Write> := [];
      assert NulledWrites(qm, re, inp) == Some(e + e);
      assert e + e == e;
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 {
      } else if nul == R.NonNullable {
      } else if q.max == None && nul == R.CINullable && q.greedy {
      } else if q.max == None && nul == R.CDNullable && q.greedy {
      } else {
        NfaRepNulledMono(r1, c, pc + 1, pc);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(c, pc) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
                     && NfaRepNulledRE(r1, c, pc + 1, e1)
                     && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
                     && pc == e1 + 1;
      NfaRepNulledMono(r1, c, pc + 1, e1);
  }

  lemma NfaRepNulledMono(re: R.regex, c: RB.code, pc1: nat, pc2: nat)
    requires NfaRepNulledRE(re, c, pc1, pc2)
    ensures pc1 <= pc2
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
                     && NfaRepNulledRE(r1, c, pc1 + 1, e1)
                     && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc2))
                     && NfaRepNulledRE(r2, c, e1 + 1, pc2);
      NfaRepNulledMono(r1, c, pc1 + 1, e1);
      NfaRepNulledMono(r2, c, e1 + 1, pc2);
    case Re_con(r1, r2) =>
      var e1: nat :| NfaRepNulledRE(r1, c, pc1, e1) && NfaRepNulledRE(r2, c, e1, pc2);
      NfaRepNulledMono(r1, c, pc1, e1);
      NfaRepNulledMono(r2, c, e1, pc2);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 {
      } else if nul == R.NonNullable {
      } else if q.max == None && nul == R.CINullable && q.greedy {
      } else if q.max == None && nul == R.CDNullable && q.greedy {
      } else {
        NfaRepNulledMono(r1, c, pc1 + 1, pc2);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
                     && NfaRepNulledRE(r1, c, pc1 + 1, e1)
                     && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
                     && pc2 == e1 + 1;
      NfaRepNulledMono(r1, c, pc1 + 1, e1);
  }

  // ===========================================================================
  // 9. THE TOP-LEVEL STATEMENT over `FNullInterp`.
  // ===========================================================================

  /** One epsilon closure over `compile_reconstruct_nulled(re)` from a single
      thread at `CpOf(inp)`: it accepts iff `NulledWrites` is `Some`, leaves the
      oracle view untouched, and the accepting thread's registers are the
      initial ones with `NulledWrites` applied at strictly increasing clocks
      above the start clock. */
  lemma NullInterpNulled(qm: AR.QMap, re: R.regex, inp: LC.Input, s0: AI.VmState, ov: LOr.OracleView,
                         cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, clk: int)
    requires NoCdnPlusRE(re) && ov == qm.ov
    requires var c := CP.compile_reconstruct_nulled(re);
             s0 == AI.FInitState(c, TR.CpOf(inp) as int, cap, lk, qt, clk, TR.CtxOf(inp)).(cdn := s0.cdn)
    ensures var c := CP.compile_reconstruct_nulled(re);
      var (res, sf, ov') := AI.FNullInterp(c, s0, ov, RA.Forward);
      ov' == ov
      && (res.Some? <==> NulledWrites(qm, re, inp).Some?)
      && (res.Some? ==> RegsFrom(RegsOf(res.value), NulledWrites(qm, re, inp).value,
                                 TR.CpOf(inp) as int, (cap, lk, qt), clk, sf.clock))
  {
    var c := CP.compile_reconstruct_nulled(re);
    CompileReconstructNulledLayout(re);
    ReconstructCodeShape(re);
    var n: nat := |c| - 1;
    var cp := TR.CpOf(inp) as int;
    var t0 := AI.init_thread(cap, lk, qt);
    assert s0.active == [t0] + [];
    assert Sized(c, s0);
    RegsFromNil((cap, lk, qt), cp, clk, s0.clock);
    assert RegsOf(t0) == (cap, lk, qt);
    assert forall p: nat :: 0 <= p < n ==> !AI.bpc_mem(s0.processed, p, false);
    assert RestOk(c, [], s0.processed, 0, n, cp, s0.context, ov);
    var s', t', junk := NulledRunRE(qm, re, inp, c, 0, n, s0, ov, t0, [], [], (cap, lk, qt), clk);
    OvStable(c, s', ov);
    match NulledWrites(qm, re, inp) {
      case Some(w) =>
        assert s'.active == [t'] + junk + [] == [t'] + junk;
        assert !AI.bpc_mem(s'.processed, t'.pc, t'.exit_allowed) by {
          assert AI.bpc_mem(s'.processed, n, false) == AI.bpc_mem(s0.processed, n, false);
        }
        assert RB.get_instr(c, t'.pc) == RB.Accept;
        StepAccept(c, s', ov, RA.Forward, t', junk);
        var sf := Bump(s', t').(active := [], bestmatch := Some(t'));
        assert AI.FAdvanceEpsilon(c, s0, ov, RA.Forward) == (sf, ov);
        assert [] + w == w;
        RegsFromWeaken(RegsOf(t'), w, cp, (cap, lk, qt), clk, s'.clock, sf.clock);
      case None =>
        assert s'.active == junk + [] == junk;
        var s'' := JunkSkip(c, s', ov, junk, [], 0, n);
        assert s''.active == [];
        assert AI.FAdvanceEpsilon(c, s'', ov, RA.Forward) == (s'', ov);
        assert s''.bestmatch == None;
    }
  }

  /** The closure never writes the oracle over code without `WriteOracle`. */
  lemma OvStable(c: RB.code, s: AI.VmState, ov: LOr.OracleView)
    requires Sized(c, s)
    requires forall p: nat :: p < |c| ==> !c[p].WriteOracle?
    ensures AI.FAdvanceEpsilon(c, s, ov, RA.Forward).1 == ov
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      OvStable(c, s.(active := ac), ov);
      return;
    }
    var s1 := Bump(s, t);
    BumpFacts(c, s, t);
    match RB.get_instr(c, t.pc) {
      case Consume(ce) =>
        var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
        OvStable(c, s1.(blocked := nb, isblocked := ni, active := ac), ov);
      case Accept =>
      case Jmp(x) => OvStable(c, s1.(active := [t.(pc := x)] + ac), ov);
      case Fork(x, y) =>
        var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
        OvStable(c, s1.(active := [newt, t.(pc := y)] + ac), ov);
      case SetRegisterToCP(reg) =>
        OvStable(c, s1.(active := [t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1)] + ac), ov);
      case SetQuantToClock(q, b) =>
        OvStable(c, s1.(active := [t.(quant_regs := AReg.set_reg(t.quant_regs, q, if b then Some(s1.cp) else None, s1.clock), pc := t.pc + 1)] + ac), ov);
      case CheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          OvStable(c, s1.(active := [t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock))] + ac), ov);
        } else {
          OvStable(c, s1.(active := ac), ov);
        }
      case NegCheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          OvStable(c, s1.(active := ac), ov);
        } else {
          OvStable(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
        }
      case WriteOracle(l) =>
        assert 0 <= t.pc < |c|;
        assert false;
      case BeginLoop =>
        OvStable(c, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov);
      case EndLoop =>
        if t.exit_allowed {
          OvStable(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
        } else {
          OvStable(c, s1.(active := ac), ov);
        }
      case CheckNullable(qid) =>
        if LCdn.cdn_get(s1.cdn, qid) {
          OvStable(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
        } else {
          OvStable(c, s1.(active := ac), ov);
        }
      case AnchorAssertion(a) =>
        if RA.is_satisfied(a, s1.context, RA.Forward) {
          OvStable(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
        } else {
          OvStable(c, s1.(active := ac), ov);
        }
      case Fail =>
        OvStable(c, s1.(active := ac), ov);
    }
  }
}
