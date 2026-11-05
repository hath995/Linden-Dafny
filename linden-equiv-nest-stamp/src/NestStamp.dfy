// §2.5b STAGE 2, RUNG D — the POSITIONAL STAMP invariant.
//
// `NestStampRE` is the stamp-only mirror of `NI.NestInvRE`: it locates a
// thread's `pc` in the compiled block structure (`NfaRepRE`'s layout) and
// claims, at every site the thread can only have reached THROUGH a
// quantifier's clock mark `SetQuantToClock(qid, false)`, that `qid`'s
// nulled-exit stamp is CLEAR (`qcp[qid] < 0`).
//
// Why a separate family rather than a `qcp` parameter threaded through
// `NestInvRE`: the claim is register-independent (it reads only `qcp`), so
// EVERY step that does not write a quant register preserves it by one
// `NestStampAdvance`, and `NestInvRE` — the hot predicate whose inline size
// already forced `NestInvGenRE`/`NestInvCinRE` out of line — keeps its exact
// axiom.
//
// What it buys (rung D): a live stamp's body groups are replaced wholesale by
// the reconstruction chain in the readout `GmOfLiveR`, so a capture write must
// never land inside a LIVE stamp's body. Structurally: every entry into
// `qid`'s body passes `qid`'s clock mark, which clears the stamp; the only
// in-block sites where a stale stamp survives are the head fork, the mark
// itself and the true-stamp instruction — none of which writes a capture
// register (`NestStampWriteOutside`).
module LindenElkNestStamp {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import NR = LindenElkNfaRep
  import AI = ArrayInterp
  import PIV = LindenElkPikeInv
  import NI = LindenElkNestInv

  // =========================================================================
  // 1. The invariant.
  // =========================================================================

  /** `qid`'s nulled-exit stamp is clear. */
  ghost predicate StampClearRE(qcp: seq<int>, qid: R.quantid) {
    AI.get_idx(qcp, qid) < 0
  }

  /** The stamp invariant for a forced-copy chain (`NfaRepMinRE`): at the FIRST
      copy head (the chain's own mark site) nothing is claimed — the thread has
      not run the mark yet; anywhere past it the mark has run, so the stamp is
      clear for the rest of the chain (copy heads included). */
  ghost predicate NestStampMinRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code,
                                 pcb: nat, pce: nat, pc: nat, qcp: seq<int>)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    decreases CP.rsize(r1), k + 2
  {
    k > 0 ==>
    exists e1: nat {:trigger NR.NfaRepRE(r1, code, pcb + 1, e1)} ::
      NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce)
      && if pc == pcb then true                         // the mark site: no claim
         else StampClearRE(qcp, qid)
              && (if pc < e1 then NestStampRE(r1, code, pcb + 1, e1, pc, qcp)
                  else NestStampMinRE(k - 1, qid, r1, code, e1, pce, pc, qcp))
  }

  /** The stamp invariant for an optional-layer chain (`NfaRepOptRE`): each
      layer's fork and mark sites claim nothing, everything from its
      `BeginLoop` on claims the clear stamp. */
  ghost predicate NestStampOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                                 pcb: nat, pce: nat, pc: nat, qcp: seq<int>)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    decreases CP.rsize(r1), k + 2
  {
    k > 0 ==>
    exists e1: nat ::
      NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, pcb + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce)
      && if pc == pcb || pc == pcb + 1 then true        // fork / mark site: no claim
         else if pc == pcb + 2 then StampClearRE(qcp, qid)
         else if pcb + 3 <= pc < e1 then
           StampClearRE(qcp, qid) && NestStampRE(r1, code, pcb + 3, e1, pc, qcp)
         else if pc == e1 then StampClearRE(qcp, qid)
         else NestStampOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, qcp)
  }

  /** (§2.5a) The GENERIC unbounded-`min` arm: `min` forced copies then the
      ordinary star loop at `em`. Named (not inlined) for the same axiom-size
      reason as `NI.NestInvGenRE`. */
  ghost predicate NestStampGenRE(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier,
                                 r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat, qcp: seq<int>)
    requires q.min > 0
    decreases CP.rsize(r1), q.min as nat + 3
  {
    var mn := q.min as nat;
    exists em: nat, e1: nat
      {:trigger NR.NfaRepMinRE(mn, qid, r1, code, pcb, em), NR.NfaRepRE(r1, code, em + 3, e1)} ::
      NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
      && NR.GetPcRE(code, em) == Some(RB.Fork(e1 + 2, em + 1))
      && NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, em + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, em + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(em))
      && pce == e1 + 2
      && if pc < em then NestStampMinRE(mn, qid, r1, code, pcb, em, pc, qcp)
         else if pc == em || pc == em + 1 then true
         else if pc == em + 2 then StampClearRE(qcp, qid)
         else if em + 3 <= pc < e1 then
           StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 3, e1, pc, qcp)
         else StampClearRE(qcp, qid)
  }

  /** (§2.5b) The CIN-GREEDY end-fork arm: `min - 1` forced copies, then the
      guarded loop whose exit stamps `SetQuantToClock(qid, true)` at `e1 + 2`.
      The trailing stamp site carries NO claim — the head fork's skip arm jumps
      there directly, before any mark of `qid` on this pass. */
  ghost predicate NestStampCinRE(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier,
                                 r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat, qcp: seq<int>)
    requires q.min > 0
    decreases CP.rsize(r1), q.min as nat + 3
  {
    var mn1 := (q.min - 1) as nat;
    exists em: nat, e1: nat
      {:trigger NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em), NR.NfaRepRE(r1, code, em + 3, e1)} ::
      NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
      && NR.GetPcRE(code, em) == Some(RB.Fork(em + 1, e1 + 2))
      && NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, em + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, em + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.GetPcRE(code, e1 + 1) == Some(RB.Fork(em + 1, e1 + 3))
      && NR.GetPcRE(code, e1 + 2) == Some(RB.SetQuantToClock(qid, true))
      && pce == e1 + 3
      && if pc < em then NestStampMinRE(mn1, qid, r1, code, pcb, em, pc, qcp)
         else if pc == em || pc == em + 1 then true
         else if pc == em + 2 then StampClearRE(qcp, qid)
         else if em + 3 <= pc < e1 then
           StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 3, e1, pc, qcp)
         else if pc == e1 || pc == e1 + 1 then StampClearRE(qcp, qid)
         else true                                      // the true-stamp site
  }

  /** THE INVARIANT: `pc` sits inside `re`'s compiled block `[pcb, pce)`; every
      quantifier whose clock mark the thread must have run to be at `pc` has a
      clear stamp. Dispatches on `re`'s shape exactly like `NI.NestInvRE`. */
  ghost predicate NestStampRE(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat, qcp: seq<int>)
    requires NR.NfaRepRE(re, code, pcb, pce)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty => true
    case Re_character(_) => true
    case Re_alt(r1, r2) =>
      exists e1: nat ::
        NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && if pc == pcb then true
           else if pcb + 1 <= pc < e1 then NestStampRE(r1, code, pcb + 1, e1, pc, qcp)
           else if pc == e1 then true
           else NestStampRE(r2, code, e1 + 1, pce, pc, qcp)
    case Re_con(r1, r2) =>
      exists e1: nat ::
        NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && if pc < e1 then NestStampRE(r1, code, pcb, e1, pc, qcp)
           else NestStampRE(r2, code, e1, pce, pc, qcp)
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None then
        exists e1: nat ::
          NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
          && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, code, pcb + 3, e1)
          && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
          && pce == e1 + 2
          && if pc == pcb || pc == pcb + 1 then true
             else if pc == pcb + 2 then StampClearRE(qcp, qid)
             else if pcb + 3 <= pc < e1 then
               StampClearRE(qcp, qid) && NestStampRE(r1, code, pcb + 3, e1, pc, qcp)
             else StampClearRE(qcp, qid)
      else if q.max.Some? then
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        exists em: nat ::
          NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid, r1, code, em, pce)
          && if pc < em then NestStampMinRE(mn, qid, r1, code, pcb, em, pc, qcp)
             else NestStampOptRE(kx, q.greedy, qid, r1, code, em, pce, pc, qcp)
      else if nul == R.NonNullable then
        var mn1 := (q.min - 1) as nat;
        exists em: nat, e1: nat ::
          NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
          && NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
          && NR.NfaRepRE(r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pce == e1 + 1
          && if pc < em then NestStampMinRE(mn1, qid, r1, code, pcb, em, pc, qcp)
             else if pc == em then true                 // the mark site: no claim
             else if em + 1 <= pc < e1 then
               StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 1, e1, pc, qcp)
             else StampClearRE(qcp, qid)
      else if !q.greedy then
        NestStampGenRE(nul, qid, q, r1, code, pcb, pce, pc, qcp)
      else
        NestStampCinRE(nul, qid, q, r1, code, pcb, pce, pc, qcp)
    case Re_capture(cid, r1) =>
      exists e1: nat ::
        NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && (pcb + 1 <= pc < e1 ==> NestStampRE(r1, code, pcb + 1, e1, pc, qcp))
    case Re_lookaround(_, _, _) => true
    case Re_anchor(_) => true
  }

  /** The top-level wrapper (mirror of `NI.NestTopRE`). */
  ghost predicate NestStampTopRE(re: R.regex, code: RB.code, endl: nat, pc: nat, qcp: seq<int>)
    requires NR.NfaRepRE(re, code, 0, endl)
  {
    pc == endl || (pc < endl && NestStampRE(re, code, 0, endl, pc, qcp))
  }

  // =========================================================================
  // 2. Inversion / introduction for the two named arms (mirrors of
  //    `NI.NestInvGenREInv` and friends: consumers never unfold the
  //    triggered existential themselves).
  // =========================================================================

  lemma NestStampGenREInv(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier,
                          r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat, qcp: seq<int>)
    returns (em: nat, e1: nat)
    requires q.min > 0
    requires NestStampGenRE(nul, qid, q, r1, code, pcb, pce, pc, qcp)
    ensures NR.NfaRepMinRE(q.min as nat, qid, r1, code, pcb, em)
    ensures NR.GetPcRE(code, em) == Some(RB.Fork(e1 + 2, em + 1))
    ensures NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qid, false))
    ensures NR.GetPcRE(code, em + 2) == Some(RB.BeginLoop)
    ensures NR.NfaRepRE(r1, code, em + 3, e1)
    ensures NR.GetPcRE(code, e1) == Some(RB.EndLoop)
    ensures NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(em))
    ensures pce == e1 + 2
    ensures pc < em ==> NestStampMinRE(q.min as nat, qid, r1, code, pcb, em, pc, qcp)
    ensures pc == em + 2 ==> StampClearRE(qcp, qid)
    ensures em + 3 <= pc < e1 ==>
              StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 3, e1, pc, qcp)
    ensures pc >= e1 ==> StampClearRE(qcp, qid)
  {
    var mn := q.min as nat;
    em, e1 :|
      NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
      && NR.GetPcRE(code, em) == Some(RB.Fork(e1 + 2, em + 1))
      && NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, em + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, em + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(em))
      && pce == e1 + 2
      && if pc < em then NestStampMinRE(mn, qid, r1, code, pcb, em, pc, qcp)
         else if pc == em || pc == em + 1 then true
         else if pc == em + 2 then StampClearRE(qcp, qid)
         else if em + 3 <= pc < e1 then
           StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 3, e1, pc, qcp)
         else StampClearRE(qcp, qid);
    NR.NfaRepIncrRE(r1, code, em + 3, e1);
  }

  lemma NestStampGenREIntro(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier,
                            r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat, qcp: seq<int>,
                            em: nat, e1: nat)
    requires q.min > 0
    requires NR.NfaRepMinRE(q.min as nat, qid, r1, code, pcb, em)
    requires NR.GetPcRE(code, em) == Some(RB.Fork(e1 + 2, em + 1))
    requires NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qid, false))
    requires NR.GetPcRE(code, em + 2) == Some(RB.BeginLoop)
    requires NR.NfaRepRE(r1, code, em + 3, e1)
    requires NR.GetPcRE(code, e1) == Some(RB.EndLoop)
    requires NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(em))
    requires pce == e1 + 2
    requires pc < em ==> NestStampMinRE(q.min as nat, qid, r1, code, pcb, em, pc, qcp)
    requires pc == em + 2 ==> StampClearRE(qcp, qid)
    requires em + 3 <= pc < e1 ==>
               StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 3, e1, pc, qcp)
    requires pc >= e1 ==> StampClearRE(qcp, qid)
    ensures NestStampGenRE(nul, qid, q, r1, code, pcb, pce, pc, qcp)
  {
    var mn := q.min as nat;
    assert NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
      && NR.GetPcRE(code, em) == Some(RB.Fork(e1 + 2, em + 1))
      && NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, em + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, em + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(em))
      && pce == e1 + 2
      && if pc < em then NestStampMinRE(mn, qid, r1, code, pcb, em, pc, qcp)
         else if pc == em || pc == em + 1 then true
         else if pc == em + 2 then StampClearRE(qcp, qid)
         else if em + 3 <= pc < e1 then
           StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 3, e1, pc, qcp)
         else StampClearRE(qcp, qid);
  }

  lemma NestStampCinREInv(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier,
                          r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat, qcp: seq<int>)
    returns (em: nat, e1: nat)
    requires q.min > 0
    requires NestStampCinRE(nul, qid, q, r1, code, pcb, pce, pc, qcp)
    ensures NR.NfaRepMinRE((q.min - 1) as nat, qid, r1, code, pcb, em)
    ensures NR.GetPcRE(code, em) == Some(RB.Fork(em + 1, e1 + 2))
    ensures NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qid, false))
    ensures NR.GetPcRE(code, em + 2) == Some(RB.BeginLoop)
    ensures NR.NfaRepRE(r1, code, em + 3, e1)
    ensures NR.GetPcRE(code, e1) == Some(RB.EndLoop)
    ensures NR.GetPcRE(code, e1 + 1) == Some(RB.Fork(em + 1, e1 + 3))
    ensures NR.GetPcRE(code, e1 + 2) == Some(RB.SetQuantToClock(qid, true))
    ensures pce == e1 + 3
    ensures pc < em ==> NestStampMinRE((q.min - 1) as nat, qid, r1, code, pcb, em, pc, qcp)
    ensures pc == em + 2 ==> StampClearRE(qcp, qid)
    ensures em + 3 <= pc < e1 ==>
              StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 3, e1, pc, qcp)
    ensures pc == e1 || pc == e1 + 1 ==> StampClearRE(qcp, qid)
  {
    var mn1 := (q.min - 1) as nat;
    em, e1 :|
      NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
      && NR.GetPcRE(code, em) == Some(RB.Fork(em + 1, e1 + 2))
      && NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, em + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, em + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.GetPcRE(code, e1 + 1) == Some(RB.Fork(em + 1, e1 + 3))
      && NR.GetPcRE(code, e1 + 2) == Some(RB.SetQuantToClock(qid, true))
      && pce == e1 + 3
      && if pc < em then NestStampMinRE(mn1, qid, r1, code, pcb, em, pc, qcp)
         else if pc == em || pc == em + 1 then true
         else if pc == em + 2 then StampClearRE(qcp, qid)
         else if em + 3 <= pc < e1 then
           StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 3, e1, pc, qcp)
         else if pc == e1 || pc == e1 + 1 then StampClearRE(qcp, qid)
         else true;
    NR.NfaRepIncrRE(r1, code, em + 3, e1);
  }

  lemma NestStampCinREIntro(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier,
                            r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat, qcp: seq<int>,
                            em: nat, e1: nat)
    requires q.min > 0
    requires NR.NfaRepMinRE((q.min - 1) as nat, qid, r1, code, pcb, em)
    requires NR.GetPcRE(code, em) == Some(RB.Fork(em + 1, e1 + 2))
    requires NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qid, false))
    requires NR.GetPcRE(code, em + 2) == Some(RB.BeginLoop)
    requires NR.NfaRepRE(r1, code, em + 3, e1)
    requires NR.GetPcRE(code, e1) == Some(RB.EndLoop)
    requires NR.GetPcRE(code, e1 + 1) == Some(RB.Fork(em + 1, e1 + 3))
    requires NR.GetPcRE(code, e1 + 2) == Some(RB.SetQuantToClock(qid, true))
    requires pce == e1 + 3
    requires pc < em ==> NestStampMinRE((q.min - 1) as nat, qid, r1, code, pcb, em, pc, qcp)
    requires pc == em + 2 ==> StampClearRE(qcp, qid)
    requires em + 3 <= pc < e1 ==>
               StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 3, e1, pc, qcp)
    requires pc == e1 || pc == e1 + 1 ==> StampClearRE(qcp, qid)
    ensures NestStampCinRE(nul, qid, q, r1, code, pcb, pce, pc, qcp)
  {
    var mn1 := (q.min - 1) as nat;
    assert NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
      && NR.GetPcRE(code, em) == Some(RB.Fork(em + 1, e1 + 2))
      && NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, em + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, em + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.GetPcRE(code, e1 + 1) == Some(RB.Fork(em + 1, e1 + 3))
      && NR.GetPcRE(code, e1 + 2) == Some(RB.SetQuantToClock(qid, true))
      && pce == e1 + 3
      && if pc < em then NestStampMinRE(mn1, qid, r1, code, pcb, em, pc, qcp)
         else if pc == em || pc == em + 1 then true
         else if pc == em + 2 then StampClearRE(qcp, qid)
         else if em + 3 <= pc < e1 then
           StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 3, e1, pc, qcp)
         else if pc == e1 || pc == e1 + 1 then StampClearRE(qcp, qid)
         else true;
  }

  // =========================================================================
  // 3. Entry: arriving at a block's head satisfies the invariant there —
  //    unconditionally, since every head site (fork / mark / capture open)
  //    carries no claim.
  // =========================================================================

  lemma NestStampMinEntryRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat,
                            qcp: seq<int>)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    ensures NestStampMinRE(k, qid, r1, code, pcb, pce, pcb, qcp)
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce);
    }
  }

  lemma NestStampOptEntryRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                            pcb: nat, pce: nat, qcp: seq<int>)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    ensures NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pcb, qcp)
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
      NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    }
  }

  lemma NestStampEntryRE(re: R.regex, code: RB.code, pcb: nat, pce: nat, qcp: seq<int>)
    requires NR.NfaRepRE(re, code, pcb, pce)
    ensures NestStampRE(re, code, pcb, pce, pcb, qcp)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce);
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce);
      if pcb < e1 {
        NestStampEntryRE(r1, code, pcb, e1, qcp);
      } else {
        NR.NfaRepIncrRE(r1, code, pcb, e1);
        assert e1 == pcb;
        NestStampEntryRE(r2, code, e1, pce, qcp);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        // entry pc == pcb is the fork: no claims.
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, pcb, pce);
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        if pcb < em {
          NestStampMinEntryRE(mn, qid, r1, code, pcb, em, qcp);
        } else {
          NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
          assert em == pcb;
          NestStampOptEntryRE(kx, q.greedy, qid, r1, code, em, pce, qcp);
        }
      } else if nul != R.NonNullable && !q.greedy {
        var em, e1 := NR.NfaRepREGenInv(nul, qid, q, r1, code, pcb, pce);
        var mn := q.min as nat;
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);      // pcb <= em < em + 3 <= e1: the entry claims nothing
        if pcb < em {
          NestStampMinEntryRE(mn, qid, r1, code, pcb, em, qcp);
        } else {
          assert em == pcb;
        }
        NestStampGenREIntro(nul, qid, q, r1, code, pcb, pce, pcb, qcp, em, e1);
      } else if nul != R.NonNullable {
        var em, e1 := NR.NfaRepRECinInv(nul, qid, q, r1, code, pcb, pce);
        var mn1 := (q.min - 1) as nat;
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pcb < em {
          NestStampMinEntryRE(mn1, qid, r1, code, pcb, em, qcp);
        } else {
          assert em == pcb;
        }
        NestStampCinREIntro(nul, qid, q, r1, code, pcb, pce, pcb, qcp, em, e1);
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, pcb, pce);
        var mn1 := (q.min - 1) as nat;
        if pcb < em {
          NestStampMinEntryRE(mn1, qid, r1, code, pcb, em, qcp);
        } else {
          NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
          assert em == pcb;
        }
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1;
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
  }

  /** At `pc == 0` the invariant holds for any stamp bank. */
  lemma NestStampTopInit(re: R.regex, code: RB.code, endl: nat, qcp: seq<int>)
    requires NR.NfaRepRE(re, code, 0, endl)
    ensures NestStampTopRE(re, code, endl, 0, qcp)
  {
    if 0 < endl {
      NestStampEntryRE(re, code, 0, endl, qcp);
    } else {
      NR.NfaRepIncrRE(re, code, 0, endl);
      assert endl == 0;
    }
  }

  // =========================================================================
  // 4. Monotonicity: clearing stamps only strengthens the invariant. This is
  //    what makes the clock-mark step (`SetQuantToClock(qid, false)`) free
  //    once the positional step is done.
  // =========================================================================

  ghost predicate StampsWeaken(qcp: seq<int>, qcp': seq<int>) {
    forall k: int :: AI.get_idx(qcp, k) < 0 ==> AI.get_idx(qcp', k) < 0
  }

  lemma NestStampMonoMinRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat,
                           pc: nat, qcp: seq<int>, qcp': seq<int>)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    requires NestStampMinRE(k, qid, r1, code, pcb, pce, pc, qcp)
    requires StampsWeaken(qcp, qcp')
    ensures NestStampMinRE(k, qid, r1, code, pcb, pce, pc, qcp')
    decreases CP.rsize(r1), k + 2
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce)
        && if pc == pcb then true
           else StampClearRE(qcp, qid)
                && (if pc < e1 then NestStampRE(r1, code, pcb + 1, e1, pc, qcp)
                    else NestStampMinRE(k - 1, qid, r1, code, e1, pce, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, pce);
      if pc != pcb {
        if pc < e1 {
          NestStampMonoRE(r1, code, pcb + 1, e1, pc, qcp, qcp');
        } else {
          NestStampMonoMinRE(k - 1, qid, r1, code, e1, pce, pc, qcp, qcp');
        }
      }
    }
  }

  lemma NestStampMonoOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                           pcb: nat, pce: nat, pc: nat, qcp: seq<int>, qcp': seq<int>)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    requires NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc, qcp)
    requires StampsWeaken(qcp, qcp')
    ensures NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc, qcp')
    decreases CP.rsize(r1), k + 2
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce)
        && if pc == pcb || pc == pcb + 1 then true
           else if pc == pcb + 2 then StampClearRE(qcp, qid)
           else if pcb + 3 <= pc < e1 then
             StampClearRE(qcp, qid) && NestStampRE(r1, code, pcb + 3, e1, pc, qcp)
           else if pc == e1 then StampClearRE(qcp, qid)
           else NestStampOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, qcp);
      NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
      NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
      if pcb + 3 <= pc < e1 {
        NestStampMonoRE(r1, code, pcb + 3, e1, pc, qcp, qcp');
      } else if pc > e1 {
        NestStampMonoOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, qcp, qcp');
      }
    }
  }

  lemma NestStampMonoRE(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                        qcp: seq<int>, qcp': seq<int>)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires StampsWeaken(qcp, qcp')
    ensures NestStampRE(re, code, pcb, pce, pc, qcp')
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && if pc == pcb then true
           else if pcb + 1 <= pc < e1 then NestStampRE(r1, code, pcb + 1, e1, pc, qcp)
           else if pc == e1 then true
           else NestStampRE(r2, code, e1 + 1, pce, pc, qcp);
      if pcb + 1 <= pc < e1 {
        NestStampMonoRE(r1, code, pcb + 1, e1, pc, qcp, qcp');
      } else if pc != pcb && pc != e1 {
        NestStampMonoRE(r2, code, e1 + 1, pce, pc, qcp, qcp');
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && if pc < e1 then NestStampRE(r1, code, pcb, e1, pc, qcp)
           else NestStampRE(r2, code, e1, pce, pc, qcp);
      if pc < e1 {
        NestStampMonoRE(r1, code, pcb, e1, pc, qcp, qcp');
      } else {
        NestStampMonoRE(r2, code, e1, pce, pc, qcp, qcp');
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
          && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, code, pcb + 3, e1)
          && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
          && pce == e1 + 2
          && if pc == pcb || pc == pcb + 1 then true
             else if pc == pcb + 2 then StampClearRE(qcp, qid)
             else if pcb + 3 <= pc < e1 then
               StampClearRE(qcp, qid) && NestStampRE(r1, code, pcb + 3, e1, pc, qcp)
             else StampClearRE(qcp, qid);
        if pcb + 3 <= pc < e1 {
          NestStampMonoRE(r1, code, pcb + 3, e1, pc, qcp, qcp');
        }
      } else if q.max.Some? {
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid, r1, code, em, pce)
          && (if pc < em then NestStampMinRE(mn, qid, r1, code, pcb, em, pc, qcp)
              else NestStampOptRE(kx, q.greedy, qid, r1, code, em, pce, pc, qcp));
        if pc < em {
          NestStampMonoMinRE(mn, qid, r1, code, pcb, em, pc, qcp, qcp');
        } else {
          NestStampMonoOptRE(kx, q.greedy, qid, r1, code, em, pce, pc, qcp, qcp');
        }
      } else if nul == R.NonNullable {
        var mn1 := (q.min - 1) as nat;
        var em: nat, e1: nat :| NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
          && NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
          && NR.NfaRepRE(r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pce == e1 + 1
          && if pc < em then NestStampMinRE(mn1, qid, r1, code, pcb, em, pc, qcp)
             else if pc == em then true
             else if em + 1 <= pc < e1 then
               StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 1, e1, pc, qcp)
             else StampClearRE(qcp, qid);
        if pc < em {
          NestStampMonoMinRE(mn1, qid, r1, code, pcb, em, pc, qcp, qcp');
        } else if em + 1 <= pc < e1 {
          NestStampMonoRE(r1, code, em + 1, e1, pc, qcp, qcp');
        }
      } else if !q.greedy {
        var em, e1 := NestStampGenREInv(nul, qid, q, r1, code, pcb, pce, pc, qcp);
        var mn := q.min as nat;
        if pc < em {
          NestStampMonoMinRE(mn, qid, r1, code, pcb, em, pc, qcp, qcp');
        } else if em + 3 <= pc < e1 {
          NestStampMonoRE(r1, code, em + 3, e1, pc, qcp, qcp');
        }
        NestStampGenREIntro(nul, qid, q, r1, code, pcb, pce, pc, qcp', em, e1);
      } else {
        var em, e1 := NestStampCinREInv(nul, qid, q, r1, code, pcb, pce, pc, qcp);
        var mn1 := (q.min - 1) as nat;
        if pc < em {
          NestStampMonoMinRE(mn1, qid, r1, code, pcb, em, pc, qcp, qcp');
        } else if em + 3 <= pc < e1 {
          NestStampMonoRE(r1, code, em + 3, e1, pc, qcp, qcp');
        }
        NestStampCinREIntro(nul, qid, q, r1, code, pcb, pce, pc, qcp', em, e1);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && (pcb + 1 <= pc < e1 ==> NestStampRE(r1, code, pcb + 1, e1, pc, qcp));
      if pcb + 1 <= pc < e1 {
        NestStampMonoRE(r1, code, pcb + 1, e1, pc, qcp, qcp');
      }
  }

  // =========================================================================
  // 5. Preservation across a non-quant-writing step. `StampEdgeRE` is
  //    `NI.StepEdgeRE` widened to the capture OPEN write (an even register):
  //    the stamp invariant reads no capture register, so open and close writes
  //    are the same edge for it.
  // =========================================================================

  ghost predicate StampEdgeRE(code: RB.code, pc: nat, pc': nat) {
    match NR.GetPcRE(code, pc)
    case Some(Consume(_)) => pc' == pc + 1
    case Some(AnchorAssertion(_)) => pc' == pc + 1
    case Some(CheckOracle(_)) => pc' == pc + 1
    case Some(NegCheckOracle(_)) => pc' == pc + 1
    case Some(BeginLoop) => pc' == pc + 1
    case Some(EndLoop) => pc' == pc + 1
    case Some(Fork(x, y)) => (pc' as int == x) || (pc' as int == y)
    case Some(Jmp(x)) => pc' as int == x
    case Some(SetRegisterToCP(_)) => pc' == pc + 1
    case _ => false
  }

  lemma NestStampAdvanceMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat,
                            pc: nat, pc': nat, qcp: seq<int>)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    requires pcb <= pc < pce
    requires NestStampMinRE(k, qid, r1, code, pcb, pce, pc, qcp)
    requires StampEdgeRE(code, pc, pc')
    ensures pc' == pce || (pcb <= pc' < pce && NestStampMinRE(k, qid, r1, code, pcb, pce, pc', qcp))
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce)
      && (if pc == pcb then true
          else StampClearRE(qcp, qid)
               && (if pc < e1 then NestStampRE(r1, code, pcb + 1, e1, pc, qcp)
                   else NestStampMinRE(k - 1, qid, r1, code, e1, pce, pc, qcp)));
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, pce);
    if pc == pcb {
      assert false;                                 // SetQuantToClock is not a StampEdge
    } else if pc < e1 {
      NestStampAdvanceRE(r1, code, pcb + 1, e1, pc, pc', qcp);
      if pc' == e1 {
        if k - 1 == 0 {
          assert pc' == pce;
        } else {
          NestStampMinEntryRE(k - 1, qid, r1, code, e1, pce, qcp);
          NI.NfaRepMinPosRE(k - 1, qid, r1, code, e1, pce);
          assert NestStampMinRE(k, qid, r1, code, pcb, pce, pc', qcp);
        }
      } else {
        assert NestStampMinRE(k, qid, r1, code, pcb, pce, pc', qcp);
      }
    } else {
      NestStampAdvanceMin(k - 1, qid, r1, code, e1, pce, pc, pc', qcp);
      if pc' != pce {
        assert NestStampMinRE(k, qid, r1, code, pcb, pce, pc', qcp);
      }
    }
  }

  lemma NestStampAdvanceOpt(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                            pcb: nat, pce: nat, pc: nat, pc': nat, qcp: seq<int>)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    requires pcb <= pc < pce
    requires NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc, qcp)
    requires StampEdgeRE(code, pc, pc')
    ensures pc' == pce || (pcb <= pc' < pce && NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc', qcp))
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, pcb + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce)
      && (if pc == pcb || pc == pcb + 1 then true
          else if pc == pcb + 2 then StampClearRE(qcp, qid)
          else if pcb + 3 <= pc < e1 then
            StampClearRE(qcp, qid) && NestStampRE(r1, code, pcb + 3, e1, pc, qcp)
          else if pc == e1 then StampClearRE(qcp, qid)
          else NestStampOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, qcp));
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
    if pc == pcb {
      assert pc' == pcb + 1 || pc' == pce;
      if pc' == pcb + 1 {
        assert NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc', qcp);
      }
    } else if pc == pcb + 1 {
      assert false;                                 // SetQuantToClock
    } else if pc == pcb + 2 {
      assert pc' == pcb + 3;
      if pc' != e1 {
        NestStampEntryRE(r1, code, pcb + 3, e1, qcp);
      }
      assert NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc', qcp);
    } else if pcb + 3 <= pc < e1 {
      NestStampAdvanceRE(r1, code, pcb + 3, e1, pc, pc', qcp);
      assert NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc', qcp);
    } else if pc == e1 {
      assert pc' == e1 + 1;
      if k - 1 == 0 {
        assert pc' == pce;
      } else {
        NestStampOptEntryRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, qcp);
        NI.NfaRepOptPosRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
        assert NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc', qcp);
      }
    } else {
      NestStampAdvanceOpt(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, pc', qcp);
      if pc' != pce {
        assert NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc', qcp);
      }
    }
  }

  /** Preservation across every step that does not write a quant register:
      either `pc'` lands back inside the block or it is the block exit. */
  lemma NestStampAdvanceRE(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat, pc': nat,
                           qcp: seq<int>)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires pcb <= pc < pce
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires StampEdgeRE(code, pc, pc')
    ensures pc' == pce || (pcb <= pc' < pce && NestStampRE(re, code, pcb, pce, pc', qcp))
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      assert pc == pcb && pce == pcb + 1;
      assert pc' == pc + 1;                          // Consume
    case Re_anchor(_) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      assert pc == pcb && pce == pcb + 1;
      assert pc' == pc + 1;
    case Re_lookaround(lid, la, r1) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      assert pc == pcb && pce == pcb + 1;
      assert pc' == pc + 1;
    case Re_alt(r1, r2) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && (if pc == pcb then true
            else if pcb + 1 <= pc < e1 then NestStampRE(r1, code, pcb + 1, e1, pc, qcp)
            else if pc == e1 then true
            else NestStampRE(r2, code, e1 + 1, pce, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, pce);
      if pc == pcb {
        assert pc' == pcb + 1 || pc' == e1 + 1;
        if pc' == pcb + 1 {
          if pc' != e1 { NestStampEntryRE(r1, code, pcb + 1, e1, qcp); }
          assert NestStampRE(re, code, pcb, pce, pc', qcp);
        } else {
          if pc' != pce {
            NestStampEntryRE(r2, code, e1 + 1, pce, qcp);
            assert NestStampRE(re, code, pcb, pce, pc', qcp);
          }
        }
      } else if pcb + 1 <= pc < e1 {
        NestStampAdvanceRE(r1, code, pcb + 1, e1, pc, pc', qcp);
        assert NestStampRE(re, code, pcb, pce, pc', qcp);
      } else if pc == e1 {
        assert pc' == pce;
      } else {
        NestStampAdvanceRE(r2, code, e1 + 1, pce, pc, pc', qcp);
        if pc' != pce {
          assert NestStampRE(re, code, pcb, pce, pc', qcp);
        }
      }
    case Re_con(r1, r2) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && (if pc < e1 then NestStampRE(r1, code, pcb, e1, pc, qcp)
            else NestStampRE(r2, code, e1, pce, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb, e1);
      NR.NfaRepIncrRE(r2, code, e1, pce);
      if pc < e1 {
        NestStampAdvanceRE(r1, code, pcb, e1, pc, pc', qcp);
        if pc' == e1 {
          if e1 != pce {
            NestStampEntryRE(r2, code, e1, pce, qcp);
            assert NestStampRE(re, code, pcb, pce, pc', qcp);
          }
        } else {
          assert NestStampRE(re, code, pcb, pce, pc', qcp);
        }
      } else {
        NestStampAdvanceRE(r2, code, e1, pce, pc, pc', qcp);
        if pc' != pce {
          assert NestStampRE(re, code, pcb, pce, pc', qcp);
        }
      }
    case Re_quant(nul, qid, q, r1) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      if q.max.Some? {
        assert {:split_here} true;
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid, r1, code, em, pce)
          && (if pc < em then NestStampMinRE(mn, qid, r1, code, pcb, em, pc, qcp)
              else NestStampOptRE(kx, q.greedy, qid, r1, code, em, pce, pc, qcp));
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid, r1, code, em, pce);
        if pc < em {
          NestStampAdvanceMin(mn, qid, r1, code, pcb, em, pc, pc', qcp);
          if pc' == em {
            if em != pce {
              NestStampOptEntryRE(kx, q.greedy, qid, r1, code, em, pce, qcp);
              assert NestStampRE(re, code, pcb, pce, pc', qcp);
            }
          } else {
            assert NestStampRE(re, code, pcb, pce, pc', qcp);
          }
        } else {
          NestStampAdvanceOpt(kx, q.greedy, qid, r1, code, em, pce, pc, pc', qcp);
          if pc' != pce {
            assert NestStampRE(re, code, pcb, pce, pc', qcp);
          }
        }
        return;
      }
      if !(q.min == 0 && q.max == None) && nul != R.NonNullable && !q.greedy {
        assert {:split_here} true;
        // §2.5a GENERIC
        var mn := q.min as nat;
        var em, e1 := NestStampGenREInv(nul, qid, q, r1, code, pcb, pce, pc, qcp);
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          NestStampAdvanceMin(mn, qid, r1, code, pcb, em, pc, pc', qcp);
          NestStampGenREIntro(nul, qid, q, r1, code, pcb, pce, pc', qcp, em, e1);
        } else if pc == em {
          assert pc' == em + 1 || pc' == pce;
          if pc' == em + 1 {
            NestStampGenREIntro(nul, qid, q, r1, code, pcb, pce, pc', qcp, em, e1);
          }
        } else if pc == em + 1 {
          assert false;                              // SetQuantToClock
        } else if pc == em + 2 {
          assert pc' == em + 3;
          if pc' != e1 { NestStampEntryRE(r1, code, em + 3, e1, qcp); }
          NestStampGenREIntro(nul, qid, q, r1, code, pcb, pce, pc', qcp, em, e1);
        } else if em + 3 <= pc < e1 {
          NestStampAdvanceRE(r1, code, em + 3, e1, pc, pc', qcp);
          NestStampGenREIntro(nul, qid, q, r1, code, pcb, pce, pc', qcp, em, e1);
        } else if pc == e1 {
          assert pc' == e1 + 1;
          NestStampGenREIntro(nul, qid, q, r1, code, pcb, pce, pc', qcp, em, e1);
        } else {
          assert pc == e1 + 1 && pc' == em;
          NestStampGenREIntro(nul, qid, q, r1, code, pcb, pce, pc', qcp, em, e1);
        }
        return;
      }
      if !(q.min == 0 && q.max == None) && nul != R.NonNullable {
        assert {:split_here} true;
        // §2.5b CIN-GREEDY
        var mn1 := (q.min - 1) as nat;
        var em, e1 := NestStampCinREInv(nul, qid, q, r1, code, pcb, pce, pc, qcp);
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          NestStampAdvanceMin(mn1, qid, r1, code, pcb, em, pc, pc', qcp);
          NestStampCinREIntro(nul, qid, q, r1, code, pcb, pce, pc', qcp, em, e1);
        } else if pc == em {
          // the head fork: the mark (no claim) or the skip arm to the true
          // stamp site (no claim)
          assert pc' == em + 1 || pc' == e1 + 2;
          NestStampCinREIntro(nul, qid, q, r1, code, pcb, pce, pc', qcp, em, e1);
        } else if pc == em + 1 {
          assert false;                              // SetQuantToClock
        } else if pc == em + 2 {
          assert pc' == em + 3;
          if pc' != e1 { NestStampEntryRE(r1, code, em + 3, e1, qcp); }
          NestStampCinREIntro(nul, qid, q, r1, code, pcb, pce, pc', qcp, em, e1);
        } else if em + 3 <= pc < e1 {
          NestStampAdvanceRE(r1, code, em + 3, e1, pc, pc', qcp);
          NestStampCinREIntro(nul, qid, q, r1, code, pcb, pce, pc', qcp, em, e1);
        } else if pc == e1 {
          assert pc' == e1 + 1;
          NestStampCinREIntro(nul, qid, q, r1, code, pcb, pce, pc', qcp, em, e1);
        } else if pc == e1 + 1 {
          // the end fork: back to the mark (no claim) or out of the block
          assert pc' == em + 1 || pc' == pce;
          if pc' == em + 1 {
            NestStampCinREIntro(nul, qid, q, r1, code, pcb, pce, pc', qcp, em, e1);
          }
        } else {
          assert pc == e1 + 2;
          assert false;                              // SetQuantToClock
        }
        return;
      }
      if !(q.min == 0 && q.max == None) {
        assert {:split_here} true;
        // the NonNullable do-while
        var mn1 := (q.min - 1) as nat;
        var em: nat, e1: nat :|
          NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
          && NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
          && NR.NfaRepRE(r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pce == e1 + 1
          && (if pc < em then NestStampMinRE(mn1, qid, r1, code, pcb, em, pc, qcp)
              else if pc == em then true
              else if em + 1 <= pc < e1 then
                StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 1, e1, pc, qcp)
              else StampClearRE(qcp, qid));
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          NestStampAdvanceMin(mn1, qid, r1, code, pcb, em, pc, pc', qcp);
          assert NestStampRE(re, code, pcb, pce, pc', qcp);
        } else if pc == em {
          assert false;                              // SetQuantToClock
        } else if em + 1 <= pc < e1 {
          NestStampAdvanceRE(r1, code, em + 1, e1, pc, pc', qcp);
          assert NestStampRE(re, code, pcb, pce, pc', qcp);
        } else {
          assert pc == e1;
          assert pc' == em || pc' == e1 + 1;
          if pc' == em {
            assert NestStampRE(re, code, pcb, pce, pc', qcp);
          } else {
            assert pc' == pce;
          }
        }
        return;
      }
      // the star
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
        && pce == e1 + 2
        && (if pc == pcb || pc == pcb + 1 then true
            else if pc == pcb + 2 then StampClearRE(qcp, qid)
            else if pcb + 3 <= pc < e1 then
              StampClearRE(qcp, qid) && NestStampRE(r1, code, pcb + 3, e1, pc, qcp)
            else StampClearRE(qcp, qid));
      NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
      if pc == pcb {
        assert pc' == pcb + 1 || pc' == pce;
        if pc' == pcb + 1 {
          assert NestStampRE(re, code, pcb, pce, pc', qcp);
        }
      } else if pc == pcb + 1 {
        assert false;                                // SetQuantToClock
      } else if pc == pcb + 2 {
        assert pc' == pcb + 3;
        if pc' != e1 { NestStampEntryRE(r1, code, pcb + 3, e1, qcp); }
        assert NestStampRE(re, code, pcb, pce, pc', qcp);
      } else if pcb + 3 <= pc < e1 {
        NestStampAdvanceRE(r1, code, pcb + 3, e1, pc, pc', qcp);
        assert NestStampRE(re, code, pcb, pce, pc', qcp);
      } else if pc == e1 {
        assert pc' == e1 + 1;
        assert NestStampRE(re, code, pcb, pce, pc', qcp);
      } else {
        assert pc == e1 + 1 && pc' == pcb;
        assert NestStampRE(re, code, pcb, pce, pc', qcp);
      }
    case Re_capture(cid, r1) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && (pcb + 1 <= pc < e1 ==> NestStampRE(r1, code, pcb + 1, e1, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      if pc == pcb {
        // the OPEN write falls into the body (or straight onto the close site)
        assert pc' == pcb + 1;
        if pc' != e1 { NestStampEntryRE(r1, code, pcb + 1, e1, qcp); }
        assert NestStampRE(re, code, pcb, pce, pc', qcp);
      } else if pc == e1 {
        assert pc' == e1 + 1 == pce;
      } else {
        assert pcb + 1 <= pc < e1;
        NestStampAdvanceRE(r1, code, pcb + 1, e1, pc, pc', qcp);
        assert NestStampRE(re, code, pcb, pce, pc', qcp);
      }
  }

  /** The top-level advance. */
  lemma NestStampTopAdvance(re: R.regex, code: RB.code, endl: nat, pc: nat, pc': nat, qcp: seq<int>)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires pc < endl
    requires NestStampTopRE(re, code, endl, pc, qcp)
    requires StampEdgeRE(code, pc, pc')
    ensures pc' <= endl && NestStampTopRE(re, code, endl, pc', qcp)
  {
    NestStampAdvanceRE(re, code, 0, endl, pc, pc', qcp);
  }

  // =========================================================================
  // 6. Preservation across a QUANT-REGISTER write, `SetQuantToClock(qid0, b)`.
  //    Both stamps fall through to `pc + 1`. The mark (`b == false`) clears
  //    `qid0`, which is exactly what the post-mark sites claim; the true stamp
  //    (`b == true`, only in a CIN-greedy loop) sets it and EXITS the block, so
  //    no site inside `qid0`'s own block claims anything about it any more —
  //    and every enclosing claim is about a DIFFERENT quantifier
  //    (`QuantUnique`), hence untouched.
  // =========================================================================

  lemma NestStampQuantWriteMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat,
                               pc: nat, qcp: seq<int>, qcp': seq<int>, qid0: R.quantid, b: bool)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    requires PIV.QuantUnique(r1) && qid >= 0 && (qid as nat) !in PIV.QuantIds(r1)
    requires pcb <= pc < pce
    requires NestStampMinRE(k, qid, r1, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, b))
    requires qid0 >= 0
    requires forall kk: int :: kk != qid0 ==> AI.get_idx(qcp', kk) == AI.get_idx(qcp, kk)
    requires !b ==> AI.get_idx(qcp', qid0) < 0
    ensures pc + 1 == pce || (pcb <= pc + 1 < pce && NestStampMinRE(k, qid, r1, code, pcb, pce, pc + 1, qcp'))
    ensures (qid0 as nat) in PIV.QuantIds(r1) || qid0 == qid
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce)
      && (if pc == pcb then true
          else StampClearRE(qcp, qid)
               && (if pc < e1 then NestStampRE(r1, code, pcb + 1, e1, pc, qcp)
                   else NestStampMinRE(k - 1, qid, r1, code, e1, pce, pc, qcp)));
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, pce);
    if pc == pcb {
      // THE CHAIN'S OWN MARK: qid0 == qid, cleared.
      assert qid0 == qid && !b;
      assert AI.get_idx(qcp', qid) < 0;
      if pc + 1 != pce {
        if pc + 1 < e1 {
          NestStampEntryRE(r1, code, pcb + 1, e1, qcp');
        } else {
          assert pc + 1 == e1;
          NestStampMinEntryRE(k - 1, qid, r1, code, e1, pce, qcp');
        }
        assert NestStampMinRE(k, qid, r1, code, pcb, pce, pc + 1, qcp');
      }
    } else if pc < e1 {
      NestStampQuantWriteRE(r1, code, pcb + 1, e1, pc, qcp, qcp', qid0, b);
      assert (qid0 as nat) in PIV.QuantIds(r1);
      assert qid0 != qid;
      assert StampClearRE(qcp', qid);
      if pc + 1 == e1 {
        if k - 1 == 0 {
          assert pc + 1 == pce;
        } else {
          NestStampMinEntryRE(k - 1, qid, r1, code, e1, pce, qcp');
          NI.NfaRepMinPosRE(k - 1, qid, r1, code, e1, pce);
          assert NestStampMinRE(k, qid, r1, code, pcb, pce, pc + 1, qcp');
        }
      } else {
        assert NestStampMinRE(k, qid, r1, code, pcb, pce, pc + 1, qcp');
      }
    } else {
      NestStampQuantWriteMin(k - 1, qid, r1, code, e1, pce, pc, qcp, qcp', qid0, b);
      if pc + 1 != pce {
        assert StampClearRE(qcp', qid) by {
          if qid0 == qid { assert !b || AI.get_idx(qcp', qid) < 0; }
        }
        assert NestStampMinRE(k, qid, r1, code, pcb, pce, pc + 1, qcp');
      }
    }
  }

  lemma NestStampQuantWriteOpt(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                               pcb: nat, pce: nat, pc: nat, qcp: seq<int>, qcp': seq<int>,
                               qid0: R.quantid, b: bool)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    requires PIV.QuantUnique(r1) && qid >= 0 && (qid as nat) !in PIV.QuantIds(r1)
    requires pcb <= pc < pce
    requires NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, b))
    requires qid0 >= 0
    requires forall kk: int :: kk != qid0 ==> AI.get_idx(qcp', kk) == AI.get_idx(qcp, kk)
    requires !b ==> AI.get_idx(qcp', qid0) < 0
    ensures pc + 1 == pce || (pcb <= pc + 1 < pce && NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc + 1, qcp'))
    ensures (qid0 as nat) in PIV.QuantIds(r1) || qid0 == qid
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, pcb + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce)
      && (if pc == pcb || pc == pcb + 1 then true
          else if pc == pcb + 2 then StampClearRE(qcp, qid)
          else if pcb + 3 <= pc < e1 then
            StampClearRE(qcp, qid) && NestStampRE(r1, code, pcb + 3, e1, pc, qcp)
          else if pc == e1 then StampClearRE(qcp, qid)
          else NestStampOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, qcp));
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
    if pc == pcb {
      assert false;                                  // the layer fork
    } else if pc == pcb + 1 {
      // THIS LAYER'S MARK
      assert qid0 == qid && !b;
      assert AI.get_idx(qcp', qid) < 0;
      assert NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc + 1, qcp');
    } else if pc == pcb + 2 {
      assert false;                                  // BeginLoop
    } else if pcb + 3 <= pc < e1 {
      NestStampQuantWriteRE(r1, code, pcb + 3, e1, pc, qcp, qcp', qid0, b);
      assert (qid0 as nat) in PIV.QuantIds(r1);
      assert qid0 != qid;
      assert NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc + 1, qcp');
    } else if pc == e1 {
      assert false;                                  // EndLoop
    } else {
      NestStampQuantWriteOpt(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, qcp, qcp', qid0, b);
      if pc + 1 != pce {
        assert NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc + 1, qcp');
      }
    }
  }

  /** THE QUANT-WRITE STEP. */
  lemma NestStampQuantWriteRE(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                              qcp: seq<int>, qcp': seq<int>, qid0: R.quantid, b: bool)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, b))
    requires qid0 >= 0
    requires forall kk: int :: kk != qid0 ==> AI.get_idx(qcp', kk) == AI.get_idx(qcp, kk)
    requires !b ==> AI.get_idx(qcp', qid0) < 0
    ensures pc + 1 == pce || (pcb <= pc + 1 < pce && NestStampRE(re, code, pcb, pce, pc + 1, qcp'))
    ensures (qid0 as nat) in PIV.QuantIds(re)
    decreases CP.rsize(re), 2
  {
    match re
    case Re_empty =>
      assert {:split_here} true;   // (2026-11-05) the pack OOM: this refutation searched the whole context
      NR.NfaRepIncrRE(re, code, pcb, pce);
      assert false;
    case Re_character(ch) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      assert false;                                  // Consume
    case Re_anchor(_) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      assert false;                                  // AnchorAssertion
    case Re_lookaround(lid, la, r1) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      assert false;                                  // CheckOracle / NegCheckOracle
    case Re_alt(r1, r2) =>
      QuantWriteAlt(re, code, pcb, pce, pc, qcp, qcp', qid0, b, r1, r2);
    case Re_con(r1, r2) =>
      QuantWriteCon(re, code, pcb, pce, pc, qcp, qcp', qid0, b, r1, r2);
    case Re_capture(cid, r1) =>
      QuantWriteCap(re, code, pcb, pce, pc, qcp, qcp', qid0, b, cid, r1);
    case Re_quant(nul, qid, q, r1) =>
      QuantWriteQuant(re, code, pcb, pce, pc, qcp, qcp', qid0, b, nul, qid, q, r1);
  }

  /** (2026-11-05) The `Re_alt` arm of `NestStampQuantWriteRE`, as its own lemma:
      in one VC with the other arms its batch passed the 24 GB slice (one worker). */
  lemma QuantWriteAlt(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                              qcp: seq<int>, qcp': seq<int>, qid0: R.quantid, b: bool,
                              r1: R.regex, r2: R.regex)
    requires re == R.Re_alt(r1, r2)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, b))
    requires qid0 >= 0
    requires forall kk: int :: kk != qid0 ==> AI.get_idx(qcp', kk) == AI.get_idx(qcp, kk)
    requires !b ==> AI.get_idx(qcp', qid0) < 0
    ensures pc + 1 == pce || (pcb <= pc + 1 < pce && NestStampRE(re, code, pcb, pce, pc + 1, qcp'))
    ensures (qid0 as nat) in PIV.QuantIds(re)
    decreases CP.rsize(re), 1
  {
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && (if pc == pcb then true
            else if pcb + 1 <= pc < e1 then NestStampRE(r1, code, pcb + 1, e1, pc, qcp)
            else if pc == e1 then true
            else NestStampRE(r2, code, e1 + 1, pce, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, pce);
      if pc == pcb || pc == e1 {
        assert false;
      } else if pcb + 1 <= pc < e1 {
        NestStampQuantWriteRE(r1, code, pcb + 1, e1, pc, qcp, qcp', qid0, b);
        assert NestStampRE(re, code, pcb, pce, pc + 1, qcp');
      } else {
        NestStampQuantWriteRE(r2, code, e1 + 1, pce, pc, qcp, qcp', qid0, b);
        if pc + 1 != pce {
          assert NestStampRE(re, code, pcb, pce, pc + 1, qcp');
        }
      }
  }

  /** (2026-11-05) The `Re_con` arm of `NestStampQuantWriteRE`, as its own lemma:
      in one VC with the other arms its batch passed the 24 GB slice (one worker). */
  lemma QuantWriteCon(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                              qcp: seq<int>, qcp': seq<int>, qid0: R.quantid, b: bool,
                              r1: R.regex, r2: R.regex)
    requires re == R.Re_con(r1, r2)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, b))
    requires qid0 >= 0
    requires forall kk: int :: kk != qid0 ==> AI.get_idx(qcp', kk) == AI.get_idx(qcp, kk)
    requires !b ==> AI.get_idx(qcp', qid0) < 0
    ensures pc + 1 == pce || (pcb <= pc + 1 < pce && NestStampRE(re, code, pcb, pce, pc + 1, qcp'))
    ensures (qid0 as nat) in PIV.QuantIds(re)
    decreases CP.rsize(re), 1
  {
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && (if pc < e1 then NestStampRE(r1, code, pcb, e1, pc, qcp)
            else NestStampRE(r2, code, e1, pce, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb, e1);
      NR.NfaRepIncrRE(r2, code, e1, pce);
      if pc < e1 {
        NestStampQuantWriteRE(r1, code, pcb, e1, pc, qcp, qcp', qid0, b);
        if pc + 1 == e1 {
          if e1 != pce {
            NestStampEntryRE(r2, code, e1, pce, qcp');
            assert NestStampRE(re, code, pcb, pce, pc + 1, qcp');
          }
        } else {
          assert NestStampRE(re, code, pcb, pce, pc + 1, qcp');
        }
      } else {
        NestStampQuantWriteRE(r2, code, e1, pce, pc, qcp, qcp', qid0, b);
        if pc + 1 != pce {
          assert NestStampRE(re, code, pcb, pce, pc + 1, qcp');
        }
      }
  }

  /** (2026-11-05) The `Re_capture` arm of `NestStampQuantWriteRE`, as its own lemma:
      in one VC with the other arms its batch passed the 24 GB slice (one worker). */
  lemma QuantWriteCap(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                              qcp: seq<int>, qcp': seq<int>, qid0: R.quantid, b: bool,
                              cid: int, r1: R.regex)
    requires re == R.Re_capture(cid, r1)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, b))
    requires qid0 >= 0
    requires forall kk: int :: kk != qid0 ==> AI.get_idx(qcp', kk) == AI.get_idx(qcp, kk)
    requires !b ==> AI.get_idx(qcp', qid0) < 0
    ensures pc + 1 == pce || (pcb <= pc + 1 < pce && NestStampRE(re, code, pcb, pce, pc + 1, qcp'))
    ensures (qid0 as nat) in PIV.QuantIds(re)
    decreases CP.rsize(re), 1
  {
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && (pcb + 1 <= pc < e1 ==> NestStampRE(r1, code, pcb + 1, e1, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      if pc == pcb || pc == e1 {
        assert false;                                // SetRegisterToCP
      } else {
        NestStampQuantWriteRE(r1, code, pcb + 1, e1, pc, qcp, qcp', qid0, b);
        assert NestStampRE(re, code, pcb, pce, pc + 1, qcp');
      }
  }

  /** (2026-11-05) The `Re_quant` arm of `NestStampQuantWriteRE`, as its own lemma:
      in one VC with the other arms its batch passed the 24 GB slice (one worker). */
  lemma QuantWriteQuant(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                              qcp: seq<int>, qcp': seq<int>, qid0: R.quantid, b: bool,
                              nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, r1: R.regex)
    requires re == R.Re_quant(nul, qid, q, r1)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, b))
    requires qid0 >= 0
    requires forall kk: int :: kk != qid0 ==> AI.get_idx(qcp', kk) == AI.get_idx(qcp, kk)
    requires !b ==> AI.get_idx(qcp', qid0) < 0
    ensures pc + 1 == pce || (pcb <= pc + 1 < pce && NestStampRE(re, code, pcb, pce, pc + 1, qcp'))
    ensures (qid0 as nat) in PIV.QuantIds(re)
    decreases CP.rsize(re), 1
  {
    assert qid >= 0;                               // QuantUnique
    if q.max.Some? { QWQBounded(re, code, pcb, pce, pc, qcp, qcp', qid0, b, nul, qid, q, r1); }
    else if !(q.min == 0 && q.max == None) && nul != R.NonNullable && !q.greedy { QWQGen(re, code, pcb, pce, pc, qcp, qcp', qid0, b, nul, qid, q, r1); }
    else if !(q.min == 0 && q.max == None) && nul != R.NonNullable { QWQCin(re, code, pcb, pce, pc, qcp, qcp', qid0, b, nul, qid, q, r1); }
    else if !(q.min == 0 && q.max == None) { QWQNonNull(re, code, pcb, pce, pc, qcp, qcp', qid0, b, nul, qid, q, r1); }
    else { QWQStar(re, code, pcb, pce, pc, qcp, qcp', qid0, b, nul, qid, q, r1); }
  }

  lemma QWQBounded(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                              qcp: seq<int>, qcp': seq<int>, qid0: R.quantid, b: bool,
                              nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, r1: R.regex)
    requires re == R.Re_quant(nul, qid, q, r1)
    requires q.max.Some?
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, b))
    requires qid0 >= 0
    requires forall kk: int :: kk != qid0 ==> AI.get_idx(qcp', kk) == AI.get_idx(qcp, kk)
    requires !b ==> AI.get_idx(qcp', qid0) < 0
    ensures pc + 1 == pce || (pcb <= pc + 1 < pce && NestStampRE(re, code, pcb, pce, pc + 1, qcp'))
    ensures (qid0 as nat) in PIV.QuantIds(re)
    decreases CP.rsize(re), 0
  {
      assert qid >= 0;                               // QuantUnique
      assert (qid as nat) !in PIV.QuantIds(r1);       // QuantUnique
      assert {:split_here} true;
      var mn := q.min as nat;
      var kx := (q.max.value - q.min) as nat;
      var em: nat :| NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
        && NR.NfaRepOptRE(kx, q.greedy, qid, r1, code, em, pce)
        && (if pc < em then NestStampMinRE(mn, qid, r1, code, pcb, em, pc, qcp)
            else NestStampOptRE(kx, q.greedy, qid, r1, code, em, pce, pc, qcp));
      NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
      NR.NfaRepIncrOptRE(kx, q.greedy, qid, r1, code, em, pce);
      if pc < em {
        NestStampQuantWriteMin(mn, qid, r1, code, pcb, em, pc, qcp, qcp', qid0, b);
        if pc + 1 == em {
          if em != pce {
            NestStampOptEntryRE(kx, q.greedy, qid, r1, code, em, pce, qcp');
            assert NestStampRE(re, code, pcb, pce, pc + 1, qcp');
          }
        } else {
          assert NestStampRE(re, code, pcb, pce, pc + 1, qcp');
        }
      } else {
        NestStampQuantWriteOpt(kx, q.greedy, qid, r1, code, em, pce, pc, qcp, qcp', qid0, b);
        if pc + 1 != pce {
          assert NestStampRE(re, code, pcb, pce, pc + 1, qcp');
        }
      }
  }

  lemma QWQGen(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                              qcp: seq<int>, qcp': seq<int>, qid0: R.quantid, b: bool,
                              nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, r1: R.regex)
    requires re == R.Re_quant(nul, qid, q, r1)
    requires !q.max.Some? && !(q.min == 0 && q.max == None) && nul != R.NonNullable && !q.greedy
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, b))
    requires qid0 >= 0
    requires forall kk: int :: kk != qid0 ==> AI.get_idx(qcp', kk) == AI.get_idx(qcp, kk)
    requires !b ==> AI.get_idx(qcp', qid0) < 0
    ensures pc + 1 == pce || (pcb <= pc + 1 < pce && NestStampRE(re, code, pcb, pce, pc + 1, qcp'))
    ensures (qid0 as nat) in PIV.QuantIds(re)
    decreases CP.rsize(re), 0
  {
      assert qid >= 0;                               // QuantUnique
      assert (qid as nat) !in PIV.QuantIds(r1);       // QuantUnique
      assert {:split_here} true;
      // §2.5a GENERIC
      var mn := q.min as nat;
      var em, e1 := NestStampGenREInv(nul, qid, q, r1, code, pcb, pce, pc, qcp);
      NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
      NR.NfaRepIncrRE(r1, code, em + 3, e1);
      if pc < em {
        NestStampQuantWriteMin(mn, qid, r1, code, pcb, em, pc, qcp, qcp', qid0, b);
        NestStampGenREIntro(nul, qid, q, r1, code, pcb, pce, pc + 1, qcp', em, e1);
      } else if pc == em {
        assert false;                              // the loop fork
      } else if pc == em + 1 {
        // THE LOOP'S MARK
        assert qid0 == qid && !b;
        NestStampGenREIntro(nul, qid, q, r1, code, pcb, pce, pc + 1, qcp', em, e1);
      } else if pc == em + 2 {
        assert false;                              // BeginLoop
      } else if em + 3 <= pc < e1 {
        NestStampQuantWriteRE(r1, code, em + 3, e1, pc, qcp, qcp', qid0, b);
        assert qid0 != qid;
        NestStampGenREIntro(nul, qid, q, r1, code, pcb, pce, pc + 1, qcp', em, e1);
      } else {
        assert pc == e1 || pc == e1 + 1;
        assert false;                              // EndLoop / back-Jmp
      }
  }

  lemma QWQCin(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                              qcp: seq<int>, qcp': seq<int>, qid0: R.quantid, b: bool,
                              nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, r1: R.regex)
    requires re == R.Re_quant(nul, qid, q, r1)
    requires !q.max.Some? && !(q.min == 0 && q.max == None) && nul != R.NonNullable && q.greedy
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, b))
    requires qid0 >= 0
    requires forall kk: int :: kk != qid0 ==> AI.get_idx(qcp', kk) == AI.get_idx(qcp, kk)
    requires !b ==> AI.get_idx(qcp', qid0) < 0
    ensures pc + 1 == pce || (pcb <= pc + 1 < pce && NestStampRE(re, code, pcb, pce, pc + 1, qcp'))
    ensures (qid0 as nat) in PIV.QuantIds(re)
    decreases CP.rsize(re), 0
  {
      assert qid >= 0;                               // QuantUnique
      assert (qid as nat) !in PIV.QuantIds(r1);       // QuantUnique
      assert {:split_here} true;
      // §2.5b CIN-GREEDY
      var mn1 := (q.min - 1) as nat;
      var em, e1 := NestStampCinREInv(nul, qid, q, r1, code, pcb, pce, pc, qcp);
      NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
      NR.NfaRepIncrRE(r1, code, em + 3, e1);
      if pc < em {
        NestStampQuantWriteMin(mn1, qid, r1, code, pcb, em, pc, qcp, qcp', qid0, b);
        NestStampCinREIntro(nul, qid, q, r1, code, pcb, pce, pc + 1, qcp', em, e1);
      } else if pc == em {
        assert false;                              // the head fork
      } else if pc == em + 1 {
        // THE LOOP'S MARK
        assert qid0 == qid && !b;
        NestStampCinREIntro(nul, qid, q, r1, code, pcb, pce, pc + 1, qcp', em, e1);
      } else if pc == em + 2 {
        assert false;                              // BeginLoop
      } else if em + 3 <= pc < e1 {
        NestStampQuantWriteRE(r1, code, em + 3, e1, pc, qcp, qcp', qid0, b);
        assert qid0 != qid;
        NestStampCinREIntro(nul, qid, q, r1, code, pcb, pce, pc + 1, qcp', em, e1);
      } else if pc == e1 || pc == e1 + 1 {
        assert false;                              // EndLoop / the end fork
      } else {
        // THE TRUE STAMP at e1 + 2: it exits the block.
        assert pc == e1 + 2;
        assert qid0 == qid;
        assert pc + 1 == pce;
      }
  }

  lemma QWQNonNull(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                              qcp: seq<int>, qcp': seq<int>, qid0: R.quantid, b: bool,
                              nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, r1: R.regex)
    requires re == R.Re_quant(nul, qid, q, r1)
    requires !q.max.Some? && !(q.min == 0 && q.max == None) && nul == R.NonNullable
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, b))
    requires qid0 >= 0
    requires forall kk: int :: kk != qid0 ==> AI.get_idx(qcp', kk) == AI.get_idx(qcp, kk)
    requires !b ==> AI.get_idx(qcp', qid0) < 0
    ensures pc + 1 == pce || (pcb <= pc + 1 < pce && NestStampRE(re, code, pcb, pce, pc + 1, qcp'))
    ensures (qid0 as nat) in PIV.QuantIds(re)
    decreases CP.rsize(re), 0
  {
      assert qid >= 0;                               // QuantUnique
      assert (qid as nat) !in PIV.QuantIds(r1);       // QuantUnique
      assert {:split_here} true;
      // the NonNullable do-while
      var mn1 := (q.min - 1) as nat;
      var em: nat, e1: nat :|
        NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
        && NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
        && NR.NfaRepRE(r1, code, em + 1, e1)
        && NR.GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
        && pce == e1 + 1
        && (if pc < em then NestStampMinRE(mn1, qid, r1, code, pcb, em, pc, qcp)
            else if pc == em then true
            else if em + 1 <= pc < e1 then
              StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 1, e1, pc, qcp)
            else StampClearRE(qcp, qid));
      NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
      NR.NfaRepIncrRE(r1, code, em + 1, e1);
      if pc < em {
        NestStampQuantWriteMin(mn1, qid, r1, code, pcb, em, pc, qcp, qcp', qid0, b);
        assert NestStampRE(re, code, pcb, pce, pc + 1, qcp');
      } else if pc == em {
        // THE LAST MARK
        assert qid0 == qid && !b;
        if pc + 1 != e1 {
          NestStampEntryRE(r1, code, em + 1, e1, qcp');
        }
        assert NestStampRE(re, code, pcb, pce, pc + 1, qcp');
      } else if em + 1 <= pc < e1 {
        NestStampQuantWriteRE(r1, code, em + 1, e1, pc, qcp, qcp', qid0, b);
        assert qid0 != qid;
        assert NestStampRE(re, code, pcb, pce, pc + 1, qcp');
      } else {
        assert pc == e1;
        assert false;                              // the backward fork
      }
  }

  lemma QWQStar(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                              qcp: seq<int>, qcp': seq<int>, qid0: R.quantid, b: bool,
                              nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, r1: R.regex)
    requires re == R.Re_quant(nul, qid, q, r1)
    requires !q.max.Some? && q.min == 0 && q.max == None
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, b))
    requires qid0 >= 0
    requires forall kk: int :: kk != qid0 ==> AI.get_idx(qcp', kk) == AI.get_idx(qcp, kk)
    requires !b ==> AI.get_idx(qcp', qid0) < 0
    ensures pc + 1 == pce || (pcb <= pc + 1 < pce && NestStampRE(re, code, pcb, pce, pc + 1, qcp'))
    ensures (qid0 as nat) in PIV.QuantIds(re)
    decreases CP.rsize(re), 0
  {
      assert qid >= 0;                               // QuantUnique
      assert (qid as nat) !in PIV.QuantIds(r1);       // QuantUnique
      // the star
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
        && pce == e1 + 2
        && (if pc == pcb || pc == pcb + 1 then true
            else if pc == pcb + 2 then StampClearRE(qcp, qid)
            else if pcb + 3 <= pc < e1 then
              StampClearRE(qcp, qid) && NestStampRE(r1, code, pcb + 3, e1, pc, qcp)
            else StampClearRE(qcp, qid));
      NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
      if pc == pcb {
        assert false;                                // the fork
      } else if pc == pcb + 1 {
        // THE STAR'S MARK
        assert qid0 == qid && !b;
        assert NestStampRE(re, code, pcb, pce, pc + 1, qcp');
      } else if pc == pcb + 2 {
        assert false;                                // BeginLoop
      } else if pcb + 3 <= pc < e1 {
        NestStampQuantWriteRE(r1, code, pcb + 3, e1, pc, qcp, qcp', qid0, b);
        assert qid0 != qid;
        assert NestStampRE(re, code, pcb, pce, pc + 1, qcp');
      } else {
        assert pc == e1 || pc == e1 + 1;
        assert false;                                // EndLoop / back-Jmp
      }
  }



  /** The top-level quant-write step. */
  lemma NestStampTopQuantWrite(re: R.regex, code: RB.code, endl: nat, pc: nat,
                               qcp: seq<int>, qcp': seq<int>, qid0: R.quantid, b: bool)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires PIV.QuantUnique(re)
    requires pc < endl
    requires NestStampTopRE(re, code, endl, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, b))
    requires qid0 >= 0
    requires forall kk: int :: kk != qid0 ==> AI.get_idx(qcp', kk) == AI.get_idx(qcp, kk)
    requires !b ==> AI.get_idx(qcp', qid0) < 0
    ensures pc + 1 <= endl && NestStampTopRE(re, code, endl, pc + 1, qcp')
    ensures (qid0 as nat) in PIV.QuantIds(re)
  {
    NestStampQuantWriteRE(re, code, 0, endl, pc, qcp, qcp', qid0, b);
  }

  // =========================================================================
  // 7. THE PAYOFF: a capture write never lands inside a STAMPED quantifier's
  //    body. Every open/close site is past its enclosing quantifiers' clock
  //    marks, and a mark clears the stamp; the sites where a stale stamp can
  //    survive (head fork, mark, true stamp) carry no capture write.
  // =========================================================================

  lemma NestStampOpenSiteMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat,
                             pc: nat, qcp: seq<int>, gid: nat)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    requires PIV.CapUnique(r1) && PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    requires NestStampMinRE(k, qid, r1, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid)))
    ensures gid in PIV.CapIds(r1)
    ensures StampClearRE(qcp, qid)
    ensures forall A: nat :: A in PIV.QuantIds(r1) && AI.get_idx(qcp, A) >= 0
              ==> gid !in PIV.CapIds(PIV.QidBody(r1, A))
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce)
      && (if pc == pcb then true
          else StampClearRE(qcp, qid)
               && (if pc < e1 then NestStampRE(r1, code, pcb + 1, e1, pc, qcp)
                   else NestStampMinRE(k - 1, qid, r1, code, e1, pce, pc, qcp)));
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, pce);
    if pc == pcb {
      assert {:split_here} true;
      assert false;                                  // SetQuantToClock
    } else if pc < e1 {
      assert {:split_here} true;
      NestStampOpenSiteRE(r1, code, pcb + 1, e1, pc, qcp, gid);
    } else {
      assert {:split_here} true;
      NestStampOpenSiteMin(k - 1, qid, r1, code, e1, pce, pc, qcp, gid);
    }
  }

  lemma NestStampOpenSiteOpt(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                             pcb: nat, pce: nat, pc: nat, qcp: seq<int>, gid: nat)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    requires PIV.CapUnique(r1) && PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    requires NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid)))
    ensures gid in PIV.CapIds(r1)
    ensures StampClearRE(qcp, qid)
    ensures forall A: nat :: A in PIV.QuantIds(r1) && AI.get_idx(qcp, A) >= 0
              ==> gid !in PIV.CapIds(PIV.QidBody(r1, A))
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, pcb + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce)
      && (if pc == pcb || pc == pcb + 1 then true
          else if pc == pcb + 2 then StampClearRE(qcp, qid)
          else if pcb + 3 <= pc < e1 then
            StampClearRE(qcp, qid) && NestStampRE(r1, code, pcb + 3, e1, pc, qcp)
          else if pc == e1 then StampClearRE(qcp, qid)
          else NestStampOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, qcp));
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
    // (2026-09-04) refutation branch FIRST and one batch per branch: the
    // three-way split in one VC took 15 min.
    if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 {
      assert {:split_here} true;
      assert false;                                  // Fork / stamp / BeginLoop / EndLoop
    } else if pcb + 3 <= pc < e1 {
      assert {:split_here} true;
      NestStampOpenSiteRE(r1, code, pcb + 3, e1, pc, qcp, gid);
    } else {
      assert {:split_here} true;
      NestStampOpenSiteOpt(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, qcp, gid);
    }
  }

  /** A capture OPEN site is inside `re` and outside the body of every
      STAMPED quantifier of `re`. */
  lemma NestStampOpenSiteRE(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                            qcp: seq<int>, gid: nat)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid)))
    ensures gid in PIV.CapIds(re)
    ensures forall A: nat :: A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
              ==> gid !in PIV.CapIds(PIV.QidBody(re, A))
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
      NR.NfaRepIncrRE(re, code, pcb, pce);
      assert false;
    case Re_character(ch) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      assert pc == pcb;
      assert false;                                  // Consume
    case Re_anchor(_) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      assert pc == pcb;
      assert false;                                  // AnchorAssertion
    case Re_lookaround(lid, la, r1) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      assert pc == pcb;
      assert false;                                  // CheckOracle / NegCheckOracle
    case Re_alt(r1, r2) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && (if pc == pcb then true
            else if pcb + 1 <= pc < e1 then NestStampRE(r1, code, pcb + 1, e1, pc, qcp)
            else if pc == e1 then true
            else NestStampRE(r2, code, e1 + 1, pce, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, pce);
      if pc == pcb || pc == e1 {
        assert false;                                // Fork / Jmp
      } else if pcb + 1 <= pc < e1 {
        NestStampOpenSiteRE(r1, code, pcb + 1, e1, pc, qcp, gid);
        NestStampSplitAlt(re, r1, r2, qcp, gid, true);
      } else {
        NestStampOpenSiteRE(r2, code, e1 + 1, pce, pc, qcp, gid);
        NestStampSplitAlt(re, r1, r2, qcp, gid, false);
      }
    case Re_con(r1, r2) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && (if pc < e1 then NestStampRE(r1, code, pcb, e1, pc, qcp)
            else NestStampRE(r2, code, e1, pce, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb, e1);
      NR.NfaRepIncrRE(r2, code, e1, pce);
      if pc < e1 {
        NestStampOpenSiteRE(r1, code, pcb, e1, pc, qcp, gid);
        NestStampSplitAlt(re, r1, r2, qcp, gid, true);
      } else {
        NestStampOpenSiteRE(r2, code, e1, pce, pc, qcp, gid);
        NestStampSplitAlt(re, r1, r2, qcp, gid, false);
      }
    case Re_capture(cid, r1) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && (pcb + 1 <= pc < e1 ==> NestStampRE(r1, code, pcb + 1, e1, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      assert cid >= 0;                               // CapUnique
      assert PIV.QuantIds(re) == PIV.QuantIds(r1);
      if pc == pcb {
        assert CP.start_reg(cid) == CP.start_reg(gid);
        assert cid == gid;
        assert gid in PIV.CapIds(re);
        forall A: nat | A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
          ensures gid !in PIV.CapIds(PIV.QidBody(re, A)) {
          assert PIV.QidBody(re, A) == PIV.QidBody(r1, A);
          PIV.CapIdsQidBodySubset(r1, A);
          assert gid !in PIV.CapIds(r1);             // CapUnique: cid is fresh for r1
        }
      } else if pc == e1 {
        assert CP.end_reg(cid) == CP.start_reg(gid);
        assert false;                                // parity
      } else {
        NestStampOpenSiteRE(r1, code, pcb + 1, e1, pc, qcp, gid);
        forall A: nat | A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
          ensures gid !in PIV.CapIds(PIV.QidBody(re, A)) {
          assert PIV.QidBody(re, A) == PIV.QidBody(r1, A);
        }
      }
    case Re_quant(nul, qid, q, r1) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      assert qid >= 0;                               // QuantUnique
      assert (qid as nat) !in PIV.QuantIds(r1);      // QuantUnique
      assert PIV.QidBody(re, qid as nat) == r1;
      var stamped := StampClearRE(qcp, qid);
      if q.max.Some? {
        assert {:split_here} true;
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid, r1, code, em, pce)
          && (if pc < em then NestStampMinRE(mn, qid, r1, code, pcb, em, pc, qcp)
              else NestStampOptRE(kx, q.greedy, qid, r1, code, em, pce, pc, qcp));
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid, r1, code, em, pce);
        if pc < em {
          NestStampOpenSiteMin(mn, qid, r1, code, pcb, em, pc, qcp, gid);
        } else {
          NestStampOpenSiteOpt(kx, q.greedy, qid, r1, code, em, pce, pc, qcp, gid);
        }
        NestStampQuantIds(re, nul, qid, q, r1, qcp, gid);
        return;
      }
      if !(q.min == 0 && q.max == None) && nul != R.NonNullable && !q.greedy {
        assert {:split_here} true;
        var mn := q.min as nat;
        var em, e1 := NestStampGenREInv(nul, qid, q, r1, code, pcb, pce, pc, qcp);
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          NestStampOpenSiteMin(mn, qid, r1, code, pcb, em, pc, qcp, gid);
        } else if em + 3 <= pc < e1 {
          NestStampOpenSiteRE(r1, code, em + 3, e1, pc, qcp, gid);
        } else {
          assert false;                              // Fork/stamp/BeginLoop/EndLoop/Jmp
        }
        NestStampQuantIds(re, nul, qid, q, r1, qcp, gid);
        return;
      }
      if !(q.min == 0 && q.max == None) && nul != R.NonNullable {
        assert {:split_here} true;
        var mn1 := (q.min - 1) as nat;
        var em, e1 := NestStampCinREInv(nul, qid, q, r1, code, pcb, pce, pc, qcp);
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          NestStampOpenSiteMin(mn1, qid, r1, code, pcb, em, pc, qcp, gid);
        } else if em + 3 <= pc < e1 {
          NestStampOpenSiteRE(r1, code, em + 3, e1, pc, qcp, gid);
        } else {
          assert false;                              // the loop's own instructions
        }
        NestStampQuantIds(re, nul, qid, q, r1, qcp, gid);
        return;
      }
      if !(q.min == 0 && q.max == None) {
        assert {:split_here} true;
        var mn1 := (q.min - 1) as nat;
        var em: nat, e1: nat :|
          NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
          && NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
          && NR.NfaRepRE(r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pce == e1 + 1
          && (if pc < em then NestStampMinRE(mn1, qid, r1, code, pcb, em, pc, qcp)
              else if pc == em then true
              else if em + 1 <= pc < e1 then
                StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 1, e1, pc, qcp)
              else StampClearRE(qcp, qid));
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          NestStampOpenSiteMin(mn1, qid, r1, code, pcb, em, pc, qcp, gid);
        } else if em + 1 <= pc < e1 {
          NestStampOpenSiteRE(r1, code, em + 1, e1, pc, qcp, gid);
        } else {
          assert false;                              // the mark / the backward fork
        }
        NestStampQuantIds(re, nul, qid, q, r1, qcp, gid);
        return;
      }
      // the star
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
        && pce == e1 + 2
        && (if pc == pcb || pc == pcb + 1 then true
            else if pc == pcb + 2 then StampClearRE(qcp, qid)
            else if pcb + 3 <= pc < e1 then
              StampClearRE(qcp, qid) && NestStampRE(r1, code, pcb + 3, e1, pc, qcp)
            else StampClearRE(qcp, qid));
      NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
      if pcb + 3 <= pc < e1 {
        NestStampOpenSiteRE(r1, code, pcb + 3, e1, pc, qcp, gid);
      } else {
        assert false;                                // the loop's own instructions
      }
      NestStampQuantIds(re, nul, qid, q, r1, qcp, gid);
  }

  // =========================================================================
  // 7b. (2026-11-04) The same for ANY capture write — open or close. A copy
  //     of the open-site family with the register left generic; the capture
  //     arm accepts both of its own registers.
  // =========================================================================

  lemma NestStampCapSiteMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat,
                             pc: nat, qcp: seq<int>, gid: nat, reg: int)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    requires PIV.CapUnique(r1) && PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    requires NestStampMinRE(k, qid, r1, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(reg))
    requires reg == CP.start_reg(gid) || reg == CP.end_reg(gid)
    ensures gid in PIV.CapIds(r1)
    ensures StampClearRE(qcp, qid)
    ensures forall A: nat :: A in PIV.QuantIds(r1) && AI.get_idx(qcp, A) >= 0
              ==> gid !in PIV.CapIds(PIV.QidBody(r1, A))
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce)
      && (if pc == pcb then true
          else StampClearRE(qcp, qid)
               && (if pc < e1 then NestStampRE(r1, code, pcb + 1, e1, pc, qcp)
                   else NestStampMinRE(k - 1, qid, r1, code, e1, pce, pc, qcp)));
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, pce);
    if pc == pcb {
      assert {:split_here} true;
      assert false;                                  // SetQuantToClock
    } else if pc < e1 {
      assert {:split_here} true;
      NestStampCapSiteRE(r1, code, pcb + 1, e1, pc, qcp, gid, reg);
    } else {
      assert {:split_here} true;
      NestStampCapSiteMin(k - 1, qid, r1, code, e1, pce, pc, qcp, gid, reg);
    }
  }

  lemma NestStampCapSiteOpt(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                             pcb: nat, pce: nat, pc: nat, qcp: seq<int>, gid: nat, reg: int)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    requires PIV.CapUnique(r1) && PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    requires NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(reg))
    requires reg == CP.start_reg(gid) || reg == CP.end_reg(gid)
    ensures gid in PIV.CapIds(r1)
    ensures StampClearRE(qcp, qid)
    ensures forall A: nat :: A in PIV.QuantIds(r1) && AI.get_idx(qcp, A) >= 0
              ==> gid !in PIV.CapIds(PIV.QidBody(r1, A))
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, pcb + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce)
      && (if pc == pcb || pc == pcb + 1 then true
          else if pc == pcb + 2 then StampClearRE(qcp, qid)
          else if pcb + 3 <= pc < e1 then
            StampClearRE(qcp, qid) && NestStampRE(r1, code, pcb + 3, e1, pc, qcp)
          else if pc == e1 then StampClearRE(qcp, qid)
          else NestStampOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, qcp));
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
    // (2026-09-04) refutation branch FIRST and one batch per branch: the
    // three-way split in one VC took 15 min.
    if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 {
      assert {:split_here} true;
      assert false;                                  // Fork / stamp / BeginLoop / EndLoop
    } else if pcb + 3 <= pc < e1 {
      assert {:split_here} true;
      NestStampCapSiteRE(r1, code, pcb + 3, e1, pc, qcp, gid, reg);
    } else {
      assert {:split_here} true;
      NestStampCapSiteOpt(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, qcp, gid, reg);
    }
  }

  /** (2026-11-04) Register-generic `NestStampOpenSiteRE`: a capture OPEN or
      CLOSE site is inside `re` and outside the body of every STAMPED
      quantifier of `re` — the hypothesis the readout's Open and Close
      commutations need (`PIV.LiveStampsGm{Open,Close}Commute`). */
  lemma NestStampCapSiteRE(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                            qcp: seq<int>, gid: nat, reg: int)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(reg))
    requires reg == CP.start_reg(gid) || reg == CP.end_reg(gid)
    ensures gid in PIV.CapIds(re)
    ensures forall A: nat :: A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
              ==> gid !in PIV.CapIds(PIV.QidBody(re, A))
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
      NR.NfaRepIncrRE(re, code, pcb, pce);
      assert false;
    case Re_character(ch) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      assert pc == pcb;
      assert false;                                  // Consume
    case Re_anchor(_) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      assert pc == pcb;
      assert false;                                  // AnchorAssertion
    case Re_lookaround(lid, la, r1) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      assert pc == pcb;
      assert false;                                  // CheckOracle / NegCheckOracle
    case Re_alt(r1, r2) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && (if pc == pcb then true
            else if pcb + 1 <= pc < e1 then NestStampRE(r1, code, pcb + 1, e1, pc, qcp)
            else if pc == e1 then true
            else NestStampRE(r2, code, e1 + 1, pce, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, pce);
      if pc == pcb || pc == e1 {
        assert false;                                // Fork / Jmp
      } else if pcb + 1 <= pc < e1 {
        NestStampCapSiteRE(r1, code, pcb + 1, e1, pc, qcp, gid, reg);
        NestStampSplitAlt(re, r1, r2, qcp, gid, true);
      } else {
        NestStampCapSiteRE(r2, code, e1 + 1, pce, pc, qcp, gid, reg);
        NestStampSplitAlt(re, r1, r2, qcp, gid, false);
      }
    case Re_con(r1, r2) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && (if pc < e1 then NestStampRE(r1, code, pcb, e1, pc, qcp)
            else NestStampRE(r2, code, e1, pce, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb, e1);
      NR.NfaRepIncrRE(r2, code, e1, pce);
      if pc < e1 {
        NestStampCapSiteRE(r1, code, pcb, e1, pc, qcp, gid, reg);
        NestStampSplitAlt(re, r1, r2, qcp, gid, true);
      } else {
        NestStampCapSiteRE(r2, code, e1, pce, pc, qcp, gid, reg);
        NestStampSplitAlt(re, r1, r2, qcp, gid, false);
      }
    case Re_capture(cid, r1) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && (pcb + 1 <= pc < e1 ==> NestStampRE(r1, code, pcb + 1, e1, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      assert cid >= 0;                               // CapUnique
      assert PIV.QuantIds(re) == PIV.QuantIds(r1);
      if pc == pcb || pc == e1 {
        // the capture's own open/close: the register pins the group (parity)
        assert reg == CP.start_reg(cid) || reg == CP.end_reg(cid);
        assert cid == gid;
        assert gid in PIV.CapIds(re);
        forall A: nat | A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
          ensures gid !in PIV.CapIds(PIV.QidBody(re, A)) {
          assert PIV.QidBody(re, A) == PIV.QidBody(r1, A);
          PIV.CapIdsQidBodySubset(r1, A);
          assert gid !in PIV.CapIds(r1);             // CapUnique: cid is fresh for r1
        }
      } else {
        NestStampCapSiteRE(r1, code, pcb + 1, e1, pc, qcp, gid, reg);
        forall A: nat | A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
          ensures gid !in PIV.CapIds(PIV.QidBody(re, A)) {
          assert PIV.QidBody(re, A) == PIV.QidBody(r1, A);
        }
      }
    case Re_quant(nul, qid, q, r1) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      assert qid >= 0;                               // QuantUnique
      assert (qid as nat) !in PIV.QuantIds(r1);      // QuantUnique
      assert PIV.QidBody(re, qid as nat) == r1;
      var stamped := StampClearRE(qcp, qid);
      if q.max.Some? {
        assert {:split_here} true;
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid, r1, code, em, pce)
          && (if pc < em then NestStampMinRE(mn, qid, r1, code, pcb, em, pc, qcp)
              else NestStampOptRE(kx, q.greedy, qid, r1, code, em, pce, pc, qcp));
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid, r1, code, em, pce);
        if pc < em {
          NestStampCapSiteMin(mn, qid, r1, code, pcb, em, pc, qcp, gid, reg);
        } else {
          NestStampCapSiteOpt(kx, q.greedy, qid, r1, code, em, pce, pc, qcp, gid, reg);
        }
        NestStampQuantIds(re, nul, qid, q, r1, qcp, gid);
        return;
      }
      if !(q.min == 0 && q.max == None) && nul != R.NonNullable && !q.greedy {
        assert {:split_here} true;
        var mn := q.min as nat;
        var em, e1 := NestStampGenREInv(nul, qid, q, r1, code, pcb, pce, pc, qcp);
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          NestStampCapSiteMin(mn, qid, r1, code, pcb, em, pc, qcp, gid, reg);
        } else if em + 3 <= pc < e1 {
          NestStampCapSiteRE(r1, code, em + 3, e1, pc, qcp, gid, reg);
        } else {
          assert false;                              // Fork/stamp/BeginLoop/EndLoop/Jmp
        }
        NestStampQuantIds(re, nul, qid, q, r1, qcp, gid);
        return;
      }
      if !(q.min == 0 && q.max == None) && nul != R.NonNullable {
        assert {:split_here} true;
        var mn1 := (q.min - 1) as nat;
        var em, e1 := NestStampCinREInv(nul, qid, q, r1, code, pcb, pce, pc, qcp);
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          NestStampCapSiteMin(mn1, qid, r1, code, pcb, em, pc, qcp, gid, reg);
        } else if em + 3 <= pc < e1 {
          NestStampCapSiteRE(r1, code, em + 3, e1, pc, qcp, gid, reg);
        } else {
          assert false;                              // the loop's own instructions
        }
        NestStampQuantIds(re, nul, qid, q, r1, qcp, gid);
        return;
      }
      if !(q.min == 0 && q.max == None) {
        assert {:split_here} true;
        var mn1 := (q.min - 1) as nat;
        var em: nat, e1: nat :|
          NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
          && NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
          && NR.NfaRepRE(r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pce == e1 + 1
          && (if pc < em then NestStampMinRE(mn1, qid, r1, code, pcb, em, pc, qcp)
              else if pc == em then true
              else if em + 1 <= pc < e1 then
                StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 1, e1, pc, qcp)
              else StampClearRE(qcp, qid));
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          NestStampCapSiteMin(mn1, qid, r1, code, pcb, em, pc, qcp, gid, reg);
        } else if em + 1 <= pc < e1 {
          NestStampCapSiteRE(r1, code, em + 1, e1, pc, qcp, gid, reg);
        } else {
          assert false;                              // the mark / the backward fork
        }
        NestStampQuantIds(re, nul, qid, q, r1, qcp, gid);
        return;
      }
      // the star
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
        && pce == e1 + 2
        && (if pc == pcb || pc == pcb + 1 then true
            else if pc == pcb + 2 then StampClearRE(qcp, qid)
            else if pcb + 3 <= pc < e1 then
              StampClearRE(qcp, qid) && NestStampRE(r1, code, pcb + 3, e1, pc, qcp)
            else StampClearRE(qcp, qid));
      NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
      if pcb + 3 <= pc < e1 {
        NestStampCapSiteRE(r1, code, pcb + 3, e1, pc, qcp, gid, reg);
      } else {
        assert false;                                // the loop's own instructions
      }
      NestStampQuantIds(re, nul, qid, q, r1, qcp, gid);
  }

  /** Bookkeeping for `NestStampOpenSiteRE`'s binary arms: the write is in one
      half, so a stamped quantifier of the OTHER half cannot own it
      (`CapUnique`), and one in the same half is the recursive conclusion. */
  lemma NestStampSplitAlt(re: R.regex, r1: R.regex, r2: R.regex, qcp: seq<int>, gid: nat, inLeft: bool)
    requires re == R.Re_alt(r1, r2) || re == R.Re_con(r1, r2)
    requires PIV.CapUnique(re)
    requires inLeft ==> gid in PIV.CapIds(r1)
    requires !inLeft ==> gid in PIV.CapIds(r2)
    requires inLeft ==> forall A: nat :: A in PIV.QuantIds(r1) && AI.get_idx(qcp, A) >= 0
                          ==> gid !in PIV.CapIds(PIV.QidBody(r1, A))
    requires !inLeft ==> forall A: nat :: A in PIV.QuantIds(r2) && AI.get_idx(qcp, A) >= 0
                           ==> gid !in PIV.CapIds(PIV.QidBody(r2, A))
    ensures gid in PIV.CapIds(re)
    ensures forall A: nat :: A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
              ==> gid !in PIV.CapIds(PIV.QidBody(re, A))
  {
    assert PIV.CapIds(re) == PIV.CapIds(r1) + PIV.CapIds(r2);
    assert PIV.QuantIds(re) == PIV.QuantIds(r1) + PIV.QuantIds(r2);
    assert PIV.CapIds(r1) * PIV.CapIds(r2) == {};
    forall A: nat | A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
      ensures gid !in PIV.CapIds(PIV.QidBody(re, A)) {
      if A in PIV.QuantIds(r1) {
        assert PIV.QidBody(re, A) == PIV.QidBody(r1, A);
        PIV.CapIdsQidBodySubset(r1, A);
        if !inLeft {
          assert gid !in PIV.CapIds(r1)
            by { if gid in PIV.CapIds(r1) { assert gid in PIV.CapIds(r1) * PIV.CapIds(r2); } }
        }
      } else {
        assert A in PIV.QuantIds(r2);
        assert PIV.QidBody(re, A) == PIV.QidBody(r2, A);
        PIV.CapIdsQidBodySubset(r2, A);
        if inLeft {
          assert gid !in PIV.CapIds(r2)
            by { if gid in PIV.CapIds(r2) { assert gid in PIV.CapIds(r1) * PIV.CapIds(r2); } }
        }
      }
    }
  }

  /** Bookkeeping for `NestStampOpenSiteRE`'s quantifier arms: the write sits
      in the body, past `qid`'s mark, so `qid`'s own stamp is clear and every
      other stamped quantifier is one of the body's. */
  lemma NestStampQuantIds(re: R.regex, nul: R.nullability, qid: R.quantid, q: R.counted_quantifier,
                          r1: R.regex, qcp: seq<int>, gid: nat)
    requires re == R.Re_quant(nul, qid, q, r1)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires gid in PIV.CapIds(r1)
    requires StampClearRE(qcp, qid)
    requires forall A: nat :: A in PIV.QuantIds(r1) && AI.get_idx(qcp, A) >= 0
               ==> gid !in PIV.CapIds(PIV.QidBody(r1, A))
    ensures gid in PIV.CapIds(re)
    ensures forall A: nat :: A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
              ==> gid !in PIV.CapIds(PIV.QidBody(re, A))
  {
    assert PIV.CapIds(re) == PIV.CapIds(r1);
    forall A: nat | A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
      ensures gid !in PIV.CapIds(PIV.QidBody(re, A)) {
      if qid >= 0 && A == qid as nat {
        assert AI.get_idx(qcp, qid) < 0;             // StampClearRE
        assert false;
      } else {
        assert A in PIV.QuantIds(r1);
        assert PIV.QidBody(re, A) == PIV.QidBody(r1, A);
      }
    }
  }

  // =========================================================================
  // 8. (2026-11-04) THE QUANT-WRITE SITE: no STAMPED quantifier encloses a
  //    `SetQuantToClock(q0, _)` instruction. Every such site is past each
  //    enclosing quantifier's clock mark (which clears that stamp) and before
  //    its true stamp (which exits the block). The readout's mark and stamp
  //    steps (`PIV.LiveStampsGmMark` / `PIV.LiveStampsGmStamp`) need exactly
  //    `PIV.NoStampedAbove`.
  // =========================================================================

  lemma QuantIdsQidBodySubset(r: R.regex, qid: nat)
    requires qid in PIV.QuantIds(r)
    ensures PIV.QuantIds(PIV.QidBody(r, qid)) <= PIV.QuantIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if qid in PIV.QuantIds(r1) { QuantIdsQidBodySubset(r1, qid); } else { QuantIdsQidBodySubset(r2, qid); }
    case Re_con(r1, r2) => if qid in PIV.QuantIds(r1) { QuantIdsQidBodySubset(r1, qid); } else { QuantIdsQidBodySubset(r2, qid); }
    case Re_quant(nul, qid0, q, r1) => if qid0 >= 0 && (qid0 as nat) == qid {} else { QuantIdsQidBodySubset(r1, qid); }
    case Re_capture(cid, r1) => QuantIdsQidBodySubset(r1, qid);
    case Re_lookaround(_, _, r1) => QuantIdsQidBodySubset(r1, qid);
  }

  /** The conclusion inside a quantifier `qid` over body `r1`: the write is
      `qid`'s own, or it sits in the body past `qid`'s mark. */
  ghost predicate QuantSiteIn(qid: R.quantid, r1: R.regex, qcp: seq<int>, q0: int) {
    q0 >= 0
    && (q0 == qid
        || ((q0 as nat) in PIV.QuantIds(r1) && StampClearRE(qcp, qid)
            && PIV.NoStampedAbove(r1, qcp, q0 as nat)))
  }

  /** …lifted to the quantifier node itself. */
  lemma QuantSiteLift(re: R.regex, nul: R.nullability, qid: R.quantid, q: R.counted_quantifier,
                      r1: R.regex, qcp: seq<int>, q0: int)
    requires re == R.Re_quant(nul, qid, q, r1)
    requires PIV.QuantUnique(re)
    requires QuantSiteIn(qid, r1, qcp, q0)
    ensures q0 >= 0 && (q0 as nat) in PIV.QuantIds(re)
    ensures PIV.NoStampedAbove(re, qcp, q0 as nat)
  {
    assert qid >= 0 && (qid as nat) !in PIV.QuantIds(r1);
    forall A: nat | A in PIV.QuantIds(re) && A != q0 as nat && AI.get_idx(qcp, A) >= 0
      ensures (q0 as nat) !in PIV.QuantIds(PIV.QidBody(re, A))
    {
      if A == qid as nat {
        // only reachable when q0 is in the body — and then qid's stamp is clear
        assert q0 != qid;
        assert StampClearRE(qcp, qid);
        assert false;
      } else {
        assert A in PIV.QuantIds(r1) && PIV.QidBody(re, A) == PIV.QidBody(r1, A);
        if q0 == qid {
          QuantIdsQidBodySubset(r1, A);
        }
      }
    }
  }

  /** The binary arms: the write is in one half, and a stamped quantifier of
      the OTHER half cannot enclose it (`QuantUnique`). */
  lemma QuantSiteSplit(re: R.regex, r1: R.regex, r2: R.regex, qcp: seq<int>, q0: nat, inLeft: bool)
    requires re == R.Re_alt(r1, r2) || re == R.Re_con(r1, r2)
    requires PIV.QuantUnique(re)
    requires inLeft ==> q0 in PIV.QuantIds(r1) && PIV.NoStampedAbove(r1, qcp, q0)
    requires !inLeft ==> q0 in PIV.QuantIds(r2) && PIV.NoStampedAbove(r2, qcp, q0)
    ensures q0 in PIV.QuantIds(re)
    ensures PIV.NoStampedAbove(re, qcp, q0)
  {
    assert PIV.QuantIds(re) == PIV.QuantIds(r1) + PIV.QuantIds(r2);
    forall A: nat | A in PIV.QuantIds(re) && A != q0 && AI.get_idx(qcp, A) >= 0
      ensures q0 !in PIV.QuantIds(PIV.QidBody(re, A))
    {
      if A in PIV.QuantIds(r1) {
        assert PIV.QidBody(re, A) == PIV.QidBody(r1, A);
        QuantIdsQidBodySubset(r1, A);
        if !inLeft {
          assert q0 !in PIV.QuantIds(r1)
            by { if q0 in PIV.QuantIds(r1) { assert q0 in PIV.QuantIds(r1) * PIV.QuantIds(r2); } }
        }
      } else {
        assert A in PIV.QuantIds(r2) && A !in PIV.QuantIds(r1);
        assert PIV.QidBody(re, A) == PIV.QidBody(r2, A);
        QuantIdsQidBodySubset(r2, A);
        if inLeft {
          assert q0 !in PIV.QuantIds(r2)
            by { if q0 in PIV.QuantIds(r2) { assert q0 in PIV.QuantIds(r1) * PIV.QuantIds(r2); } }
        }
      }
    }
  }

  lemma NestStampQuantSiteMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat,
                              pc: nat, qcp: seq<int>, q0: int, b: bool)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    requires PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    requires NestStampMinRE(k, qid, r1, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q0, b))
    requires qid >= 0
    ensures QuantSiteIn(qid, r1, qcp, q0)
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce)
      && (if pc == pcb then true
          else StampClearRE(qcp, qid)
               && (if pc < e1 then NestStampRE(r1, code, pcb + 1, e1, pc, qcp)
                   else NestStampMinRE(k - 1, qid, r1, code, e1, pce, pc, qcp)));
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, pce);
    if pc == pcb {
      assert {:split_here} true;
      assert q0 == qid;                              // the copy's own mark
    } else if pc < e1 {
      assert {:split_here} true;
      NestStampQuantSiteRE(r1, code, pcb + 1, e1, pc, qcp, q0, b);
    } else {
      assert {:split_here} true;
      NestStampQuantSiteMin(k - 1, qid, r1, code, e1, pce, pc, qcp, q0, b);
    }
  }

  lemma NestStampQuantSiteOpt(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                              pcb: nat, pce: nat, pc: nat, qcp: seq<int>, q0: int, b: bool)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    requires PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    requires NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q0, b))
    requires qid >= 0
    ensures QuantSiteIn(qid, r1, qcp, q0)
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, pcb + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce)
      && (if pc == pcb || pc == pcb + 1 then true
          else if pc == pcb + 2 then StampClearRE(qcp, qid)
          else if pcb + 3 <= pc < e1 then
            StampClearRE(qcp, qid) && NestStampRE(r1, code, pcb + 3, e1, pc, qcp)
          else if pc == e1 then StampClearRE(qcp, qid)
          else NestStampOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, qcp));
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
    if pc == pcb || pc == pcb + 2 || pc == e1 {
      assert {:split_here} true;
      assert false;                                  // Fork / BeginLoop / EndLoop
    } else if pc == pcb + 1 {
      assert {:split_here} true;
      assert q0 == qid;                              // the copy's own mark
    } else if pcb + 3 <= pc < e1 {
      assert {:split_here} true;
      NestStampQuantSiteRE(r1, code, pcb + 3, e1, pc, qcp, q0, b);
    } else {
      assert {:split_here} true;
      NestStampQuantSiteOpt(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, qcp, q0, b);
    }
  }

  /** A `SetQuantToClock(q0, _)` site is a quantifier of `re` that no STAMPED
      quantifier of `re` encloses. */
  lemma NestStampQuantSiteRE(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                             qcp: seq<int>, q0: int, b: bool)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q0, b))
    ensures q0 >= 0 && (q0 as nat) in PIV.QuantIds(re)
    ensures PIV.NoStampedAbove(re, qcp, q0 as nat)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
      NR.NfaRepIncrRE(re, code, pcb, pce);
      assert false;
    case Re_character(ch) =>
      assert {:split_here} true;
      assert pc == pcb;
      assert false;                                  // Consume
    case Re_anchor(_) =>
      assert {:split_here} true;
      assert pc == pcb;
      assert false;                                  // AnchorAssertion
    case Re_lookaround(lid, la, r1) =>
      assert {:split_here} true;
      assert pc == pcb;
      assert false;                                  // CheckOracle / NegCheckOracle
    case Re_alt(r1, r2) =>
      assert {:split_here} true;
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && (if pc == pcb then true
            else if pcb + 1 <= pc < e1 then NestStampRE(r1, code, pcb + 1, e1, pc, qcp)
            else if pc == e1 then true
            else NestStampRE(r2, code, e1 + 1, pce, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, pce);
      if pc == pcb || pc == e1 {
        assert false;                                // Fork / Jmp
      } else if pcb + 1 <= pc < e1 {
        NestStampQuantSiteRE(r1, code, pcb + 1, e1, pc, qcp, q0, b);
        QuantSiteSplit(re, r1, r2, qcp, q0 as nat, true);
      } else {
        NestStampQuantSiteRE(r2, code, e1 + 1, pce, pc, qcp, q0, b);
        QuantSiteSplit(re, r1, r2, qcp, q0 as nat, false);
      }
    case Re_con(r1, r2) =>
      assert {:split_here} true;
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && (if pc < e1 then NestStampRE(r1, code, pcb, e1, pc, qcp)
            else NestStampRE(r2, code, e1, pce, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb, e1);
      NR.NfaRepIncrRE(r2, code, e1, pce);
      if pc < e1 {
        NestStampQuantSiteRE(r1, code, pcb, e1, pc, qcp, q0, b);
        QuantSiteSplit(re, r1, r2, qcp, q0 as nat, true);
      } else {
        NestStampQuantSiteRE(r2, code, e1, pce, pc, qcp, q0, b);
        QuantSiteSplit(re, r1, r2, qcp, q0 as nat, false);
      }
    case Re_capture(cid, r1) =>
      assert {:split_here} true;
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && (pcb + 1 <= pc < e1 ==> NestStampRE(r1, code, pcb + 1, e1, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      if pc == pcb || pc == e1 {
        assert false;                                // SetRegisterToCP
      } else {
        NestStampQuantSiteRE(r1, code, pcb + 1, e1, pc, qcp, q0, b);
        assert PIV.QuantIds(re) == PIV.QuantIds(r1);
        forall A: nat | A in PIV.QuantIds(re) ensures PIV.QidBody(re, A) == PIV.QidBody(r1, A) {}
      }
    case Re_quant(nul, qid, q, r1) =>
      assert {:split_here} true;
      assert qid >= 0;                               // QuantUnique
      if q.max.Some? {
        assert {:split_here} true;
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid, r1, code, em, pce)
          && (if pc < em then NestStampMinRE(mn, qid, r1, code, pcb, em, pc, qcp)
              else NestStampOptRE(kx, q.greedy, qid, r1, code, em, pce, pc, qcp));
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid, r1, code, em, pce);
        if pc < em {
          NestStampQuantSiteMin(mn, qid, r1, code, pcb, em, pc, qcp, q0, b);
        } else {
          NestStampQuantSiteOpt(kx, q.greedy, qid, r1, code, em, pce, pc, qcp, q0, b);
        }
        QuantSiteLift(re, nul, qid, q, r1, qcp, q0);
        return;
      }
      if !(q.min == 0 && q.max == None) && nul != R.NonNullable && !q.greedy {
        assert {:split_here} true;
        var mn := q.min as nat;
        var em, e1 := NestStampGenREInv(nul, qid, q, r1, code, pcb, pce, pc, qcp);
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          NestStampQuantSiteMin(mn, qid, r1, code, pcb, em, pc, qcp, q0, b);
        } else if pc == em + 1 {
          assert q0 == qid;                          // the loop's mark
        } else if em + 3 <= pc < e1 {
          NestStampQuantSiteRE(r1, code, em + 3, e1, pc, qcp, q0, b);
        } else {
          assert false;                              // Fork/BeginLoop/EndLoop/Jmp
        }
        QuantSiteLift(re, nul, qid, q, r1, qcp, q0);
        return;
      }
      if !(q.min == 0 && q.max == None) && nul != R.NonNullable {
        assert {:split_here} true;
        var mn1 := (q.min - 1) as nat;
        var em, e1 := NestStampCinREInv(nul, qid, q, r1, code, pcb, pce, pc, qcp);
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          NestStampQuantSiteMin(mn1, qid, r1, code, pcb, em, pc, qcp, q0, b);
        } else if pc == em + 1 || pc == e1 + 2 {
          assert q0 == qid;                          // the loop's mark / the true stamp
        } else if em + 3 <= pc < e1 {
          NestStampQuantSiteRE(r1, code, em + 3, e1, pc, qcp, q0, b);
        } else {
          assert false;                              // Fork/BeginLoop/EndLoop/end fork
        }
        QuantSiteLift(re, nul, qid, q, r1, qcp, q0);
        return;
      }
      if !(q.min == 0 && q.max == None) {
        assert {:split_here} true;
        var mn1 := (q.min - 1) as nat;
        var em: nat, e1: nat :|
          NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
          && NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
          && NR.NfaRepRE(r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pce == e1 + 1
          && (if pc < em then NestStampMinRE(mn1, qid, r1, code, pcb, em, pc, qcp)
              else if pc == em then true
              else if em + 1 <= pc < e1 then
                StampClearRE(qcp, qid) && NestStampRE(r1, code, em + 1, e1, pc, qcp)
              else StampClearRE(qcp, qid));
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          NestStampQuantSiteMin(mn1, qid, r1, code, pcb, em, pc, qcp, q0, b);
        } else if pc == em {
          assert q0 == qid;                          // the mark
        } else if em + 1 <= pc < e1 {
          NestStampQuantSiteRE(r1, code, em + 1, e1, pc, qcp, q0, b);
        } else {
          assert false;                              // the backward fork
        }
        QuantSiteLift(re, nul, qid, q, r1, qcp, q0);
        return;
      }
      // the star
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
        && pce == e1 + 2
        && (if pc == pcb || pc == pcb + 1 then true
            else if pc == pcb + 2 then StampClearRE(qcp, qid)
            else if pcb + 3 <= pc < e1 then
              StampClearRE(qcp, qid) && NestStampRE(r1, code, pcb + 3, e1, pc, qcp)
            else StampClearRE(qcp, qid));
      NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
      if pc == pcb + 1 {
        assert q0 == qid;                            // the mark
      } else if pcb + 3 <= pc < e1 {
        NestStampQuantSiteRE(r1, code, pcb + 3, e1, pc, qcp, q0, b);
      } else {
        assert false;                                // Fork/BeginLoop/EndLoop/Jmp
      }
      QuantSiteLift(re, nul, qid, q, r1, qcp, q0);
  }

  /** Top-level wrappers (mirrors of `NestStampTopQuantWrite`). */
  lemma NestStampTopQuantSite(re: R.regex, code: RB.code, endl: nat, pc: nat, qcp: seq<int>, q0: int, b: bool)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires PIV.QuantUnique(re)
    requires pc < endl
    requires NestStampTopRE(re, code, endl, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q0, b))
    ensures q0 >= 0 && (q0 as nat) in PIV.QuantIds(re)
    ensures PIV.NoStampedAbove(re, qcp, q0 as nat)
  {
    NestStampQuantSiteRE(re, code, 0, endl, pc, qcp, q0, b);
  }

  lemma NestStampTopCapSite(re: R.regex, code: RB.code, endl: nat, pc: nat, qcp: seq<int>, gid: nat, reg: int)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires pc < endl
    requires NestStampTopRE(re, code, endl, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(reg))
    requires reg == CP.start_reg(gid) || reg == CP.end_reg(gid)
    ensures gid in PIV.CapIds(re)
    ensures forall A: nat :: A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
              ==> gid !in PIV.CapIds(PIV.QidBody(re, A))
  {
    NestStampCapSiteRE(re, code, 0, endl, pc, qcp, gid, reg);
  }


  // =========================================================================
  // 9. (2026-11-04, §2.5b rung D2) THE TRUE STAMP `SetQuantToClock(q, true)`
  //    at the CIN-greedy plus's exit `e1 + 2`, on the clock side
  //    (`NI.NestInvRE`; nest-inv itself stays untouched and cached):
  //    * `TrueStampSite*` — twin of `NI.NestInvResetSite`: the site is a
  //      quantifier of `re`, outside looks, with its enclosing quantifiers
  //      and captures present (`PathPresentQ`). Every FALSE mark is now a
  //      contradiction and the CIN arm's `e1 + 2` is the base case.
  //    * `TrueStampBack*` — the thread may be re-positioned to the end fork
  //      `e1 + 1` under the NEW clocks `qc' = qc[q0 := clk]`: no claim outside
  //      q0's own block mentions q0's clock, and the end fork's own claim
  //      (`qc'[q0] >= mx`) holds for the fresh clock. The end fork's exit
  //      edge `e1 + 1 -> e1 + 3` is an ordinary `NI.StepEdgeRE`, so
  //      `NI.NestInvAdvance` finishes the step (`NestInvTopTrueStamp`).
  // =========================================================================

  lemma TrueStampSiteMin(k: nat, qn: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                            cc: seq<int>, qc: seq<int>, mx: int, qid: nat)
    requires NR.NfaRepMinRE(k, qn, r1, code, pcb, pce)
    requires PIV.CapUnique(r1) && PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    requires NI.NestInvMinRE(k, qn, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, true))
    ensures (qid as int) == qn
         || (qid in PIV.QuantIds(r1) && qid in PIV.QuantIdsOutsideLooks(r1)
             && AI.get_idx(qc, qn) >= mx
             && PIV.PathPresentQ(r1, cc, qc, AI.get_idx(qc, qn), qid))
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qn, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qn, r1, code, e1, pce)
      && (if pc == pcb then true
          else if pcb + 1 <= pc < e1 then
            AI.get_idx(qc, qn) >= mx
            && NI.NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, AI.get_idx(qc, qn))
          else NI.NestInvMinRE(k - 1, qn, r1, code, e1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    if pc == pcb {
      assert false;                                 // the copy head stamps FALSE
    } else if pcb + 1 <= pc < e1 {
      var qv := AI.get_idx(qc, qn);
      TrueStampSite(r1, code, pcb + 1, e1, pc, cc, qc, qv, qid);
    } else {
      TrueStampSiteMin(k - 1, qn, r1, code, e1, pce, pc, cc, qc, mx, qid);
    }
  }

  /** `TrueStampSite` for optional-layer chains. */
  lemma TrueStampSiteOpt(k: nat, greedy: bool, qn: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                            cc: seq<int>, qc: seq<int>, mx: int, qid: nat)
    requires NR.NfaRepOptRE(k, greedy, qn, r1, code, pcb, pce)
    requires PIV.CapUnique(r1) && PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    requires NI.NestInvOptRE(k, greedy, qn, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, true))
    ensures (qid as int) == qn
         || (qid in PIV.QuantIds(r1) && qid in PIV.QuantIdsOutsideLooks(r1)
             && AI.get_idx(qc, qn) >= mx
             && PIV.PathPresentQ(r1, cc, qc, AI.get_idx(qc, qn), qid))
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qn, false))
      && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, pcb + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qn, r1, code, e1 + 1, pce)
      && (if pc == pcb || pc == pcb + 1 then true
          else if pc == pcb + 2 then
            AI.get_idx(qc, qn) >= mx && NI.AllStaleRE(r1, cc, AI.get_idx(qc, qn))
          else if pcb + 3 <= pc < e1 then
            AI.get_idx(qc, qn) >= mx
            && NI.NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qn))
          else if pc == e1 then AI.get_idx(qc, qn) >= mx
          else NI.NestInvOptRE(k - 1, greedy, qn, r1, code, e1 + 1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    if pc == pcb + 1 || pc == pcb || pc == pcb + 2 || pc == e1 {
      assert false;                                 // Fork/BeginLoop/EndLoop
    } else if pcb + 3 <= pc < e1 {
      var qv := AI.get_idx(qc, qn);
      TrueStampSite(r1, code, pcb + 3, e1, pc, cc, qc, qv, qid);
    } else {
      TrueStampSiteOpt(k - 1, greedy, qn, r1, code, e1 + 1, pce, pc, cc, qc, mx, qid);
    }
  }

  lemma TrueStampSite(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                         cc: seq<int>, qc: seq<int>, mx: int, qid: nat)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NI.NestInvRE(re, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, true))
    ensures qid in PIV.QuantIds(re)
    ensures qid in PIV.QuantIdsOutsideLooks(re)   // L3a: SetQuantToClock sites are outside-look
    ensures PIV.PathPresentQ(re, cc, qc, mx, qid)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
      assert {:split_here} true;   // (2026-09-05) per-arm batch under z3 4.14
    case Re_character(ch) =>
      assert {:split_here} true;   // (2026-09-05) per-arm batch under z3 4.14
      assert pc == pcb;
      assert false;
    case Re_alt(r1, r2) =>
      assert {:split_here} true;   // (2026-09-05) per-arm batch under z3 4.14
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && if pc == pcb then NI.AllStaleRE(r1, cc, mx) && NI.AllStaleRE(r2, cc, mx)
           else if pcb + 1 <= pc < e1 then
             NI.NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx) && NI.AllStaleRE(r2, cc, mx)
           else if pc == e1 then true
           else NI.NestInvRE(r2, code, e1 + 1, pce, pc, cc, qc, mx);
      if pc == pcb {
        assert false;
      } else if pcb + 1 <= pc < e1 {
        TrueStampSite(r1, code, pcb + 1, e1, pc, cc, qc, mx, qid);
      } else if pc == e1 {
        assert false;
      } else {
        TrueStampSite(r2, code, e1 + 1, pce, pc, cc, qc, mx, qid);
        assert qid !in PIV.QuantIds(r1) by {
          if qid in PIV.QuantIds(r1) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
      }
    case Re_con(r1, r2) =>
      assert {:split_here} true;   // (2026-09-05) per-arm batch under z3 4.14
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && if pc < e1 then NI.NestInvRE(r1, code, pcb, e1, pc, cc, qc, mx) && NI.AllStaleRE(r2, cc, mx)
           else NI.NestInvRE(r2, code, e1, pce, pc, cc, qc, mx);
      if pc < e1 {
        TrueStampSite(r1, code, pcb, e1, pc, cc, qc, mx, qid);
      } else {
        TrueStampSite(r2, code, e1, pce, pc, cc, qc, mx, qid);
        assert qid !in PIV.QuantIds(r1) by {
          if qid in PIV.QuantIds(r1) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
      }
    case Re_quant(nul, qid0, q, r1) =>
      assert {:split_here} true;   // (2026-09-05) per-arm batch under z3 4.14
      assert qid0 >= 0;                             // QuantUnique
      if q.max.Some? {
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid0, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid0, r1, code, em, pce)
          && (if pc < em then NI.NestInvMinRE(mn, qid0, r1, code, pcb, em, pc, cc, qc, mx)
              else NI.NestInvOptRE(kx, q.greedy, qid0, r1, code, em, pce, pc, cc, qc, mx));
        NR.NfaRepIncrMinRE(mn, qid0, r1, code, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid0, r1, code, em, pce);
        if pc < em {
          TrueStampSiteMin(mn, qid0, r1, code, pcb, em, pc, cc, qc, mx, qid);
        } else {
          TrueStampSiteOpt(kx, q.greedy, qid0, r1, code, em, pce, pc, cc, qc, mx, qid);
        }
        if (qid as int) == qid0 {
          assert qid in PIV.QuantIds(re);           // PathPresentQ base case
        } else {
          assert (qid0 as nat) != qid;
          assert qid in PIV.QuantIds(r1);
          assert AI.get_idx(qc, qid0) >= mx;        // ancestor clause
        }
        return;
      }
      if !(q.min == 0 && q.max == None) && nul != R.NonNullable && !q.greedy {
        // §2.5a GENERIC: `min` forced copies, then the ORDINARY STAR loop at
        // `em`; `em + 1` is this quant's own reset site.
        var mn := q.min as nat;
        var em, e1 := NI.NestInvGenREInv(nul, qid0, q, r1, code, pcb, pce, pc, cc, qc, mx);
        NR.NfaRepIncrMinRE(mn, qid0, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          TrueStampSiteMin(mn, qid0, r1, code, pcb, em, pc, cc, qc, mx, qid);
        } else if em + 3 <= pc < e1 {
          var qv := AI.get_idx(qc, qid0);
          TrueStampSite(r1, code, em + 3, e1, pc, cc, qc, qv, qid);
        } else {
          assert false;                             // Fork/mark(false)/BeginLoop/EndLoop/Jmp
        }
        if (qid as int) == qid0 {
          assert qid in PIV.QuantIds(re);           // PathPresentQ base case
        } else {
          assert (qid0 as nat) != qid;
          assert qid in PIV.QuantIds(r1);
          assert AI.get_idx(qc, qid0) >= mx;        // ancestor clause
        }
        return;
      }
      if !(q.min == 0 && q.max == None) && nul != R.NonNullable {
        // §2.5b CIN-GREEDY: `em + 1` is this quant's own reset site; the
        // trailing stamp at `e1 + 2` carries flag TRUE, contradicting the
        // reset-site (false) hypothesis.
        var mn1 := (q.min - 1) as nat;
        var em, e1 := NI.NestInvCinREInv(nul, qid0, q, r1, code, pcb, pce, pc, cc, qc, mx);
        NR.NfaRepIncrMinRE(mn1, qid0, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          TrueStampSiteMin(mn1, qid0, r1, code, pcb, em, pc, cc, qc, mx, qid);
        } else if pc == e1 + 2 {
          // THE true stamp: the instruction pins qid == qid0
          assert (qid as int) == qid0;
        } else if em + 3 <= pc < e1 {
          var qv := AI.get_idx(qc, qid0);
          TrueStampSite(r1, code, em + 3, e1, pc, cc, qc, qv, qid);
        } else {
          assert false;   // forks/mark(false)/BeginLoop/EndLoop
        }
        if (qid as int) == qid0 {
          assert qid in PIV.QuantIds(re);           // PathPresentQ base case
        } else {
          assert (qid0 as nat) != qid;
          assert qid in PIV.QuantIds(r1);
          assert AI.get_idx(qc, qid0) >= mx;        // ancestor clause
        }
        return;
      }
      if !(q.min == 0 && q.max == None) {
        var mn1 := (q.min - 1) as nat;
        var em: nat, e1: nat :|
          NR.NfaRepMinRE(mn1, qid0, r1, code, pcb, em)
          && NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid0, false))
          && NR.NfaRepRE(r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pce == e1 + 1
          && (if pc < em then NI.NestInvMinRE(mn1, qid0, r1, code, pcb, em, pc, cc, qc, mx)
              else if pc == em then true
              else if em + 1 <= pc < e1 then
                AI.get_idx(qc, qid0) >= mx
                && NI.NestInvRE(r1, code, em + 1, e1, pc, cc, qc, AI.get_idx(qc, qid0))
              else AI.get_idx(qc, qid0) >= mx);
        NR.NfaRepIncrMinRE(mn1, qid0, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          TrueStampSiteMin(mn1, qid0, r1, code, pcb, em, pc, cc, qc, mx, qid);
        } else if pc == em {
          assert false;                             // the last-copy clock-mark stamps FALSE
        } else if em + 1 <= pc < e1 {
          var qv := AI.get_idx(qc, qid0);
          TrueStampSite(r1, code, em + 1, e1, pc, cc, qc, qv, qid);
        } else {
          assert pc == e1;
          assert false;                             // Fork is not SetQuantToClock
        }
        if (qid as int) == qid0 {
          assert qid in PIV.QuantIds(re);           // PathPresentQ base case
        } else {
          assert (qid0 as nat) != qid;
          assert qid in PIV.QuantIds(r1);
          assert AI.get_idx(qc, qid0) >= mx;        // ancestor clause
        }
        return;
      }
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid0, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
        && pce == e1 + 2
        && if pc == pcb || pc == pcb + 1 then true
           else if pc == pcb + 2 then
             AI.get_idx(qc, qid0) >= mx && NI.AllStaleRE(r1, cc, AI.get_idx(qc, qid0))
           else if pcb + 3 <= pc < e1 then
             AI.get_idx(qc, qid0) >= mx
             && NI.NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid0))
           else AI.get_idx(qc, qid0) >= mx;
      if pc == pcb + 1 || pc == pcb || pc == pcb + 2 || pc == e1 || pc == e1 + 1 {
        assert false;                               // Fork/mark(false)/BeginLoop/EndLoop/Jmp
      } else {
        assert pcb + 3 <= pc < e1;
        var qv := AI.get_idx(qc, qid0);
        TrueStampSite(r1, code, pcb + 3, e1, pc, cc, qc, qv, qid);
        assert (qid0 as nat) != qid by { assert (qid0 as nat) !in PIV.QuantIds(r1); }  // QuantUnique
        assert qv >= mx;
      }
    case Re_capture(cid, r1) =>
      assert {:split_here} true;   // (2026-09-05) per-arm batch under z3 4.14
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && if pc == pcb then
             (AI.get_idx(cc, CP.start_reg(cid)) < mx || AI.get_idx(cc, CP.start_reg(cid)) < 0)
             && NI.AllStaleRE(r1, cc, mx)
           else
             AI.get_idx(cc, CP.start_reg(cid)) >= mx
             && AI.get_idx(cc, CP.start_reg(cid)) >= 0
             && (pcb + 1 <= pc < e1 ==> NI.NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      if pc == pcb || pc == e1 {
        assert false;                               // SetRegisterToCP ≠ SetQuantToClock
      } else {
        assert pcb + 1 <= pc < e1;
        TrueStampSite(r1, code, pcb + 1, e1, pc, cc, qc, mx, qid);
        // ancestor clause of PathPresentQ: own start fresh.
      }
    case Re_lookaround(_, _, _) =>
      assert {:split_here} true;   // (2026-09-05) per-arm batch under z3 4.14
    case Re_anchor(_) =>
      assert {:split_here} true;   // (2026-09-05) per-arm batch under z3 4.14
  }

  /** The clock side of the true stamp: `q0`'s clock becomes the freshest
      value `clk`, every other clock is unchanged. */
  ghost predicate TrueStampClocks(qc: seq<int>, qc': seq<int>, q0: nat, clk: int) {
    (forall k: int :: k != q0 as int ==> AI.get_idx(qc', k) == AI.get_idx(qc, k))
    && AI.get_idx(qc', q0) == clk
    && (forall k: int :: AI.get_idx(qc, k) < clk)
  }

  lemma TrueStampBackMin(k: nat, qn: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                         cc: seq<int>, qc: seq<int>, qc': seq<int>, mx: int, q0: nat, clk: int)
    returns (fx: int)
    requires NR.NfaRepMinRE(k, qn, r1, code, pcb, pce)
    requires PIV.CapUnique(r1) && PIV.QuantUnique(r1)
    requires qn >= 0 && (qn as nat) !in PIV.QuantIds(r1)
    requires pcb <= pc < pce
    requires NI.NestInvMinRE(k, qn, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q0 as int, true))
    requires TrueStampClocks(qc, qc', q0, clk) && mx < clk
    ensures q0 in PIV.QuantIds(r1)
    ensures pcb <= pc - 1 && NI.NestInvMinRE(k, qn, r1, code, pcb, pce, pc - 1, cc, qc', mx)
    ensures NR.GetPcRE(code, pc - 1) == Some(RB.Fork(fx, pc + 1))
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qn, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qn, r1, code, e1, pce)
      && (if pc == pcb then true
          else if pcb + 1 <= pc < e1 then
            AI.get_idx(qc, qn) >= mx
            && NI.NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, AI.get_idx(qc, qn))
          else NI.NestInvMinRE(k - 1, qn, r1, code, e1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qn, r1, code, e1, pce);
    if pc == pcb {
      assert {:split_here} true;
      assert false;                                 // the copy head stamps FALSE
    } else if pcb + 1 <= pc < e1 {
      assert {:split_here} true;
      var qv := AI.get_idx(qc, qn);
      fx := TrueStampBackRE(r1, code, pcb + 1, e1, pc, cc, qc, qc', qv, q0, clk);
      assert qn != q0 as int;
      assert AI.get_idx(qc', qn) == qv;
      assert NI.NestInvMinRE(k, qn, r1, code, pcb, pce, pc - 1, cc, qc', mx);
    } else {
      assert {:split_here} true;
      fx := TrueStampBackMin(k - 1, qn, r1, code, e1, pce, pc, cc, qc, qc', mx, q0, clk);
      assert NI.NestInvMinRE(k, qn, r1, code, pcb, pce, pc - 1, cc, qc', mx);
    }
  }

  lemma TrueStampBackOpt(k: nat, greedy: bool, qn: R.quantid, r1: R.regex, code: RB.code,
                         pcb: nat, pce: nat, pc: nat,
                         cc: seq<int>, qc: seq<int>, qc': seq<int>, mx: int, q0: nat, clk: int)
    returns (fx: int)
    requires NR.NfaRepOptRE(k, greedy, qn, r1, code, pcb, pce)
    requires PIV.CapUnique(r1) && PIV.QuantUnique(r1)
    requires qn >= 0 && (qn as nat) !in PIV.QuantIds(r1)
    requires pcb <= pc < pce
    requires NI.NestInvOptRE(k, greedy, qn, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q0 as int, true))
    requires TrueStampClocks(qc, qc', q0, clk) && mx < clk
    ensures q0 in PIV.QuantIds(r1)
    ensures pcb <= pc - 1 && NI.NestInvOptRE(k, greedy, qn, r1, code, pcb, pce, pc - 1, cc, qc', mx)
    ensures NR.GetPcRE(code, pc - 1) == Some(RB.Fork(fx, pc + 1))
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qn, false))
      && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, pcb + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qn, r1, code, e1 + 1, pce)
      && (if pc == pcb || pc == pcb + 1 then true
          else if pc == pcb + 2 then
            AI.get_idx(qc, qn) >= mx && NI.AllStaleRE(r1, cc, AI.get_idx(qc, qn))
          else if pcb + 3 <= pc < e1 then
            AI.get_idx(qc, qn) >= mx
            && NI.NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qn))
          else if pc == e1 then AI.get_idx(qc, qn) >= mx
          else NI.NestInvOptRE(k - 1, greedy, qn, r1, code, e1 + 1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qn, r1, code, e1 + 1, pce);
    if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 {
      assert {:split_here} true;
      assert false;                                 // Fork / mark(false) / BeginLoop / EndLoop
    } else if pcb + 3 <= pc < e1 {
      assert {:split_here} true;
      var qv := AI.get_idx(qc, qn);
      fx := TrueStampBackRE(r1, code, pcb + 3, e1, pc, cc, qc, qc', qv, q0, clk);
      assert qn != q0 as int;
      assert AI.get_idx(qc', qn) == qv;
      assert NI.NestInvOptRE(k, greedy, qn, r1, code, pcb, pce, pc - 1, cc, qc', mx);
    } else {
      assert {:split_here} true;
      fx := TrueStampBackOpt(k - 1, greedy, qn, r1, code, e1 + 1, pce, pc, cc, qc, qc', mx, q0, clk);
      assert NI.NestInvOptRE(k, greedy, qn, r1, code, pcb, pce, pc - 1, cc, qc', mx);
    }
  }

  /** The true-stamp thread re-positioned to the end fork under the new
      clocks (see the section comment). */
  lemma TrueStampBackRE(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                        cc: seq<int>, qc: seq<int>, qc': seq<int>, mx: int, q0: nat, clk: int)
    returns (fx: int)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NI.NestInvRE(re, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q0 as int, true))
    requires TrueStampClocks(qc, qc', q0, clk) && mx < clk
    ensures q0 in PIV.QuantIds(re)
    ensures pcb <= pc - 1 && NI.NestInvRE(re, code, pcb, pce, pc - 1, cc, qc', mx)
    ensures NR.GetPcRE(code, pc - 1) == Some(RB.Fork(fx, pc + 1))
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
      NR.NfaRepIncrRE(re, code, pcb, pce);
      assert false;
    case Re_character(ch) =>
      assert {:split_here} true;
      assert pc == pcb;
      assert false;
    case Re_anchor(_) =>
      assert {:split_here} true;
      assert pc == pcb;
      assert false;
    case Re_lookaround(_, _, _) =>
      assert {:split_here} true;
      assert pc == pcb;
      assert false;
    case Re_alt(r1, r2) =>
      assert {:split_here} true;
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && if pc == pcb then NI.AllStaleRE(r1, cc, mx) && NI.AllStaleRE(r2, cc, mx)
           else if pcb + 1 <= pc < e1 then
             NI.NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx) && NI.AllStaleRE(r2, cc, mx)
           else if pc == e1 then true
           else NI.NestInvRE(r2, code, e1 + 1, pce, pc, cc, qc, mx);
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, pce);
      if pc == pcb || pc == e1 {
        assert false;                               // Fork / Jmp
      } else if pcb + 1 <= pc < e1 {
        fx := TrueStampBackRE(r1, code, pcb + 1, e1, pc, cc, qc, qc', mx, q0, clk);
        assert NI.NestInvRE(re, code, pcb, pce, pc - 1, cc, qc', mx);
      } else {
        fx := TrueStampBackRE(r2, code, e1 + 1, pce, pc, cc, qc, qc', mx, q0, clk);
        assert NI.NestInvRE(re, code, pcb, pce, pc - 1, cc, qc', mx);
      }
    case Re_con(r1, r2) =>
      assert {:split_here} true;
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && if pc < e1 then NI.NestInvRE(r1, code, pcb, e1, pc, cc, qc, mx) && NI.AllStaleRE(r2, cc, mx)
           else NI.NestInvRE(r2, code, e1, pce, pc, cc, qc, mx);
      NR.NfaRepIncrRE(r1, code, pcb, e1);
      NR.NfaRepIncrRE(r2, code, e1, pce);
      if pc < e1 {
        fx := TrueStampBackRE(r1, code, pcb, e1, pc, cc, qc, qc', mx, q0, clk);
        assert NI.NestInvRE(re, code, pcb, pce, pc - 1, cc, qc', mx);
      } else {
        fx := TrueStampBackRE(r2, code, e1, pce, pc, cc, qc, qc', mx, q0, clk);
        assert NI.NestInvRE(re, code, pcb, pce, pc - 1, cc, qc', mx);
      }
    case Re_capture(cid, r1) =>
      assert {:split_here} true;
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && if pc == pcb then
             (AI.get_idx(cc, CP.start_reg(cid)) < mx || AI.get_idx(cc, CP.start_reg(cid)) < 0)
             && NI.AllStaleRE(r1, cc, mx)
           else
             AI.get_idx(cc, CP.start_reg(cid)) >= mx
             && AI.get_idx(cc, CP.start_reg(cid)) >= 0
             && (pcb + 1 <= pc < e1 ==> NI.NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      if pc == pcb || pc == e1 {
        assert false;                               // SetRegisterToCP
      } else {
        fx := TrueStampBackRE(r1, code, pcb + 1, e1, pc, cc, qc, qc', mx, q0, clk);
        assert NI.NestInvRE(re, code, pcb, pce, pc - 1, cc, qc', mx);
      }
    case Re_quant(nul, qid0, q, r1) =>
      assert {:split_here} true;
      assert qid0 >= 0 && (qid0 as nat) !in PIV.QuantIds(r1);   // QuantUnique
      if q.max.Some? {
        assert {:split_here} true;
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid0, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid0, r1, code, em, pce)
          && (if pc < em then NI.NestInvMinRE(mn, qid0, r1, code, pcb, em, pc, cc, qc, mx)
              else NI.NestInvOptRE(kx, q.greedy, qid0, r1, code, em, pce, pc, cc, qc, mx));
        NR.NfaRepIncrMinRE(mn, qid0, r1, code, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid0, r1, code, em, pce);
        if pc < em {
          fx := TrueStampBackMin(mn, qid0, r1, code, pcb, em, pc, cc, qc, qc', mx, q0, clk);
        } else {
          fx := TrueStampBackOpt(kx, q.greedy, qid0, r1, code, em, pce, pc, cc, qc, qc', mx, q0, clk);
          assert pc - 1 >= em;      // an Opt layer's first site is its fork, not a stamp
        }
        assert NI.NestInvRE(re, code, pcb, pce, pc - 1, cc, qc', mx);
        return;
      }
      if !(q.min == 0 && q.max == None) && nul != R.NonNullable && !q.greedy {
        assert {:split_here} true;
        var mn := q.min as nat;
        var em, e1 := NI.NestInvGenREInv(nul, qid0, q, r1, code, pcb, pce, pc, cc, qc, mx);
        NR.NfaRepIncrMinRE(mn, qid0, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          fx := TrueStampBackMin(mn, qid0, r1, code, pcb, em, pc, cc, qc, qc', mx, q0, clk);
          NI.NestInvGenREIntro(nul, qid0, q, r1, code, pcb, pce, pc - 1, cc, qc', mx, em, e1);
        } else if em + 3 <= pc < e1 {
          var qv := AI.get_idx(qc, qid0);
          fx := TrueStampBackRE(r1, code, em + 3, e1, pc, cc, qc, qc', qv, q0, clk);
          assert AI.get_idx(qc', qid0) == qv;
          NI.NestInvGenREIntro(nul, qid0, q, r1, code, pcb, pce, pc - 1, cc, qc', mx, em, e1);
        } else {
          assert false;                             // Fork/mark(false)/BeginLoop/EndLoop/Jmp
        }
        return;
      }
      if !(q.min == 0 && q.max == None) && nul != R.NonNullable {
        assert {:split_here} true;
        var mn1 := (q.min - 1) as nat;
        var em, e1 := NI.NestInvCinREInv(nul, qid0, q, r1, code, pcb, pce, pc, cc, qc, mx);
        NR.NfaRepIncrMinRE(mn1, qid0, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          fx := TrueStampBackMin(mn1, qid0, r1, code, pcb, em, pc, cc, qc, qc', mx, q0, clk);
          NI.NestInvCinREIntro(nul, qid0, q, r1, code, pcb, pce, pc - 1, cc, qc', mx, em, e1);
        } else if em + 3 <= pc < e1 {
          var qv := AI.get_idx(qc, qid0);
          fx := TrueStampBackRE(r1, code, em + 3, e1, pc, cc, qc, qc', qv, q0, clk);
          assert AI.get_idx(qc', qid0) == qv;
          NI.NestInvCinREIntro(nul, qid0, q, r1, code, pcb, pce, pc - 1, cc, qc', mx, em, e1);
        } else if pc == e1 + 2 {
          // THE BASE CASE: q0's own true stamp; the end fork's claim holds for
          // the fresh clock.
          assert qid0 == q0 as int;
          assert AI.get_idx(qc', qid0) == clk >= mx;
          fx := em + 1;
          NI.NestInvCinREIntro(nul, qid0, q, r1, code, pcb, pce, pc - 1, cc, qc', mx, em, e1);
        } else {
          assert false;                             // Fork/mark(false)/BeginLoop/EndLoop/end fork
        }
        return;
      }
      if !(q.min == 0 && q.max == None) {
        assert {:split_here} true;
        var mn1 := (q.min - 1) as nat;
        var em: nat, e1: nat :|
          NR.NfaRepMinRE(mn1, qid0, r1, code, pcb, em)
          && NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid0, false))
          && NR.NfaRepRE(r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pce == e1 + 1
          && (if pc < em then NI.NestInvMinRE(mn1, qid0, r1, code, pcb, em, pc, cc, qc, mx)
              else if pc == em then true
              else if em + 1 <= pc < e1 then
                AI.get_idx(qc, qid0) >= mx
                && NI.NestInvRE(r1, code, em + 1, e1, pc, cc, qc, AI.get_idx(qc, qid0))
              else AI.get_idx(qc, qid0) >= mx);
        NR.NfaRepIncrMinRE(mn1, qid0, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          fx := TrueStampBackMin(mn1, qid0, r1, code, pcb, em, pc, cc, qc, qc', mx, q0, clk);
        } else if em + 1 <= pc < e1 {
          var qv := AI.get_idx(qc, qid0);
          fx := TrueStampBackRE(r1, code, em + 1, e1, pc, cc, qc, qc', qv, q0, clk);
          assert AI.get_idx(qc', qid0) == qv;
        } else {
          assert false;                             // the mark(false) / the backward fork
        }
        assert NI.NestInvRE(re, code, pcb, pce, pc - 1, cc, qc', mx);
        return;
      }
      // the star
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid0, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
        && pce == e1 + 2
        && if pc == pcb || pc == pcb + 1 then true
           else if pc == pcb + 2 then
             AI.get_idx(qc, qid0) >= mx && NI.AllStaleRE(r1, cc, AI.get_idx(qc, qid0))
           else if pcb + 3 <= pc < e1 then
             AI.get_idx(qc, qid0) >= mx
             && NI.NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid0))
           else AI.get_idx(qc, qid0) >= mx;
      NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
      if pcb + 3 <= pc < e1 {
        var qv := AI.get_idx(qc, qid0);
        fx := TrueStampBackRE(r1, code, pcb + 3, e1, pc, cc, qc, qc', qv, q0, clk);
        assert AI.get_idx(qc', qid0) == qv;
        assert NI.NestInvRE(re, code, pcb, pce, pc - 1, cc, qc', mx);
      } else {
        assert false;                               // Fork/mark(false)/BeginLoop/EndLoop/Jmp
      }
  }

  /** THE CLOCK SIDE OF THE TRUE STAMP at top level: the successor at `pc + 1`
      satisfies `NI.NestTopRE` under the new clocks, and the site is a
      present, outside-look quantifier (`PathPresentQ` under the OLD clocks). */
  lemma NestInvTopTrueStamp(re: R.regex, code: RB.code, endl: nat, pc: nat,
                            cc: seq<int>, qc: seq<int>, qc': seq<int>, q0: int, clk: int)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires pc < endl
    requires NI.NestTopRE(re, code, endl, pc, cc, qc)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q0, true))
    requires q0 >= 0 ==> TrueStampClocks(qc, qc', q0 as nat, clk)
    requires clk >= 0
    ensures q0 >= 0 && (q0 as nat) in PIV.QuantIds(re) && (q0 as nat) in PIV.QuantIdsOutsideLooks(re)
    ensures PIV.PathPresentQ(re, cc, qc, -1, q0 as nat)
    ensures pc + 1 <= endl && NI.NestTopRE(re, code, endl, pc + 1, cc, qc')
  {
    assert NI.NestInvRE(re, code, 0, endl, pc, cc, qc, -1);
    assert q0 >= 0 by { NI.CodeShapeAt(re, code, 0, endl, pc); }
    var q: nat := q0 as nat;
    TrueStampSite(re, code, 0, endl, pc, cc, qc, -1, q);
    var fx := TrueStampBackRE(re, code, 0, endl, pc, cc, qc, qc', -1, q, clk);
    assert NI.StepEdgeRE(code, pc - 1, pc + 1);
    NI.NestInvAdvance(re, code, 0, endl, pc - 1, pc + 1, cc, qc', -1);
  }

}
