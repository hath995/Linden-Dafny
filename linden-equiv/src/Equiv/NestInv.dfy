// Phase 4b: the POSITIONAL (nesting) invariant — the last unproven ingredient
// of the preservation induction. NestInvRE locates a thread's pc inside the
// compiled block structure (NfaRepRE's layout) and threads the enclosing-star
// stamp `mx` down the recursion exactly like filter_capture does:
//
//   - quant node, pc past the stamp site: qc[qid] >= mx (the stamp chain),
//     recurse into the body with mx := qc[qid];
//   - capture node, pc AT its open site: own start stale-or-unset + body
//     AllStale w.r.t. mx — exactly GmOfLiveOpenGMOpen's positional hypotheses;
//   - capture node, pc inside its body: own start fresh (>= mx, >= 0) —
//     exactly PathPresent's ancestor clause;
//   - structures not yet reached this iteration: AllStale — re-armed FOR FREE
//     by the clock backbone at every stamp (new stamp S+1 > all stored <= S).
//
// The key layout fact making this work: a star compiles to
//   Fork; SetQuantToClock; BeginLoop; body; EndLoop; Jmp(back)
// so EVERY entry into the body passes through the stamp — freshness of the
// stamp chain is structural, not historical.
include "PikeInvRE.dfy"

/** Phase 4b: the POSITIONAL (nesting) invariant `NestInvRE` — locates a
    thread's `pc` inside the compiled block structure (`NfaRepRE`'s layout)
    and threads the enclosing-star stamp `mx` down the recursion exactly as
    `filter_capture` does. This is what lets a fresh quant/capture-open write
    reset every stale descendant "for free" via the clock backbone, and is the
    last unproven ingredient of the `PikeInvRE` preservation induction. */
module LindenElkNestInv {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import NR = LindenElkNfaRep
  import AI = ArrayInterp
  import AReg = Array_Regs
  import PIV = LindenElkPikeInv
  import AR = LindenElkActionsRep
  import LTB = LindenElkLookTables

  // Every capture start clock in re is stale (below M) or unset.
  /** Every capture start clock inside `re` is either stale (below `M`) or
      unset — the staleness side-condition `filter_capture` needs to treat a
      subtree as entirely reset. */
  ghost predicate AllStaleRE(re: R.regex, cc: seq<int>, M: int) {
    forall g: nat :: g in PIV.CapIds(re)
      ==> AI.get_idx(cc, CP.start_reg(g)) < M || AI.get_idx(cc, CP.start_reg(g)) < 0
  }

  /** Staleness w.r.t. `M` persists under any looser (larger) threshold `M'`. */
  lemma AllStaleWeaken(re: R.regex, cc: seq<int>, M: int, M': int)
    requires AllStaleRE(re, cc, M) && M <= M'
    ensures AllStaleRE(re, cc, M')
  {}

  // NfaRepRE end labels are unique given (re, code, start): every case's
  // internal split is pinned by an instruction value or by the sub-regex's own
  // determinism.
  /** `NfaRepRE`'s end label is unique for a given `(re, code, start)`: two
      derivations of the same block must agree on where it ends. */
  /** `NfaRepDetermRE` for forced-copy chains: the body end is pinned by the
      body's own determinism, then the tails agree by induction. */
  lemma NfaRepDetermMinRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, e: nat, e': nat)
    requires NR.NfaRepMinRE(k, qid, r1, code, start, e)
    requires NR.NfaRepMinRE(k, qid, r1, code, start, e')
    ensures e == e'
    decreases CP.rsize(r1), k + 2
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, e);
      var e1': nat :| NR.GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
        && NR.NfaRepRE(r1, code, start + 1, e1')
        && NR.NfaRepMinRE(k - 1, qid, r1, code, e1', e');
      NfaRepDetermRE(r1, code, start + 1, e1, e1');
      NfaRepDetermMinRE(k - 1, qid, r1, code, e1, e, e');
    }
  }

  /** `NfaRepDetermRE` for optional-layer chains: for `k > 0` the layer's fork
      instruction pins the common end directly. */
  lemma NfaRepDetermOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, e: nat, e': nat)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, start, e)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, start, e')
    ensures e == e'
    decreases CP.rsize(r1), k + 2
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, e) else RB.Fork(e, start + 1))
        && NR.NfaRepRE(r1, code, start + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, e);
      var e1': nat :| NR.GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, e') else RB.Fork(e', start + 1))
        && NR.NfaRepRE(r1, code, start + 3, e1')
        && NR.GetPcRE(code, e1') == Some(RB.EndLoop)
        && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1' + 1, e');
      assert e == e';                   // pinned by the Fork instruction value
    }
  }

  lemma NfaRepDetermRE(re: R.regex, code: RB.code, start: nat, e: nat, e': nat)
    requires NR.NfaRepRE(re, code, start, e)
    requires NR.NfaRepRE(re, code, start, e')
    ensures e == e'
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(e))
        && NR.NfaRepRE(r2, code, e1 + 1, e);
      var e1': nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1' + 1))
        && NR.NfaRepRE(r1, code, start + 1, e1')
        && NR.GetPcRE(code, e1') == Some(RB.Jmp(e'))
        && NR.NfaRepRE(r2, code, e1' + 1, e');
      assert e1 == e1';               // pinned by the Fork instruction value
      assert e == e';                 // pinned by the Jmp instruction value
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, e);
      var e1': nat :| NR.NfaRepRE(r1, code, start, e1') && NR.NfaRepRE(r2, code, e1', e');
      NfaRepDetermRE(r1, code, start, e1, e1');
      NfaRepDetermRE(r2, code, e1, e, e');
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| NR.GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
          && NR.NfaRepRE(r1, code, start + 3, e1) && e == e1 + 2;
        var e1': nat :| NR.GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, e1' + 2) else RB.Fork(e1' + 2, start + 1))
          && NR.NfaRepRE(r1, code, start + 3, e1') && e' == e1' + 2;
        assert e1 == e1';             // pinned by the Fork instruction value
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, e);
        var em' := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, e');
        NfaRepDetermMinRE(q.min as nat, qid, r1, code, start, em, em');
        NfaRepDetermOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, e, e');
      } else {
        var em, be := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, e);
        var em', be' := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, e');
        NfaRepDetermMinRE((q.min - 1) as nat, qid, r1, code, start, em, em');
        NfaRepDetermRE(r1, code, em + 1, be, be');
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start + 1, e1) && e == e1 + 1;
      var e1': nat :| NR.NfaRepRE(r1, code, start + 1, e1') && e' == e1' + 1;
      NfaRepDetermRE(r1, code, start + 1, e1, e1');
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
  }

  // =========================================================================
  // The nesting invariant. pc is located strictly inside re's block
  // [pcb, pce); mx is the innermost enclosing star's current stamp (-1 at
  // top). Dispatch mirrors NfaRepRE's layout; claims are exactly what the
  // write-site discharge lemmas need, threaded so that every conjunct is
  // (a) local to the path from the block entry to pc, and (b) re-armable by
  // the clock backbone at stamps.
  // =========================================================================
  /** The nesting invariant. `pc` sits strictly inside `re`'s compiled block
      `[pcb, pce)`; `mx` is the innermost enclosing star's current clock stamp
      (`-1` at top level). Dispatches on `re`'s shape mirroring `NfaRepRE`'s own
      layout, and at each site states exactly the positional fact the
      write-site discharge lemmas (`NestInvOpenSite`, `NestInvStamp`,
      `NestInvOpenWrite`, `NestInvResetSite`) need: which captures/quants are
      open, fresh, or provably stale from `mx`. */
  /** The nesting invariant for a forced-copy chain (`NfaRepMinRE`): the copy
      head (the stamp site) claims nothing; inside a copy body the chain claims
      the stamp beats `mx` and threads the body invariant at the stamp, exactly
      like the star's body case. */
  ghost predicate NestInvMinRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code,
                               pcb: nat, pce: nat, pc: nat,
                               cc: seq<int>, qc: seq<int>, mx: int)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    decreases CP.rsize(r1), k + 2
  {
    k > 0 ==>
    var body := pcb + 1;
    var rest := k - 1;
    exists e1: nat ::
      NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, body, e1)
      && NR.NfaRepMinRE(rest, qid, r1, code, e1, pce)
      && if pc == pcb then true                          // stamp site: no claims yet
         else if pcb + 1 <= pc < e1 then                 // inside this copy's body
           AI.get_idx(qc, qid) >= mx
           && NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, AI.get_idx(qc, qid))
         else NestInvMinRE(k - 1, qid, r1, code, e1, pce, pc, cc, qc, mx)
  }

  /** The nesting invariant for an optional-layer chain (`NfaRepOptRE`): each
      layer mirrors the star's claims — fork/stamp sites claim nothing,
      `BeginLoop` claims the fresh stamp re-armed the body, the body threads
      `NestInvRE` at the stamp, `EndLoop` keeps the stamp-chain claim. */
  ghost predicate NestInvOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                               pcb: nat, pce: nat, pc: nat,
                               cc: seq<int>, qc: seq<int>, mx: int)
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
      && if pc == pcb || pc == pcb + 1 then true         // fork / stamp site: no claims yet
         else if pc == pcb + 2 then                      // BeginLoop: stamped, body pending
           AI.get_idx(qc, qid) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qid))
         else if pcb + 3 <= pc < e1 then                 // inside the body
           AI.get_idx(qc, qid) >= mx
           && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid))
         else if pc == e1 then AI.get_idx(qc, qid) >= mx // EndLoop: body done
         else NestInvOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, cc, qc, mx)
  }

  ghost predicate NestInvRE(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                            cc: seq<int>, qc: seq<int>, mx: int)
    requires NR.NfaRepRE(re, code, pcb, pce)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty => true             // no pc strictly inside an empty block
    case Re_character(_) => true      // pc == pcb (the Consume): no claims
    case Re_alt(r1, r2) =>
      exists e1: nat ::
        NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && if pc == pcb then AllStaleRE(r1, cc, mx) && AllStaleRE(r2, cc, mx)
           else if pcb + 1 <= pc < e1 then
             NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else if pc == e1 then true                     // the join Jmp: both sides done or bypassed
           else NestInvRE(r2, code, e1 + 1, pce, pc, cc, qc, mx)
    case Re_con(r1, r2) =>
      exists e1: nat ::
        NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && if pc < e1 then NestInvRE(r1, code, pcb, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else NestInvRE(r2, code, e1, pce, pc, cc, qc, mx)
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None then
        // the star: fast-path arm, kept verbatim
        exists e1: nat ::
          NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
          && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, code, pcb + 3, e1)
          && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
          && pce == e1 + 2
          && if pc == pcb || pc == pcb + 1 then true      // fork / stamp site: no claims yet
             else if pc == pcb + 2 then                   // BeginLoop: stamped, body pending
               AI.get_idx(qc, qid) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qid))
             else if pcb + 3 <= pc < e1 then              // inside the body
               AI.get_idx(qc, qid) >= mx
               && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid))
             else AI.get_idx(qc, qid) >= mx               // EndLoop or back-Jmp: body done
      else if q.max.Some? then
        // bounded {min,max}: the claims live in the chain invariants
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        exists em: nat ::
          NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid, r1, code, em, pce)
          && if pc < em then NestInvMinRE(mn, qid, r1, code, pcb, em, pc, cc, qc, mx)
             else NestInvOptRE(kx, q.greedy, qid, r1, code, em, pce, pc, cc, qc, mx)
      else
        // the do-while (+/{n,}): a Min copy's claims at the last stamp, then
        // the star body's claims, then the backward fork
        var mn1 := (q.min - 1) as nat;
        exists em: nat, e1: nat ::
          NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
          && NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
          && NR.NfaRepRE(r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pce == e1 + 1
          && if pc < em then NestInvMinRE(mn1, qid, r1, code, pcb, em, pc, cc, qc, mx)
             else if pc == em then true                       // the stamp site: no claims yet
             else if em + 1 <= pc < e1 then                   // inside the guaranteed body
               AI.get_idx(qc, qid) >= mx
               && NestInvRE(r1, code, em + 1, e1, pc, cc, qc, AI.get_idx(qc, qid))
             else AI.get_idx(qc, qid) >= mx                   // the backward fork: body done
    case Re_capture(cid, r1) =>
      exists e1: nat ::
        NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && if pc == pcb then                              // the OPEN site
             (AI.get_idx(cc, CP.start_reg(cid)) < mx || AI.get_idx(cc, CP.start_reg(cid)) < 0)
             && AllStaleRE(r1, cc, mx)
           else                                           // inside body or at the close site
             AI.get_idx(cc, CP.start_reg(cid)) >= mx
             && AI.get_idx(cc, CP.start_reg(cid)) >= 0
             && (pcb + 1 <= pc < e1 ==> NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx))
    case Re_lookaround(_, _, _) => true  // pc == pcb (the oracle check): no claims
    case Re_anchor(_) => true         // pc == pcb (the AnchorAssertion): no claims
  }

  // =========================================================================
  // Block-entry introduction: arriving at a block whose whole subtree is
  // stale w.r.t. mx satisfies the invariant at the entry pc. This is how
  // fall-through/fork edges INTO a block discharge the entry claims (the
  // parent's AllStale conjunct feeds it).
  // =========================================================================
  /** Arriving at a block whose whole subtree is stale w.r.t. `mx`
      (`AllStaleRE`) satisfies `NestInvRE` at the block's entry `pc` — how a
      fall-through/fork edge INTO a block discharges the invariant there. */
  /** Entering a forced-copy chain at its head satisfies the chain invariant
      there (the head is a stamp site: no claims). */
  lemma NestMinEntryRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat,
                       cc: seq<int>, qc: seq<int>, mx: int)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    ensures NestInvMinRE(k, qid, r1, code, pcb, pce, pcb, cc, qc, mx)
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce);
    }
  }

  /** Entering an optional-layer chain at its head satisfies the chain
      invariant there (the head is a fork site: no claims). */
  lemma NestOptEntryRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat,
                       cc: seq<int>, qc: seq<int>, mx: int)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    ensures NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pcb, cc, qc, mx)
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
      NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
      assert pcb < pcb + 1;             // entry is the fork, not past it
    }
  }

  lemma NestEntryRE(re: R.regex, code: RB.code, pcb: nat, pce: nat,
                    cc: seq<int>, qc: seq<int>, mx: int)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires AllStaleRE(re, cc, mx)
    ensures NestInvRE(re, code, pcb, pce, pcb, cc, qc, mx)
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
      assert AllStaleRE(r1, cc, mx) && AllStaleRE(r2, cc, mx);
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce);
      if pcb < e1 {
        NestEntryRE(r1, code, pcb, e1, cc, qc, mx);
        assert AllStaleRE(r2, cc, mx);
      } else {
        // r1's block is empty (e1 == pcb): the entry belongs to r2.
        NR.NfaRepIncrRE(r1, code, pcb, e1);
        assert e1 == pcb;
        NestEntryRE(r2, code, e1, pce, cc, qc, mx);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        // entry pc == pcb is the fork: no claims.
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, pcb, pce);
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        if pcb < em {
          NestMinEntryRE(mn, qid, r1, code, pcb, em, cc, qc, mx);
        } else {
          NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
          assert em == pcb;
          NestOptEntryRE(kx, q.greedy, qid, r1, code, em, pce, cc, qc, mx);
        }
      } else {
        // the do-while: entry is a Min copy head or the last stamp - no claims
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, pcb, pce);
        var mn1 := (q.min - 1) as nat;
        if pcb < em {
          NestMinEntryRE(mn1, qid, r1, code, pcb, em, cc, qc, mx);
        } else {
          NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
          assert em == pcb;
          // the stamp site: no claims
        }
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1;
      if cid >= 0 {
        assert (cid as nat) in PIV.CapIds(re);
        assert AI.get_idx(cc, CP.start_reg(cid)) < mx || AI.get_idx(cc, CP.start_reg(cid)) < 0;
      } else {
        assert CP.start_reg(cid) < 0;                 // negative slot reads as -1
        assert AI.get_idx(cc, CP.start_reg(cid)) == -1;
      }
      assert AllStaleRE(r1, cc, mx);
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
  }

  // =========================================================================
  // Top-level wrapper and initial establishment: at pc 0 with fresh registers
  // the whole regex is untouched (init clocks are -1 < any mx bound; the
  // -1-threshold disjunct `< 0` carries it).
  // =========================================================================
  /** The top-level wrapper of `NestInvRE`: either `pc` is the `Accept`
      terminator (no claims), or `NestInvRE` holds with the top-level threshold
      `mx == -1`. */
  ghost predicate NestTopRE(re: R.regex, code: RB.code, endl: nat, pc: nat,
                            cc: seq<int>, qc: seq<int>)
    requires NR.NfaRepRE(re, code, 0, endl)
  {
    pc == endl                                    // at the Accept terminator: no claims
    || (pc < endl && NestInvRE(re, code, 0, endl, pc, cc, qc, -1))
  }

  /** At `pc == 0` with freshly-initialized (all `< 0`) clocks, `NestTopRE`
      holds — the invariant's base case at the start of a match attempt. */
  lemma NestTopInit(re: R.regex, code: RB.code, endl: nat, cc: seq<int>, qc: seq<int>)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires forall k :: AI.get_idx(cc, k) < 0    // freshly-initialized clocks
    ensures NestTopRE(re, code, endl, 0, cc, qc)
  {
    if 0 < endl {
      assert AllStaleRE(re, cc, -1);
      NestEntryRE(re, code, 0, endl, cc, qc, -1);
    } else {
      NR.NfaRepIncrRE(re, code, 0, endl);
      assert endl == 0;
    }
  }

  /** A non-empty forced-copy chain occupies at least its head instruction. */
  lemma NfaRepMinPosRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat)
    requires k > 0
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    ensures pcb < pce
  {
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce);
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, pce);
  }

  /** A non-empty optional-layer chain occupies at least its head layer. */
  lemma NfaRepOptPosRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat)
    requires k > 0
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    ensures pcb + 3 < pce
  {
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, pcb + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
  }

  // =========================================================================
  // Site extraction: at a pc holding gid's OPEN instruction, the invariant's
  // path claims assemble into GmOfLiveOpenGMOpen's positional hypotheses —
  // PathPresent, own-start stale-or-unset, and body staleness, all phrased
  // against MxAtGid (whose threading NestInvRE's mx mirrors exactly).
  // =========================================================================
  /** At a `pc` holding capture `gid`'s OPEN instruction, `NestInvRE`'s path
      claims assemble into exactly `GmOfLiveOpenGMOpen`'s positional
      hypotheses: `gid` is a real capture id, `PathPresent` holds, `gid`'s own
      start is stale-or-unset, and its whole body is stale w.r.t.
      `MxAtGid`. */
  /** `NestInvOpenSite` for forced-copy chains: the open site sits inside some
      copy's body; the body invariant (thresholded at this quantifier's stamp)
      assembles the same positional hypotheses, phrased against the body. */
  lemma NestInvOpenSiteMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                           cc: seq<int>, qc: seq<int>, mx: int, gid: nat)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    requires PIV.CapUnique(r1)
    requires pcb <= pc < pce
    requires NestInvMinRE(k, qid, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid)))
    ensures gid in PIV.CapIds(r1)
    ensures gid !in PIV.CapIdsInLooks(r1)   // L3a: outside-look write site
    ensures AI.get_idx(qc, qid) >= mx
    ensures PIV.PathPresent(r1, cc, qc, AI.get_idx(qc, qid), gid)
    ensures AI.get_idx(cc, CP.start_reg(gid)) < PIV.MxAtGid(r1, cc, qc, AI.get_idx(qc, qid), gid)
         || AI.get_idx(cc, CP.start_reg(gid)) < 0
    ensures forall sg: nat :: (sg in PIV.CapIds(PIV.BodyOf(r1, gid))
         ==> (AI.get_idx(cc, CP.start_reg(sg)) < PIV.MxAtGid(r1, cc, qc, AI.get_idx(qc, qid), gid)
              || AI.get_idx(cc, CP.start_reg(sg)) < 0))
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce)
      && (if pc == pcb then true
          else if pcb + 1 <= pc < e1 then
            AI.get_idx(qc, qid) >= mx
            && NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, AI.get_idx(qc, qid))
          else NestInvMinRE(k - 1, qid, r1, code, e1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    if pc == pcb {
      assert false;                                 // SetQuantToClock ≠ SetRegisterToCP
    } else if pcb + 1 <= pc < e1 {
      var qv := AI.get_idx(qc, qid);
      NestInvOpenSite(r1, code, pcb + 1, e1, pc, cc, qc, qv, gid);
    } else {
      NestInvOpenSiteMin(k - 1, qid, r1, code, e1, pce, pc, cc, qc, mx, gid);
    }
  }

  /** `NestInvOpenSite` for optional-layer chains. */
  lemma NestInvOpenSiteOpt(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                           cc: seq<int>, qc: seq<int>, mx: int, gid: nat)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    requires PIV.CapUnique(r1)
    requires pcb <= pc < pce
    requires NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid)))
    ensures gid in PIV.CapIds(r1)
    ensures gid !in PIV.CapIdsInLooks(r1)   // L3a: outside-look write site
    ensures AI.get_idx(qc, qid) >= mx
    ensures PIV.PathPresent(r1, cc, qc, AI.get_idx(qc, qid), gid)
    ensures AI.get_idx(cc, CP.start_reg(gid)) < PIV.MxAtGid(r1, cc, qc, AI.get_idx(qc, qid), gid)
         || AI.get_idx(cc, CP.start_reg(gid)) < 0
    ensures forall sg: nat :: (sg in PIV.CapIds(PIV.BodyOf(r1, gid))
         ==> (AI.get_idx(cc, CP.start_reg(sg)) < PIV.MxAtGid(r1, cc, qc, AI.get_idx(qc, qid), gid)
              || AI.get_idx(cc, CP.start_reg(sg)) < 0))
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
          else if pc == pcb + 2 then
            AI.get_idx(qc, qid) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qid))
          else if pcb + 3 <= pc < e1 then
            AI.get_idx(qc, qid) >= mx
            && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid))
          else if pc == e1 then AI.get_idx(qc, qid) >= mx
          else NestInvOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 {
      assert false;                                 // Fork/SetQuantToClock/BeginLoop/EndLoop
    } else if pcb + 3 <= pc < e1 {
      var qv := AI.get_idx(qc, qid);
      NestInvOpenSite(r1, code, pcb + 3, e1, pc, cc, qc, qv, gid);
    } else {
      NestInvOpenSiteOpt(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, cc, qc, mx, gid);
    }
  }

  /** `CapIdsInLooks ⊆ CapIds`, contrapositive form: not a capture id at all ⇒
      not an inside-look capture id. */
  lemma InLooksNotIn(r: R.regex, g: nat)
    requires g !in PIV.CapIds(r)
    ensures g !in PIV.CapIdsInLooks(r)
  { PIV.CapIdsSplit(r); }

  /** The quant analog: not a quant id at all ⇒ not an inside-look quant id. */
  lemma QuantInLooksNotIn(r: R.regex, q: nat)
    requires q !in PIV.QuantIds(r)
    ensures q !in PIV.QuantIdsInLooks(r)
  { PIV.QuantIdsSplit(r); }

  lemma NestInvOpenSite(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                        cc: seq<int>, qc: seq<int>, mx: int, gid: nat)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.CapUnique(re)
    requires pcb <= pc < pce
    requires NestInvRE(re, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid)))
    ensures gid in PIV.CapIds(re)
    ensures gid !in PIV.CapIdsInLooks(re)   // L3a: SetRegisterToCP sites are outside-look (looks compile to CheckOracle)
    ensures PIV.PathPresent(re, cc, qc, mx, gid)
    ensures AI.get_idx(cc, CP.start_reg(gid)) < PIV.MxAtGid(re, cc, qc, mx, gid)
         || AI.get_idx(cc, CP.start_reg(gid)) < 0
    ensures forall sg: nat :: (sg in PIV.CapIds(PIV.BodyOf(re, gid))
         ==> (AI.get_idx(cc, CP.start_reg(sg)) < PIV.MxAtGid(re, cc, qc, mx, gid)
              || AI.get_idx(cc, CP.start_reg(sg)) < 0))
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
      // pcb == pce contradicts pcb <= pc < pce.
    case Re_character(ch) =>
      assert pc == pcb;
      assert false;                                 // Consume ≠ SetRegisterToCP
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && if pc == pcb then AllStaleRE(r1, cc, mx) && AllStaleRE(r2, cc, mx)
           else if pcb + 1 <= pc < e1 then
             NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else if pc == e1 then true
           else NestInvRE(r2, code, e1 + 1, pce, pc, cc, qc, mx);
      if pc == pcb {
        assert false;                               // Fork ≠ SetRegisterToCP
      } else if pcb + 1 <= pc < e1 {
        NestInvOpenSite(r1, code, pcb + 1, e1, pc, cc, qc, mx, gid);
        assert gid !in PIV.CapIds(r2) by {
          if gid in PIV.CapIds(r2) { assert gid in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
        InLooksNotIn(r2, gid);
        assert PIV.MxAtGid(re, cc, qc, mx, gid) == PIV.MxAtGid(r1, cc, qc, mx, gid);
        assert PIV.BodyOf(re, gid) == PIV.BodyOf(r1, gid);
      } else if pc == e1 {
        assert false;                               // Jmp ≠ SetRegisterToCP
      } else {
        NestInvOpenSite(r2, code, e1 + 1, pce, pc, cc, qc, mx, gid);
        assert gid !in PIV.CapIds(r1) by {
          if gid in PIV.CapIds(r1) { assert gid in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
        InLooksNotIn(r1, gid);
        assert PIV.MxAtGid(re, cc, qc, mx, gid) == PIV.MxAtGid(r2, cc, qc, mx, gid);
        assert PIV.BodyOf(re, gid) == PIV.BodyOf(r2, gid);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && if pc < e1 then NestInvRE(r1, code, pcb, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else NestInvRE(r2, code, e1, pce, pc, cc, qc, mx);
      if pc < e1 {
        NestInvOpenSite(r1, code, pcb, e1, pc, cc, qc, mx, gid);
        assert gid !in PIV.CapIds(r2) by {
          if gid in PIV.CapIds(r2) { assert gid in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
        InLooksNotIn(r2, gid);   // gid !in CapIdsInLooks(r2); combined with recursion ⇒ !in CapIdsInLooks(re)
        assert PIV.MxAtGid(re, cc, qc, mx, gid) == PIV.MxAtGid(r1, cc, qc, mx, gid);
        assert PIV.BodyOf(re, gid) == PIV.BodyOf(r1, gid);
      } else {
        NestInvOpenSite(r2, code, e1, pce, pc, cc, qc, mx, gid);
        assert gid !in PIV.CapIds(r1) by {
          if gid in PIV.CapIds(r1) { assert gid in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
        InLooksNotIn(r1, gid);
        assert PIV.MxAtGid(re, cc, qc, mx, gid) == PIV.MxAtGid(r2, cc, qc, mx, gid);
        assert PIV.BodyOf(re, gid) == PIV.BodyOf(r2, gid);
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
             else if pc == pcb + 2 then
               AI.get_idx(qc, qid) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qid))
             else if pcb + 3 <= pc < e1 then
               AI.get_idx(qc, qid) >= mx
               && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid))
             else AI.get_idx(qc, qid) >= mx;
        if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 || pc == e1 + 1 {
          assert false;                             // Fork/SetQuantToClock/BeginLoop/EndLoop/Jmp
        } else {
          assert pcb + 3 <= pc < e1;
          var qv := AI.get_idx(qc, qid);
          NestInvOpenSite(r1, code, pcb + 3, e1, pc, cc, qc, qv, gid);
          assert PIV.MxAtGid(re, cc, qc, mx, gid) == PIV.MxAtGid(r1, cc, qc, qv, gid);
          assert PIV.BodyOf(re, gid) == PIV.BodyOf(r1, gid);
          assert qv >= mx;                          // the stamp-chain claim
        }
      } else if q.max.Some? {
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid, r1, code, em, pce)
          && (if pc < em then NestInvMinRE(mn, qid, r1, code, pcb, em, pc, cc, qc, mx)
              else NestInvOptRE(kx, q.greedy, qid, r1, code, em, pce, pc, cc, qc, mx));
        var qv := AI.get_idx(qc, qid);
        if pc < em {
          NestInvOpenSiteMin(mn, qid, r1, code, pcb, em, pc, cc, qc, mx, gid);
        } else {
          NestInvOpenSiteOpt(kx, q.greedy, qid, r1, code, em, pce, pc, cc, qc, mx, gid);
        }
        assert PIV.MxAtGid(re, cc, qc, mx, gid) == PIV.MxAtGid(r1, cc, qc, qv, gid);
        assert PIV.BodyOf(re, gid) == PIV.BodyOf(r1, gid);
      } else {
        var mn1 := (q.min - 1) as nat;
        var em: nat, e1: nat :|
          NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
          && NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
          && NR.NfaRepRE(r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pce == e1 + 1
          && (if pc < em then NestInvMinRE(mn1, qid, r1, code, pcb, em, pc, cc, qc, mx)
              else if pc == em then true
              else if em + 1 <= pc < e1 then
                AI.get_idx(qc, qid) >= mx
                && NestInvRE(r1, code, em + 1, e1, pc, cc, qc, AI.get_idx(qc, qid))
              else AI.get_idx(qc, qid) >= mx);
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        var qv := AI.get_idx(qc, qid);
        if pc < em {
          NestInvOpenSiteMin(mn1, qid, r1, code, pcb, em, pc, cc, qc, mx, gid);
        } else if pc == em || pc == e1 {
          assert false;      // SetQuantToClock / Fork are not SetRegisterToCP
        } else {
          assert em + 1 <= pc < e1;
          NestInvOpenSite(r1, code, em + 1, e1, pc, cc, qc, qv, gid);
          assert qv >= mx;                          // the stamp-chain claim
        }
        assert PIV.MxAtGid(re, cc, qc, mx, gid) == PIV.MxAtGid(r1, cc, qc, qv, gid);
        assert PIV.BodyOf(re, gid) == PIV.BodyOf(r1, gid);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && if pc == pcb then
             (AI.get_idx(cc, CP.start_reg(cid)) < mx || AI.get_idx(cc, CP.start_reg(cid)) < 0)
             && AllStaleRE(r1, cc, mx)
           else
             AI.get_idx(cc, CP.start_reg(cid)) >= mx
             && AI.get_idx(cc, CP.start_reg(cid)) >= 0
             && (pcb + 1 <= pc < e1 ==> NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx));
      assert cid >= 0;                              // CapUnique
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);       // e1 >= pcb + 1 > pcb
      if pc == pcb {
        // THE open site: the instruction pins cid == gid.
        assert CP.start_reg(cid) == CP.start_reg(gid);
        assert cid == gid;                          // 2cid == 2gid
        assert gid in PIV.CapIds(re);
        assert (gid as nat) !in PIV.CapIds(r1);     // CapUnique(Re_capture)
        InLooksNotIn(r1, gid);                       // gid !in CapIdsInLooks(r1) == CapIdsInLooks(re)
        assert PIV.MxAtGid(re, cc, qc, mx, gid) == mx;
        assert PIV.BodyOf(re, gid) == r1;
        // PathPresent base case at gid's own node; own + body claims verbatim.
      } else if pc == e1 {
        // the CLOSE site: an odd register can't equal an even one.
        assert CP.end_reg(cid) == CP.start_reg(gid);
        assert 2 * cid + 1 == 2 * gid;
        assert false;
      } else {
        assert pcb + 1 <= pc < e1;
        NestInvOpenSite(r1, code, pcb + 1, e1, pc, cc, qc, mx, gid);
        assert (cid as nat) != gid by { assert (cid as nat) !in PIV.CapIds(r1); }  // CapUnique
        assert PIV.MxAtGid(re, cc, qc, mx, gid) == PIV.MxAtGid(r1, cc, qc, mx, gid);
        assert PIV.BodyOf(re, gid) == PIV.BodyOf(r1, gid);
        // ancestor clause of PathPresent: own start fresh (>= 0, >= mx).
      }
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
  }

  // =========================================================================
  // Preservation, part 1: pc advances that do NOT write registers. One edge
  // relation covers Consume fall-through (the blocked->active resume),
  // BeginLoop/EndLoop fall-through, both Fork targets, and Jmp (alt join and
  // the star back-edge). The lemma pushes the invariant across the edge; a
  // target equal to the block end bubbles out to the caller's context.
  // =========================================================================
  /** The pc-advance edges that do NOT write any register: `Consume`/`BeginLoop`
      /`EndLoop` fall-through, either `Fork` target, `Jmp`, and a CLOSE write
      (odd register, invariant-neutral). Covers every step `NestInvAdvance`
      pushes the invariant across. */
  ghost predicate StepEdgeRE(code: RB.code, pc: nat, pc': nat) {
    match NR.GetPcRE(code, pc)
    case Some(Consume(_)) => pc' == pc + 1
    case Some(AnchorAssertion(_)) => pc' == pc + 1   // zero-width fall-through, no writes
    // the lookaround gate: zero-width fall-through like an anchor. Its
    // look_regs write is invariant-neutral — NestInvRE reads capture and
    // quant clocks only.
    case Some(CheckOracle(_)) => pc' == pc + 1
    case Some(NegCheckOracle(_)) => pc' == pc + 1
    case Some(BeginLoop) => pc' == pc + 1
    case Some(EndLoop) => pc' == pc + 1
    case Some(Fork(x, y)) => (pc' as int == x) || (pc' as int == y)
    case Some(Jmp(x)) => pc' as int == x
    // a CLOSE write (odd register) is invariant-neutral: the invariant reads
    // only even (start) clock slots — see NestInvFrameOdd. Its pc-move is a
    // plain fall-through.
    case Some(SetRegisterToCP(rg)) => rg % 2 == 1 && pc' == pc + 1
    case _ => false
  }

  /** Preservation, part 1: `NestInvRE` survives every non-writing `StepEdgeRE`
      step — either the new `pc` lands back inside the block (invariant holds
      there) or it is the block's exit (`pce`), which bubbles out to the
      caller's context. */
  /** `NestInvAdvance` for forced-copy chains: non-writing steps stay inside
      the chain (body steps, body exit onto the next copy head) or exit at its
      end. */
  lemma NestInvAdvanceMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat, pc': nat,
                          cc: seq<int>, qc: seq<int>, mx: int)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    requires pcb <= pc < pce
    requires NestInvMinRE(k, qid, r1, code, pcb, pce, pc, cc, qc, mx)
    requires StepEdgeRE(code, pc, pc')
    ensures pc' == pce || (pcb <= pc' < pce && NestInvMinRE(k, qid, r1, code, pcb, pce, pc', cc, qc, mx))
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce)
      && (if pc == pcb then true
          else if pcb + 1 <= pc < e1 then
            AI.get_idx(qc, qid) >= mx
            && NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, AI.get_idx(qc, qid))
          else NestInvMinRE(k - 1, qid, r1, code, e1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, pce);
    if pc == pcb {
      assert false;                                 // SetQuantToClock is a write
    } else if pcb + 1 <= pc < e1 {
      var qv := AI.get_idx(qc, qid);
      NestInvAdvance(r1, code, pcb + 1, e1, pc, pc', cc, qc, qv);
      if pc' == e1 {
        // body exit: the next copy's head (claims `true`) or the chain end.
        if k - 1 == 0 {
          assert pc' == pce;
        } else {
          NestMinEntryRE(k - 1, qid, r1, code, e1, pce, cc, qc, mx);
          NfaRepMinPosRE(k - 1, qid, r1, code, e1, pce);
          assert NestInvMinRE(k, qid, r1, code, pcb, pce, pc', cc, qc, mx);
        }
      } else {
        assert NestInvMinRE(k, qid, r1, code, pcb, pce, pc', cc, qc, mx);
      }
    } else {
      NestInvAdvanceMin(k - 1, qid, r1, code, e1, pce, pc, pc', cc, qc, mx);
      if pc' == pce {
      } else {
        assert NestInvMinRE(k, qid, r1, code, pcb, pce, pc', cc, qc, mx);
      }
    }
  }

  /** `NestInvAdvance` for optional-layer chains: the layer fork enters the
      stamp site or escapes to the common end; `BeginLoop` enters the body from
      the re-armed `AllStale`; `EndLoop` falls onto the next layer head. */
  lemma NestInvAdvanceOpt(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat, pc': nat,
                          cc: seq<int>, qc: seq<int>, mx: int)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    requires pcb <= pc < pce
    requires NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc, cc, qc, mx)
    requires StepEdgeRE(code, pc, pc')
    ensures pc' == pce || (pcb <= pc' < pce && NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc', cc, qc, mx))
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
          else if pc == pcb + 2 then
            AI.get_idx(qc, qid) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qid))
          else if pcb + 3 <= pc < e1 then
            AI.get_idx(qc, qid) >= mx
            && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid))
          else if pc == e1 then AI.get_idx(qc, qid) >= mx
          else NestInvOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
    if pc == pcb {
      // the layer fork: stamp site (claims `true`) or the common end.
      assert pc' == pcb + 1 || pc' == pce;
      if pc' == pcb + 1 {
        assert NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc', cc, qc, mx);
      }
    } else if pc == pcb + 1 {
      assert false;                                 // SetQuantToClock is a write
    } else if pc == pcb + 2 {
      // BeginLoop falls into the body entry (or, empty body, onto EndLoop).
      assert pc' == pcb + 3;
      var qv := AI.get_idx(qc, qid);
      if pc' == e1 {
        assert NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc', cc, qc, mx);
      } else {
        NestEntryRE(r1, code, pcb + 3, e1, cc, qc, qv);
        assert NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc', cc, qc, mx);
      }
    } else if pcb + 3 <= pc < e1 {
      var qv := AI.get_idx(qc, qid);
      NestInvAdvance(r1, code, pcb + 3, e1, pc, pc', cc, qc, qv);
      if pc' == e1 {
        assert NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc', cc, qc, mx);
      } else {
        assert NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc', cc, qc, mx);
      }
    } else if pc == e1 {
      // EndLoop falls onto the next layer head (claims `true`) or the chain end.
      assert pc' == e1 + 1;
      if k - 1 == 0 {
        assert pc' == pce;
      } else {
        NestOptEntryRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, cc, qc, mx);
        NfaRepOptPosRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
        assert NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc', cc, qc, mx);
      }
    } else {
      NestInvAdvanceOpt(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, pc', cc, qc, mx);
      if pc' == pce {
      } else {
        assert NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc', cc, qc, mx);
      }
    }
  }

  lemma NestInvAdvance(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat, pc': nat,
                       cc: seq<int>, qc: seq<int>, mx: int)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires pcb <= pc < pce
    requires NestInvRE(re, code, pcb, pce, pc, cc, qc, mx)
    requires StepEdgeRE(code, pc, pc')
    ensures pc' == pce || (pcb <= pc' < pce && NestInvRE(re, code, pcb, pce, pc', cc, qc, mx))
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
      assert pc == pcb && pce == pcb + 1;
      assert pc' == pc + 1;                          // Consume
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && if pc == pcb then AllStaleRE(r1, cc, mx) && AllStaleRE(r2, cc, mx)
           else if pcb + 1 <= pc < e1 then
             NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else if pc == e1 then true
           else NestInvRE(r2, code, e1 + 1, pce, pc, cc, qc, mx);
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, pce);
      if pc == pcb {
        // Fork(pcb+1, e1+1): either branch entry, from its AllStale.
        assert pc' == pcb + 1 || pc' == e1 + 1;
        if pc' == pcb + 1 {
          if pc' == e1 {
            // r1 empty: entering the join Jmp directly; claims `true`.
            assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
          } else {
            NestEntryRE(r1, code, pcb + 1, e1, cc, qc, mx);
            assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
          }
        } else {
          if pc' == pce {
            // r2 empty: the branch entry IS the block end — bubble out.
          } else {
            NestEntryRE(r2, code, e1 + 1, pce, cc, qc, mx);
            assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
          }
        }
      } else if pcb + 1 <= pc < e1 {
        NestInvAdvance(r1, code, pcb + 1, e1, pc, pc', cc, qc, mx);
        if pc' == e1 {
          assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);   // the join Jmp: `true`
        } else {
          assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
        }
      } else if pc == e1 {
        // Jmp(pce): exit the whole alt.
        assert pc' == pce;
      } else {
        NestInvAdvance(r2, code, e1 + 1, pce, pc, pc', cc, qc, mx);
        if pc' == pce {
        } else {
          assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
        }
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && if pc < e1 then NestInvRE(r1, code, pcb, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else NestInvRE(r2, code, e1, pce, pc, cc, qc, mx);
      NR.NfaRepIncrRE(r1, code, pcb, e1);
      NR.NfaRepIncrRE(r2, code, e1, pce);
      if pc < e1 {
        NestInvAdvance(r1, code, pcb, e1, pc, pc', cc, qc, mx);
        if pc' == e1 {
          // r1 exit: enter r2 (or bubble out if r2 is empty).
          if e1 == pce {
          } else {
            NestEntryRE(r2, code, e1, pce, cc, qc, mx);
            assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
          }
        } else {
          assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
        }
      } else {
        NestInvAdvance(r2, code, e1, pce, pc, pc', cc, qc, mx);
        if pc' == pce {
        } else {
          assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
        }
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.max.Some? {
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid, r1, code, em, pce)
          && (if pc < em then NestInvMinRE(mn, qid, r1, code, pcb, em, pc, cc, qc, mx)
              else NestInvOptRE(kx, q.greedy, qid, r1, code, em, pce, pc, cc, qc, mx));
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid, r1, code, em, pce);
        if pc < em {
          NestInvAdvanceMin(mn, qid, r1, code, pcb, em, pc, pc', cc, qc, mx);
          if pc' == em {
            // Min-chain exit: the Opt chain's head (claims `true`) or the end.
            if em == pce {
            } else {
              NestOptEntryRE(kx, q.greedy, qid, r1, code, em, pce, cc, qc, mx);
              assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
            }
          } else {
            assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
          }
        } else {
          NestInvAdvanceOpt(kx, q.greedy, qid, r1, code, em, pce, pc, pc', cc, qc, mx);
          if pc' == pce {
          } else {
            assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
          }
        }
        return;
      }
      if !(q.min == 0 && q.max == None) {
        var mn1 := (q.min - 1) as nat;
        var em: nat, e1: nat :|
          NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
          && NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
          && NR.NfaRepRE(r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pce == e1 + 1
          && (if pc < em then NestInvMinRE(mn1, qid, r1, code, pcb, em, pc, cc, qc, mx)
              else if pc == em then true
              else if em + 1 <= pc < e1 then
                AI.get_idx(qc, qid) >= mx
                && NestInvRE(r1, code, em + 1, e1, pc, cc, qc, AI.get_idx(qc, qid))
              else AI.get_idx(qc, qid) >= mx);
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          NestInvAdvanceMin(mn1, qid, r1, code, pcb, em, pc, pc', cc, qc, mx);
          if pc' == em {
            assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);   // stamp site: claims true
          } else {
            assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
          }
        } else if pc == em {
          assert false;      // SetQuantToClock is a write, not a StepEdge
        } else if em + 1 <= pc < e1 {
          var qv := AI.get_idx(qc, qid);
          NestInvAdvance(r1, code, em + 1, e1, pc, pc', cc, qc, qv);
          if pc' == e1 {
            assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);   // the fork: body done
          } else {
            assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
          }
        } else {
          // the backward fork: back to the stamp (claims true) or out
          assert pc == e1;
          assert pc' == em || pc' == e1 + 1;
          if pc' == em {
            assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
          } else {
            assert pc' == pce;
          }
        }
        return;
      }
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
        && pce == e1 + 2
        && if pc == pcb || pc == pcb + 1 then true
           else if pc == pcb + 2 then
             AI.get_idx(qc, qid) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qid))
           else if pcb + 3 <= pc < e1 then
             AI.get_idx(qc, qid) >= mx
             && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid))
           else AI.get_idx(qc, qid) >= mx;
      NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
      if pc == pcb {
        // Fork: loop target pcb+1 (claims `true`) or exit target pce (bubble).
        assert pc' == pcb + 1 || pc' == pce;
        if pc' == pcb + 1 {
          assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
        }
      } else if pc == pcb + 1 {
        // SetQuantToClock is a WRITE — not a StepEdge instruction.
        assert false;
      } else if pc == pcb + 2 {
        // BeginLoop falls into the body entry (or, empty body, to EndLoop).
        assert pc' == pcb + 3;
        var qv := AI.get_idx(qc, qid);
        if pc' == e1 {
          assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);   // qc-fresh carries
        } else {
          NestEntryRE(r1, code, pcb + 3, e1, cc, qc, qv);
          assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
        }
      } else if pcb + 3 <= pc < e1 {
        var qv := AI.get_idx(qc, qid);
        NestInvAdvance(r1, code, pcb + 3, e1, pc, pc', cc, qc, qv);
        if pc' == e1 {
          assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);   // EndLoop: qc-fresh carries
        } else {
          assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
        }
      } else if pc == e1 {
        // EndLoop falls through to the back-Jmp.
        assert pc' == e1 + 1;
        assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);     // qc-fresh carries
      } else {
        // the back-Jmp returns to the fork; claims there are `true`.
        assert pc == e1 + 1 && pc' == pcb;
        assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && if pc == pcb then
             (AI.get_idx(cc, CP.start_reg(cid)) < mx || AI.get_idx(cc, CP.start_reg(cid)) < 0)
             && AllStaleRE(r1, cc, mx)
           else
             AI.get_idx(cc, CP.start_reg(cid)) >= mx
             && AI.get_idx(cc, CP.start_reg(cid)) >= 0
             && (pcb + 1 <= pc < e1 ==> NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      if pc == pcb {
        // the OPEN write (even register) is not a StepEdge instruction.
        assert CP.start_reg(cid) % 2 == 0;
        assert false;
      } else if pc == e1 {
        // the CLOSE fall-through exits the block.
        assert pc' == e1 + 1 == pce;
      } else {
        assert pcb + 1 <= pc < e1;
        NestInvAdvance(r1, code, pcb + 1, e1, pc, pc', cc, qc, mx);
        if pc' == e1 {
          assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);   // close site: ownfresh carries
        } else {
          assert NestInvRE(re, code, pcb, pce, pc', cc, qc, mx);
        }
      }
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
  }

  // =========================================================================
  // Preservation, part 2: register writes.
  // =========================================================================

  // A CLOSE write touches only an ODD clock slot; the invariant reads clocks
  // only at start registers (2g, even), so it is a pure frame.
  /** A CLOSE write touches only an odd (end) clock slot; since `NestInvRE`
      only ever reads even (start) slots, it is a pure frame — the invariant is
      unaffected by any change confined to odd indices. */
  /** `NestInvFrameOdd` for forced-copy chains. */
  lemma NestInvFrameOddMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                           cc: seq<int>, cc': seq<int>, qc: seq<int>, mx: int)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    requires forall j :: j % 2 == 0 ==> AI.get_idx(cc', j) == AI.get_idx(cc, j)
    requires NestInvMinRE(k, qid, r1, code, pcb, pce, pc, cc, qc, mx)
    ensures NestInvMinRE(k, qid, r1, code, pcb, pce, pc, cc', qc, mx)
    decreases CP.rsize(r1), k + 2
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce)
        && (if pc == pcb then true
            else if pcb + 1 <= pc < e1 then
              AI.get_idx(qc, qid) >= mx
              && NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, AI.get_idx(qc, qid))
            else NestInvMinRE(k - 1, qid, r1, code, e1, pce, pc, cc, qc, mx));
      if pc == pcb {
      } else if pcb + 1 <= pc < e1 {
        NestInvFrameOdd(r1, code, pcb + 1, e1, pc, cc, cc', qc, AI.get_idx(qc, qid));
      } else {
        NestInvFrameOddMin(k - 1, qid, r1, code, e1, pce, pc, cc, cc', qc, mx);
      }
      assert NestInvMinRE(k, qid, r1, code, pcb, pce, pc, cc', qc, mx);
    }
  }

  /** `NestInvFrameOdd` for optional-layer chains. */
  lemma NestInvFrameOddOpt(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                           cc: seq<int>, cc': seq<int>, qc: seq<int>, mx: int)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    requires forall j :: j % 2 == 0 ==> AI.get_idx(cc', j) == AI.get_idx(cc, j)
    requires NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc, cc, qc, mx)
    ensures NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc, cc', qc, mx)
    decreases CP.rsize(r1), k + 2
  {
    assert forall g: nat :: AI.get_idx(cc', CP.start_reg(g)) == AI.get_idx(cc, CP.start_reg(g)) by {
      forall g: nat ensures AI.get_idx(cc', CP.start_reg(g)) == AI.get_idx(cc, CP.start_reg(g)) {
        assert CP.start_reg(g) % 2 == 0;
      }
    }
    if k > 0 {
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce)
        && (if pc == pcb || pc == pcb + 1 then true
            else if pc == pcb + 2 then
              AI.get_idx(qc, qid) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qid))
            else if pcb + 3 <= pc < e1 then
              AI.get_idx(qc, qid) >= mx
              && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid))
            else if pc == e1 then AI.get_idx(qc, qid) >= mx
            else NestInvOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, cc, qc, mx));
      if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 {
      } else if pcb + 3 <= pc < e1 {
        NestInvFrameOdd(r1, code, pcb + 3, e1, pc, cc, cc', qc, AI.get_idx(qc, qid));
      } else {
        NestInvFrameOddOpt(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, cc, cc', qc, mx);
      }
      assert NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc, cc', qc, mx);
    }
  }

  lemma NestInvFrameOdd(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                        cc: seq<int>, cc': seq<int>, qc: seq<int>, mx: int)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires forall j :: j % 2 == 0 ==> AI.get_idx(cc', j) == AI.get_idx(cc, j)
    requires NestInvRE(re, code, pcb, pce, pc, cc, qc, mx)
    ensures NestInvRE(re, code, pcb, pce, pc, cc', qc, mx)
    decreases CP.rsize(re), 1
  {
    assert forall g: nat :: AI.get_idx(cc', CP.start_reg(g)) == AI.get_idx(cc, CP.start_reg(g)) by {
      forall g: nat ensures AI.get_idx(cc', CP.start_reg(g)) == AI.get_idx(cc, CP.start_reg(g)) {
        assert CP.start_reg(g) % 2 == 0;
      }
    }
    match re
    case Re_empty => case Re_character(_) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && if pc == pcb then AllStaleRE(r1, cc, mx) && AllStaleRE(r2, cc, mx)
           else if pcb + 1 <= pc < e1 then
             NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else if pc == e1 then true
           else NestInvRE(r2, code, e1 + 1, pce, pc, cc, qc, mx);
      if pc == pcb {
      } else if pcb + 1 <= pc < e1 {
        NestInvFrameOdd(r1, code, pcb + 1, e1, pc, cc, cc', qc, mx);
      } else if pc == e1 {
      } else {
        NestInvFrameOdd(r2, code, e1 + 1, pce, pc, cc, cc', qc, mx);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && if pc < e1 then NestInvRE(r1, code, pcb, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else NestInvRE(r2, code, e1, pce, pc, cc, qc, mx);
      if pc < e1 {
        NestInvFrameOdd(r1, code, pcb, e1, pc, cc, cc', qc, mx);
      } else {
        NestInvFrameOdd(r2, code, e1, pce, pc, cc, cc', qc, mx);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.max.Some? {
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid, r1, code, em, pce)
          && (if pc < em then NestInvMinRE(mn, qid, r1, code, pcb, em, pc, cc, qc, mx)
              else NestInvOptRE(kx, q.greedy, qid, r1, code, em, pce, pc, cc, qc, mx));
        if pc < em {
          NestInvFrameOddMin(mn, qid, r1, code, pcb, em, pc, cc, cc', qc, mx);
        } else {
          NestInvFrameOddOpt(kx, q.greedy, qid, r1, code, em, pce, pc, cc, cc', qc, mx);
        }
        assert NestInvRE(re, code, pcb, pce, pc, cc', qc, mx);
        return;
      }
      if !(q.min == 0 && q.max == None) {
        var mn1 := (q.min - 1) as nat;
        var em: nat, e1: nat :|
          NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
          && NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
          && NR.NfaRepRE(r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pce == e1 + 1
          && (if pc < em then NestInvMinRE(mn1, qid, r1, code, pcb, em, pc, cc, qc, mx)
              else if pc == em then true
              else if em + 1 <= pc < e1 then
                AI.get_idx(qc, qid) >= mx
                && NestInvRE(r1, code, em + 1, e1, pc, cc, qc, AI.get_idx(qc, qid))
              else AI.get_idx(qc, qid) >= mx);
        if pc < em {
          NestInvFrameOddMin(mn1, qid, r1, code, pcb, em, pc, cc, cc', qc, mx);
        } else if em + 1 <= pc < e1 {
          NestInvFrameOdd(r1, code, em + 1, e1, pc, cc, cc', qc, AI.get_idx(qc, qid));
        }
        assert NestInvRE(re, code, pcb, pce, pc, cc', qc, mx);
        return;
      }
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
        && pce == e1 + 2
        && if pc == pcb || pc == pcb + 1 then true
           else if pc == pcb + 2 then
             AI.get_idx(qc, qid) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qid))
           else if pcb + 3 <= pc < e1 then
             AI.get_idx(qc, qid) >= mx
             && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid))
           else AI.get_idx(qc, qid) >= mx;
      if pcb + 3 <= pc < e1 {
        NestInvFrameOdd(r1, code, pcb + 3, e1, pc, cc, cc', qc, AI.get_idx(qc, qid));
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && if pc == pcb then
             (AI.get_idx(cc, CP.start_reg(cid)) < mx || AI.get_idx(cc, CP.start_reg(cid)) < 0)
             && AllStaleRE(r1, cc, mx)
           else
             AI.get_idx(cc, CP.start_reg(cid)) >= mx
             && AI.get_idx(cc, CP.start_reg(cid)) >= 0
             && (pcb + 1 <= pc < e1 ==> NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx));
      assert CP.start_reg(cid) % 2 == 0;
      if pc != pcb && pcb + 1 <= pc < e1 {
        NestInvFrameOdd(r1, code, pcb + 1, e1, pc, cc, cc', qc, mx);
      }
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
  }

  // The STAMP write: at a quant's SetQuantToClock site, writing a strictly
  // dominating clock re-arms the whole body (AllStale w.r.t. the new stamp is
  // free) and establishes the stamp-chain claim; everything else is framed by
  // quant-id uniqueness. pc advances to the BeginLoop.
  /** Preservation, part 2a: at a quant's `SetQuantToClock` site, stamping a
      clock strictly above every existing clock and above `mx` re-arms the
      whole loop body as stale for free and establishes the stamp-chain claim,
      while quant-id uniqueness (`PIV.QuantUnique`) frames every unrelated
      node. `pc` advances to the `BeginLoop`. */
  /** `NestInvStamp` for forced-copy chains: stamping a copy head re-arms that
      copy's body for free (the fresh clock dominates every capture clock);
      stamping inside a body recurses with this quantifier's node framed by
      quant-id uniqueness. The advance may exit the chain (empty bodies), hence
      the disjunctive ensures. */
  lemma NestInvStampMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                        cc: seq<int>, qc: seq<int>, qc': seq<int>, mx: int, qid0: int, clk: int)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    requires PIV.QuantUnique(r1)
    requires qid >= 0 && (qid as nat) !in PIV.QuantIds(r1)
    requires pcb <= pc < pce
    requires NestInvMinRE(k, qid, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, false))
    requires 0 <= qid0 < |qc|
    requires qc' == qc[qid0 := clk]
    requires forall j :: AI.get_idx(cc, j) < clk
    requires forall j :: AI.get_idx(qc, j) < clk
    requires mx < clk
    ensures pc + 1 == pce || (pcb <= pc + 1 < pce && NestInvMinRE(k, qid, r1, code, pcb, pce, pc + 1, cc, qc', mx))
    ensures qid0 == qid || (qid0 as nat) in PIV.QuantIds(r1)
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce)
      && (if pc == pcb then true
          else if pcb + 1 <= pc < e1 then
            AI.get_idx(qc, qid) >= mx
            && NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, AI.get_idx(qc, qid))
          else NestInvMinRE(k - 1, qid, r1, code, e1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, pce);
    if pc == pcb {
      // THE copy-head stamp: instruction pins qid0 == qid.
      assert qid0 == qid;
      assert AI.get_idx(qc', qid) == clk;
      assert AllStaleRE(r1, cc, clk);
      if pc + 1 < e1 {
        // body entry, re-armed at the fresh stamp
        NestEntryRE(r1, code, pcb + 1, e1, cc, qc', clk);
        assert NestInvMinRE(k, qid, r1, code, pcb, pce, pc + 1, cc, qc', mx);
      } else {
        // empty body: pc+1 sits on the next copy head (or exits the chain)
        assert pc + 1 == e1;
        if k - 1 == 0 {
          assert pc + 1 == pce;
        } else {
          NestMinEntryRE(k - 1, qid, r1, code, e1, pce, cc, qc', mx);
          NfaRepMinPosRE(k - 1, qid, r1, code, e1, pce);
          assert NestInvMinRE(k, qid, r1, code, pcb, pce, pc + 1, cc, qc', mx);
        }
      }
    } else if pcb + 1 <= pc < e1 {
      var qv := AI.get_idx(qc, qid);
      NestInvStamp(r1, code, pcb + 1, e1, pc, cc, qc, qc', qv, qid0, clk);
      assert (qid0 as nat) in PIV.QuantIds(r1);
      assert qid != qid0;
      assert AI.get_idx(qc', qid) == AI.get_idx(qc, qid);
      if pc + 1 == e1 {
        // body exit onto the next copy head (or out of the chain)
        if k - 1 == 0 {
          assert pc + 1 == pce;
        } else {
          NestMinEntryRE(k - 1, qid, r1, code, e1, pce, cc, qc', mx);
          NfaRepMinPosRE(k - 1, qid, r1, code, e1, pce);
          assert NestInvMinRE(k, qid, r1, code, pcb, pce, pc + 1, cc, qc', mx);
        }
      } else {
        assert NestInvMinRE(k, qid, r1, code, pcb, pce, pc + 1, cc, qc', mx);
      }
    } else {
      NestInvStampMin(k - 1, qid, r1, code, e1, pce, pc, cc, qc, qc', mx, qid0, clk);
      if pc + 1 == pce {
      } else {
        assert NestInvMinRE(k, qid, r1, code, pcb, pce, pc + 1, cc, qc', mx);
      }
    }
  }

  /** `NestInvStamp` for optional-layer chains: the layer stamp lands on the
      `BeginLoop` with the body re-armed; body stamps are framed like the
      star's. A stamp is never the last instruction of a layer, so the strong
      ensures survives. */
  lemma NestInvStampOpt(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                        cc: seq<int>, qc: seq<int>, qc': seq<int>, mx: int, qid0: int, clk: int)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    requires PIV.QuantUnique(r1)
    requires qid >= 0 && (qid as nat) !in PIV.QuantIds(r1)
    requires pcb <= pc < pce
    requires NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, false))
    requires 0 <= qid0 < |qc|
    requires qc' == qc[qid0 := clk]
    requires forall j :: AI.get_idx(cc, j) < clk
    requires forall j :: AI.get_idx(qc, j) < clk
    requires mx < clk
    ensures pcb <= pc + 1 < pce && NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc + 1, cc, qc', mx)
    ensures qid0 == qid || (qid0 as nat) in PIV.QuantIds(r1)
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
          else if pc == pcb + 2 then
            AI.get_idx(qc, qid) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qid))
          else if pcb + 3 <= pc < e1 then
            AI.get_idx(qc, qid) >= mx
            && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid))
          else if pc == e1 then AI.get_idx(qc, qid) >= mx
          else NestInvOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
    if pc == pcb + 1 {
      // THE layer stamp: instruction pins qid0 == qid; lands on the BeginLoop.
      assert qid0 == qid;
      assert AI.get_idx(qc', qid) == clk;
      assert clk >= mx;
      assert AllStaleRE(r1, cc, clk);
      assert NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc + 1, cc, qc', mx);
    } else if pc == pcb || pc == pcb + 2 || pc == e1 {
      assert false;                                 // Fork/BeginLoop/EndLoop
    } else if pcb + 3 <= pc < e1 {
      var qv := AI.get_idx(qc, qid);
      NestInvStamp(r1, code, pcb + 3, e1, pc, cc, qc, qc', qv, qid0, clk);
      assert (qid0 as nat) in PIV.QuantIds(r1);
      assert qid != qid0;
      assert AI.get_idx(qc', qid) == AI.get_idx(qc, qid);
      if pc + 1 == e1 {
        assert NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc + 1, cc, qc', mx);
      } else {
        assert NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc + 1, cc, qc', mx);
      }
    } else {
      NestInvStampOpt(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, cc, qc, qc', mx, qid0, clk);
      assert NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc + 1, cc, qc', mx);
    }
  }

  lemma NestInvStamp(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                     cc: seq<int>, qc: seq<int>, qc': seq<int>, mx: int, qid0: int, clk: int)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestInvRE(re, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, false))
    requires 0 <= qid0 < |qc|
    requires qc' == qc[qid0 := clk]
    requires forall k :: AI.get_idx(cc, k) < clk
    requires forall k :: AI.get_idx(qc, k) < clk
    requires mx < clk
    ensures pc + 1 == pce || (pcb <= pc + 1 < pce && NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx))
    ensures (qid0 as nat) in PIV.QuantIds(re)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
      assert pc == pcb;
      assert false;
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && if pc == pcb then AllStaleRE(r1, cc, mx) && AllStaleRE(r2, cc, mx)
           else if pcb + 1 <= pc < e1 then
             NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else if pc == e1 then true
           else NestInvRE(r2, code, e1 + 1, pce, pc, cc, qc, mx);
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, pce);
      if pc == pcb || pc == e1 {
        assert false;
      } else if pcb + 1 <= pc < e1 {
        NestInvStamp(r1, code, pcb + 1, e1, pc, cc, qc, qc', mx, qid0, clk);
        if pc + 1 == e1 {
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);  // the join Jmp: `true`
        } else {
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);
        }
      } else {
        NestInvStamp(r2, code, e1 + 1, pce, pc, cc, qc, qc', mx, qid0, clk);
        if pc + 1 == pce {
        } else {
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);
        }
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && if pc < e1 then NestInvRE(r1, code, pcb, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else NestInvRE(r2, code, e1, pce, pc, cc, qc, mx);
      NR.NfaRepIncrRE(r1, code, pcb, e1);
      NR.NfaRepIncrRE(r2, code, e1, pce);
      if pc < e1 {
        NestInvStamp(r1, code, pcb, e1, pc, cc, qc, qc', mx, qid0, clk);
        if pc + 1 == e1 {
          // r1 exit: enter r2 (or bubble out if r2 is empty; cc unchanged).
          if e1 == pce {
          } else {
            NestEntryRE(r2, code, e1, pce, cc, qc', mx);
            assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);
          }
        } else {
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);
        }
      } else {
        NestInvStamp(r2, code, e1, pce, pc, cc, qc, qc', mx, qid0, clk);
        if pc + 1 == pce {
        } else {
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);
        }
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.max.Some? {
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid, r1, code, em, pce)
          && (if pc < em then NestInvMinRE(mn, qid, r1, code, pcb, em, pc, cc, qc, mx)
              else NestInvOptRE(kx, q.greedy, qid, r1, code, em, pce, pc, cc, qc, mx));
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid, r1, code, em, pce);
        assert qid >= 0;                                // QuantUnique
        assert (qid as nat) !in PIV.QuantIds(r1);       // QuantUnique
        if pc < em {
          NestInvStampMin(mn, qid, r1, code, pcb, em, pc, cc, qc, qc', mx, qid0, clk);
          assert (qid0 as nat) in PIV.QuantIds(re);
          if pc + 1 == em {
            // Min-chain exit: the Opt chain's head (claims `true`) or the end.
            if em == pce {
              assert pc + 1 == pce;
            } else {
              NestOptEntryRE(kx, q.greedy, qid, r1, code, em, pce, cc, qc', mx);
              assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);
            }
          } else {
            assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);
          }
        } else {
          NestInvStampOpt(kx, q.greedy, qid, r1, code, em, pce, pc, cc, qc, qc', mx, qid0, clk);
          assert (qid0 as nat) in PIV.QuantIds(re);
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);
        }
        return;
      }
      if !(q.min == 0 && q.max == None) {
        var mn1 := (q.min - 1) as nat;
        var em: nat, e1: nat :|
          NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
          && NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
          && NR.NfaRepRE(r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pce == e1 + 1
          && (if pc < em then NestInvMinRE(mn1, qid, r1, code, pcb, em, pc, cc, qc, mx)
              else if pc == em then true
              else if em + 1 <= pc < e1 then
                AI.get_idx(qc, qid) >= mx
                && NestInvRE(r1, code, em + 1, e1, pc, cc, qc, AI.get_idx(qc, qid))
              else AI.get_idx(qc, qid) >= mx);
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        assert qid >= 0;                                // QuantUnique
        assert (qid as nat) !in PIV.QuantIds(r1);       // QuantUnique
        if pc < em {
          NestInvStampMin(mn1, qid, r1, code, pcb, em, pc, cc, qc, qc', mx, qid0, clk);
          assert (qid0 as nat) in PIV.QuantIds(re);
          if pc + 1 == em {
            assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);   // the stamp site: claims true
          } else {
            assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);
          }
        } else if pc == em {
          // THE last-copy stamp: the instruction pins qid0 == qid
          assert qid0 == qid;
          assert (qid0 as nat) in PIV.QuantIds(re);
          assert AI.get_idx(qc', qid) == clk;
          assert clk >= mx;
          if pc + 1 == e1 {
            // empty body: pc+1 is the fork; the stamp-chain claim carries
            assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);
          } else {
            assert AllStaleRE(r1, cc, clk);
            NestEntryRE(r1, code, em + 1, e1, cc, qc', clk);
            assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);
          }
        } else if em + 1 <= pc < e1 {
          var qv := AI.get_idx(qc, qid);
          NestInvStamp(r1, code, em + 1, e1, pc, cc, qc, qc', qv, qid0, clk);
          assert (qid0 as nat) in PIV.QuantIds(r1);
          assert qid != qid0;
          assert AI.get_idx(qc', qid) == AI.get_idx(qc, qid);
          if pc + 1 == e1 {
            assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);   // the fork: stamp-chain claim
          } else {
            assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);
          }
        } else {
          assert pc == e1;
          assert false;                                 // Fork is not SetQuantToClock
        }
        return;
      }
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
        && pce == e1 + 2
        && if pc == pcb || pc == pcb + 1 then true
           else if pc == pcb + 2 then
             AI.get_idx(qc, qid) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qid))
           else if pcb + 3 <= pc < e1 then
             AI.get_idx(qc, qid) >= mx
             && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid))
           else AI.get_idx(qc, qid) >= mx;
      NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
      assert qid >= 0;                                  // QuantUnique
      if pc == pcb + 1 {
        // THE stamp site: instruction pins qid == qid0.
        assert qid == qid0;
        assert (qid0 as nat) in PIV.QuantIds(re);
        assert AI.get_idx(qc', qid0) == clk;
        // claims at pcb+2: fresh stamp beats mx; body all-stale w.r.t. it.
        assert clk >= mx;
        assert AllStaleRE(r1, cc, clk);
        assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);
      } else if pc == pcb || pc == pcb + 2 || pc == e1 || pc == e1 + 1 {
        assert false;                                   // Fork/BeginLoop/EndLoop/Jmp
      } else {
        assert pcb + 3 <= pc < e1;
        var qv := AI.get_idx(qc, qid);
        NestInvStamp(r1, code, pcb + 3, e1, pc, cc, qc, qc', qv, qid0, clk);
        // the site's qid0 sits inside r1; this node's qid is distinct.
        assert (qid0 as nat) in PIV.QuantIds(r1);
        assert qid != qid0 by { assert (qid as nat) !in PIV.QuantIds(r1); }   // QuantUnique
        assert AI.get_idx(qc', qid) == AI.get_idx(qc, qid);
        if pc + 1 == e1 {
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);  // EndLoop: stamp-chain claim
        } else {
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);
        }
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && if pc == pcb then
             (AI.get_idx(cc, CP.start_reg(cid)) < mx || AI.get_idx(cc, CP.start_reg(cid)) < 0)
             && AllStaleRE(r1, cc, mx)
           else
             AI.get_idx(cc, CP.start_reg(cid)) >= mx
             && AI.get_idx(cc, CP.start_reg(cid)) >= 0
             && (pcb + 1 <= pc < e1 ==> NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      if pc == pcb || pc == e1 {
        assert false;                                   // SetRegisterToCP ≠ SetQuantToClock
      } else {
        assert pcb + 1 <= pc < e1;
        NestInvStamp(r1, code, pcb + 1, e1, pc, cc, qc, qc', mx, qid0, clk);
        if pc + 1 == e1 {
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);  // close site: ownfresh carries (cc unchanged)
        } else {
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc, qc', mx);
        }
      }
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
  }

  // The OPEN write: at a capture's open site, writing a strictly dominating
  // clock into the start register makes the node fresh (ownfresh claims) and
  // enters the body from its AllStale (untouched by the write — the id is not
  // in its own body). Ancestors and siblings are framed by capture-id
  // uniqueness. pc advances into the body (or to the close site if empty).
  /** Preservation, part 2b: at a capture's open site, writing a strictly
      dominating clock into the start register makes that node fresh and lets
      the body be entered from its own `AllStaleRE`, while capture-id
      uniqueness (`PIV.CapUnique`) frames ancestors and siblings. `pc` advances
      into the body (or to the close site if the body is empty). */
  /** `NestInvOpenWrite` for forced-copy chains: an OPEN write only ever sits
      inside a copy's body (chain heads are clock-mark instructions); the write
      is framed for the chain by the fresh clock's dominance. */
  lemma NestInvOpenWriteMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                            cc: seq<int>, cc': seq<int>, qc: seq<int>, mx: int, sreg: int, clk: int)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    requires PIV.CapUnique(r1)
    requires pcb <= pc < pce
    requires NestInvMinRE(k, qid, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(sreg))
    requires sreg % 2 == 0
    requires 0 <= sreg < |cc|
    requires cc' == cc[sreg := clk]
    requires forall j :: AI.get_idx(cc, j) < clk
    requires forall j :: AI.get_idx(qc, j) < clk
    requires mx < clk
    ensures pcb <= pc + 1 < pce && NestInvMinRE(k, qid, r1, code, pcb, pce, pc + 1, cc', qc, mx)
    ensures ((sreg / 2) as nat) in PIV.CapIds(r1)
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce)
      && (if pc == pcb then true
          else if pcb + 1 <= pc < e1 then
            AI.get_idx(qc, qid) >= mx
            && NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, AI.get_idx(qc, qid))
          else NestInvMinRE(k - 1, qid, r1, code, e1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, pce);
    if pc == pcb {
      assert false;                                 // SetQuantToClock ≠ SetRegisterToCP
    } else if pcb + 1 <= pc < e1 {
      var qv := AI.get_idx(qc, qid);
      NestInvOpenWrite(r1, code, pcb + 1, e1, pc, cc, cc', qc, qv, sreg, clk);
      assert NestInvMinRE(k, qid, r1, code, pcb, pce, pc + 1, cc', qc, mx);
    } else {
      NestInvOpenWriteMin(k - 1, qid, r1, code, e1, pce, pc, cc, cc', qc, mx, sreg, clk);
      assert NestInvMinRE(k, qid, r1, code, pcb, pce, pc + 1, cc', qc, mx);
    }
  }

  /** `NestInvOpenWrite` for optional-layer chains. */
  lemma NestInvOpenWriteOpt(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                            cc: seq<int>, cc': seq<int>, qc: seq<int>, mx: int, sreg: int, clk: int)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    requires PIV.CapUnique(r1)
    requires pcb <= pc < pce
    requires NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(sreg))
    requires sreg % 2 == 0
    requires 0 <= sreg < |cc|
    requires cc' == cc[sreg := clk]
    requires forall j :: AI.get_idx(cc, j) < clk
    requires forall j :: AI.get_idx(qc, j) < clk
    requires mx < clk
    ensures pcb <= pc + 1 < pce && NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc + 1, cc', qc, mx)
    ensures ((sreg / 2) as nat) in PIV.CapIds(r1)
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
          else if pc == pcb + 2 then
            AI.get_idx(qc, qid) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qid))
          else if pcb + 3 <= pc < e1 then
            AI.get_idx(qc, qid) >= mx
            && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid))
          else if pc == e1 then AI.get_idx(qc, qid) >= mx
          else NestInvOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
    if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 {
      assert false;                                 // structural instructions differ
    } else if pcb + 3 <= pc < e1 {
      var qv := AI.get_idx(qc, qid);
      NestInvOpenWrite(r1, code, pcb + 3, e1, pc, cc, cc', qc, qv, sreg, clk);
      assert NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc + 1, cc', qc, mx);
    } else {
      NestInvOpenWriteOpt(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, cc, cc', qc, mx, sreg, clk);
      assert NestInvOptRE(k, greedy, qid, r1, code, pcb, pce, pc + 1, cc', qc, mx);
    }
  }

  lemma NestInvOpenWrite(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                         cc: seq<int>, cc': seq<int>, qc: seq<int>, mx: int, sreg: int, clk: int)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.CapUnique(re)
    requires pcb <= pc < pce
    requires NestInvRE(re, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(sreg))
    requires sreg % 2 == 0
    requires 0 <= sreg < |cc|
    requires cc' == cc[sreg := clk]
    requires forall k :: AI.get_idx(cc, k) < clk
    requires forall k :: AI.get_idx(qc, k) < clk
    requires mx < clk
    ensures pcb <= pc + 1 < pce && NestInvRE(re, code, pcb, pce, pc + 1, cc', qc, mx)
    ensures ((sreg / 2) as nat) in PIV.CapIds(re)
    decreases CP.rsize(re), 1
  {
    var gid: nat := (sreg / 2) as nat;
    assert CP.start_reg(gid) == sreg;
    match re
    case Re_empty =>
    case Re_character(ch) =>
      assert pc == pcb;
      assert false;
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && if pc == pcb then AllStaleRE(r1, cc, mx) && AllStaleRE(r2, cc, mx)
           else if pcb + 1 <= pc < e1 then
             NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else if pc == e1 then true
           else NestInvRE(r2, code, e1 + 1, pce, pc, cc, qc, mx);
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, pce);
      if pc == pcb || pc == e1 {
        assert false;                                   // Fork / Jmp
      } else if pcb + 1 <= pc < e1 {
        NestInvOpenWrite(r1, code, pcb + 1, e1, pc, cc, cc', qc, mx, sreg, clk);
        // the written id lives in r1; r2's AllStale is framed by disjointness.
        assert AllStaleRE(r2, cc', mx) by {
          forall g: nat | g in PIV.CapIds(r2)
            ensures AI.get_idx(cc', CP.start_reg(g)) == AI.get_idx(cc, CP.start_reg(g))
          {
            assert g !in PIV.CapIds(r1) by { if g in PIV.CapIds(r1) { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); } }
            assert g != gid;
            assert CP.start_reg(g) != sreg;
          }
        }
        assert NestInvRE(re, code, pcb, pce, pc + 1, cc', qc, mx);
      } else {
        NestInvOpenWrite(r2, code, e1 + 1, pce, pc, cc, cc', qc, mx, sreg, clk);
        assert NestInvRE(re, code, pcb, pce, pc + 1, cc', qc, mx);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && if pc < e1 then NestInvRE(r1, code, pcb, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else NestInvRE(r2, code, e1, pce, pc, cc, qc, mx);
      NR.NfaRepIncrRE(r1, code, pcb, e1);
      NR.NfaRepIncrRE(r2, code, e1, pce);
      if pc < e1 {
        NestInvOpenWrite(r1, code, pcb, e1, pc, cc, cc', qc, mx, sreg, clk);
        assert pc + 1 < e1;                             // from the recursion's ensures
        assert AllStaleRE(r2, cc', mx) by {
          forall g: nat | g in PIV.CapIds(r2)
            ensures AI.get_idx(cc', CP.start_reg(g)) == AI.get_idx(cc, CP.start_reg(g))
          {
            assert g !in PIV.CapIds(r1) by { if g in PIV.CapIds(r1) { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); } }
            assert g != gid;
            assert CP.start_reg(g) != sreg;
          }
        }
        assert NestInvRE(re, code, pcb, pce, pc + 1, cc', qc, mx);
      } else {
        NestInvOpenWrite(r2, code, e1, pce, pc, cc, cc', qc, mx, sreg, clk);
        assert NestInvRE(re, code, pcb, pce, pc + 1, cc', qc, mx);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.max.Some? {
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid, r1, code, em, pce)
          && (if pc < em then NestInvMinRE(mn, qid, r1, code, pcb, em, pc, cc, qc, mx)
              else NestInvOptRE(kx, q.greedy, qid, r1, code, em, pce, pc, cc, qc, mx));
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid, r1, code, em, pce);
        if pc < em {
          NestInvOpenWriteMin(mn, qid, r1, code, pcb, em, pc, cc, cc', qc, mx, sreg, clk);
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc', qc, mx);
        } else {
          NestInvOpenWriteOpt(kx, q.greedy, qid, r1, code, em, pce, pc, cc, cc', qc, mx, sreg, clk);
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc', qc, mx);
        }
        return;
      }
      if !(q.min == 0 && q.max == None) {
        var mn1 := (q.min - 1) as nat;
        var em: nat, e1: nat :|
          NR.NfaRepMinRE(mn1, qid, r1, code, pcb, em)
          && NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
          && NR.NfaRepRE(r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pce == e1 + 1
          && (if pc < em then NestInvMinRE(mn1, qid, r1, code, pcb, em, pc, cc, qc, mx)
              else if pc == em then true
              else if em + 1 <= pc < e1 then
                AI.get_idx(qc, qid) >= mx
                && NestInvRE(r1, code, em + 1, e1, pc, cc, qc, AI.get_idx(qc, qid))
              else AI.get_idx(qc, qid) >= mx);
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          NestInvOpenWriteMin(mn1, qid, r1, code, pcb, em, pc, cc, cc', qc, mx, sreg, clk);
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc', qc, mx);
        } else if pc == em || pc == e1 {
          assert false;      // SetQuantToClock / Fork are not SetRegisterToCP
        } else {
          assert em + 1 <= pc < e1;
          var qv := AI.get_idx(qc, qid);
          NestInvOpenWrite(r1, code, em + 1, e1, pc, cc, cc', qc, qv, sreg, clk);
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc', qc, mx);
        }
        return;
      }
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
        && pce == e1 + 2
        && if pc == pcb || pc == pcb + 1 then true
           else if pc == pcb + 2 then
             AI.get_idx(qc, qid) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qid))
           else if pcb + 3 <= pc < e1 then
             AI.get_idx(qc, qid) >= mx
             && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid))
           else AI.get_idx(qc, qid) >= mx;
      NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
      if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 || pc == e1 + 1 {
        assert false;                                   // structural instructions differ
      } else {
        assert pcb + 3 <= pc < e1;
        var qv := AI.get_idx(qc, qid);
        NestInvOpenWrite(r1, code, pcb + 3, e1, pc, cc, cc', qc, qv, sreg, clk);
        assert NestInvRE(re, code, pcb, pce, pc + 1, cc', qc, mx);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && if pc == pcb then
             (AI.get_idx(cc, CP.start_reg(cid)) < mx || AI.get_idx(cc, CP.start_reg(cid)) < 0)
             && AllStaleRE(r1, cc, mx)
           else
             AI.get_idx(cc, CP.start_reg(cid)) >= mx
             && AI.get_idx(cc, CP.start_reg(cid)) >= 0
             && (pcb + 1 <= pc < e1 ==> NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      assert cid >= 0;                                  // CapUnique
      if pc == pcb {
        // THE open site: the instruction pins cid == gid.
        assert CP.start_reg(cid) == sreg;
        assert cid == gid;
        assert gid in PIV.CapIds(re);
        // ownfresh with the new clock.
        assert AI.get_idx(cc', CP.start_reg(cid)) == clk;
        assert clk >= 0 by { assert AI.get_idx(cc, -1) == -1 < clk; }
        assert clk >= mx;
        // body untouched by the write (cid not in its own body).
        assert AllStaleRE(r1, cc', mx) by {
          forall g: nat | g in PIV.CapIds(r1)
            ensures AI.get_idx(cc', CP.start_reg(g)) == AI.get_idx(cc, CP.start_reg(g))
          {
            assert g != gid by { assert (cid as nat) !in PIV.CapIds(r1); }
            assert CP.start_reg(g) != sreg;
          }
        }
        if pcb + 1 < e1 {
          NestEntryRE(r1, code, pcb + 1, e1, cc', qc, mx);
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc', qc, mx);
        } else {
          // empty body: pc+1 is the close site; ownfresh claims only.
          assert pc + 1 == e1;
          assert NestInvRE(re, code, pcb, pce, pc + 1, cc', qc, mx);
        }
      } else if pc == e1 {
        // the close site writes an ODD register; sreg is even.
        assert CP.end_reg(cid) == sreg;
        assert false;
      } else {
        assert pcb + 1 <= pc < e1;
        NestInvOpenWrite(r1, code, pcb + 1, e1, pc, cc, cc', qc, mx, sreg, clk);
        // this node's ownfresh is framed: cid differs from the id written inside r1.
        assert gid in PIV.CapIds(r1);
        assert (cid as nat) != gid by { assert (cid as nat) !in PIV.CapIds(r1); }
        assert CP.start_reg(cid) != sreg;
        assert AI.get_idx(cc', CP.start_reg(cid)) == AI.get_idx(cc, CP.start_reg(cid));
        assert NestInvRE(re, code, pcb, pce, pc + 1, cc', qc, mx);
      }
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
  }

  // =========================================================================
  // Instruction inventory + register bounds: every write instruction in a
  // represented block targets a register belonging to one of re's nodes, and
  // node ids are bounded by max_group/max_quant — so the pipeline's register
  // files (2*max_group+2 captures, max_quant+1 quants) cover every write.
  // Discharges the range hypotheses of NestInvOpenWrite/NestInvStamp and the
  // GM interface lemmas.
  // =========================================================================
  /** Every register-writing instruction inside a represented block targets a
      register belonging to one of `re`'s own nodes (a real capture's start/end
      register, or a real quant's clock, with `bb == false`) — the range
      hypotheses `NestInvOpenWrite`/`NestInvStamp` and the `GmOfLive*` interface
      lemmas need. */
  /** `CodeShapeAt` for forced-copy chains (phrased against the body and this
      quantifier's own id). */
  lemma CodeShapeAtMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    requires PIV.CapUnique(r1) && PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    ensures forall reg: int :: NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(reg))
              ==> exists gid: nat :: gid in PIV.CapIds(r1)
                    && (reg == CP.start_reg(gid) || reg == CP.end_reg(gid))
    ensures forall qd: int, bb: bool :: NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qd, bb))
              ==> !bb && (qd == qid || (qd >= 0 && (qd as nat) in PIV.QuantIds(r1)))
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce);
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, pce);
    if pc == pcb {
    } else if pcb + 1 <= pc < e1 {
      CodeShapeAt(r1, code, pcb + 1, e1, pc);
    } else {
      CodeShapeAtMin(k - 1, qid, r1, code, e1, pce, pc);
    }
  }

  /** `CodeShapeAt` for optional-layer chains. */
  lemma CodeShapeAtOpt(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    requires PIV.CapUnique(r1) && PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    ensures forall reg: int :: NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(reg))
              ==> exists gid: nat :: gid in PIV.CapIds(r1)
                    && (reg == CP.start_reg(gid) || reg == CP.end_reg(gid))
    ensures forall qd: int, bb: bool :: NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qd, bb))
              ==> !bb && (qd == qid || (qd >= 0 && (qd as nat) in PIV.QuantIds(r1)))
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, pcb + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
    if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 {
    } else if pcb + 3 <= pc < e1 {
      CodeShapeAt(r1, code, pcb + 3, e1, pc);
    } else {
      CodeShapeAtOpt(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc);
    }
  }

  lemma CodeShapeAt(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires pcb <= pc < pce
    ensures forall reg: int :: NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(reg))
              ==> exists gid: nat :: gid in PIV.CapIds(re)
                    && (reg == CP.start_reg(gid) || reg == CP.end_reg(gid))
    ensures forall qid: int, bb: bool :: NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, bb))
              ==> !bb && qid >= 0 && (qid as nat) in PIV.QuantIds(re)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce);
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, pce);
      if pc == pcb || pc == e1 {
      } else if pcb + 1 <= pc < e1 {
        CodeShapeAt(r1, code, pcb + 1, e1, pc);
      } else {
        CodeShapeAt(r2, code, e1 + 1, pce, pc);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce);
      NR.NfaRepIncrRE(r1, code, pcb, e1);
      NR.NfaRepIncrRE(r2, code, e1, pce);
      if pc < e1 {
        CodeShapeAt(r1, code, pcb, e1, pc);
      } else {
        CodeShapeAt(r2, code, e1, pce, pc);
      }
    case Re_quant(nul, qid, q, r1) =>
      assert qid >= 0;                                  // QuantUnique
      if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, pcb, pce);
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid, r1, code, em, pce);
        if pc < em {
          CodeShapeAtMin(mn, qid, r1, code, pcb, em, pc);
        } else {
          CodeShapeAtOpt(kx, q.greedy, qid, r1, code, em, pce, pc);
        }
        assert (qid as nat) in PIV.QuantIds(re);
        return;
      }
      if !(q.min == 0 && q.max == None) {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, pcb, pce);
        var mn1 := (q.min - 1) as nat;
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          CodeShapeAtMin(mn1, qid, r1, code, pcb, em, pc);
        } else if em + 1 <= pc < e1 {
          CodeShapeAt(r1, code, em + 1, e1, pc);
        } else {
          // pc == em: SetQuantToClock(qid, false); pc == e1: the fork
        }
        assert (qid as nat) in PIV.QuantIds(re);
        return;
      }
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
        && pce == e1 + 2;
      NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
      if pc == pcb || pc == pcb + 2 || pc == e1 || pc == e1 + 1 {
      } else if pc == pcb + 1 {
        assert (qid as nat) in PIV.QuantIds(re);
      } else {
        assert pcb + 3 <= pc < e1;
        CodeShapeAt(r1, code, pcb + 3, e1, pc);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1;
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      assert cid >= 0;                                  // CapUnique
      if pc == pcb || pc == e1 {
        assert (cid as nat) in PIV.CapIds(re);
        assert CP.start_reg((cid as nat)) == CP.start_reg(cid);
        assert CP.end_reg((cid as nat)) == CP.end_reg(cid);
      } else {
        assert pcb + 1 <= pc < e1;
        CodeShapeAt(r1, code, pcb + 1, e1, pc);
      }
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
  }

  // =========================================================================
  // Fork direction in quant-fragment code: every fork is forward. Only the
  // do-while scheme (excluded from QuantFragmentRE) emits a backward arm, so
  // under the quant gate the sim's fork case never meets one.
  // =========================================================================
  /** `ForksForwardAt` for forced-copy chains. */
  lemma ForksForwardAtMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat)
    requires NR.QuantFragmentRE(r1)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    requires pcb <= pc < pce
    ensures forall x: int, y: int :: NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
              ==> x > pc && y > pc
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce);
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, pce);
    if pc == pcb {
    } else if pcb + 1 <= pc < e1 {
      ForksForwardAt(r1, code, pcb + 1, e1, pc);
    } else {
      ForksForwardAtMin(k - 1, qid, r1, code, e1, pce, pc);
    }
  }

  /** `ForksForwardAt` for optional-layer chains. */
  lemma ForksForwardAtOpt(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat)
    requires NR.QuantFragmentRE(r1)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    requires pcb <= pc < pce
    ensures forall x: int, y: int :: NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
              ==> x > pc && y > pc
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, pcb + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
    if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 {
    } else if pcb + 3 <= pc < e1 {
      ForksForwardAt(r1, code, pcb + 3, e1, pc);
    } else {
      ForksForwardAtOpt(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc);
    }
  }

  /** Every fork instruction in quant-fragment represented code points both
      arms strictly forward — the do-while's backward arm is the only
      exception in the wider plus fragment, and `QuantFragmentRE` excludes it. */
  lemma ForksForwardAt(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat)
    requires NR.QuantFragmentRE(re)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires pcb <= pc < pce
    ensures forall x: int, y: int :: NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
              ==> x > pc && y > pc
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce);
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, pce);
      if pc == pcb || pc == e1 {
      } else if pcb + 1 <= pc < e1 {
        ForksForwardAt(r1, code, pcb + 1, e1, pc);
      } else {
        ForksForwardAt(r2, code, e1 + 1, pce, pc);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce);
      NR.NfaRepIncrRE(r1, code, pcb, e1);
      NR.NfaRepIncrRE(r2, code, e1, pce);
      if pc < e1 {
        ForksForwardAt(r1, code, pcb, e1, pc);
      } else {
        ForksForwardAt(r2, code, e1, pce, pc);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, pcb, pce);
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid, r1, code, em, pce);
        if pc < em {
          ForksForwardAtMin(mn, qid, r1, code, pcb, em, pc);
        } else {
          ForksForwardAtOpt(kx, q.greedy, qid, r1, code, em, pce, pc);
        }
        return;
      }
      // QuantFragmentRE leaves only the star
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
        && pce == e1 + 2;
      NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
      if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 || pc == e1 + 1 {
      } else {
        assert pcb + 3 <= pc < e1;
        ForksForwardAt(r1, code, pcb + 3, e1, pc);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1;
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      if pc == pcb || pc == e1 {
      } else {
        assert pcb + 1 <= pc < e1;
        ForksForwardAt(r1, code, pcb + 1, e1, pc);
      }
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
  }

  // =========================================================================
  // Cold positions: a backward-arm fork is reachable through zero-width
  // instructions alone. The sim's ea-at-backfork exclusion: a thread with
  // exit_allowed == false never sits at a Cold pc — reads re-arm the flag
  // (no Consume edge) and a CannotExit thread dies at EndLoop (no EndLoop
  // edge), so ¬Cold is closed under every VM step a false-thread survives,
  // except the BeginLoop transition, whose target is statically never Cold
  // (loop bodies are Cold sinks: their fall-through is an EndLoop, and a
  // nested do-while's fork hides behind its NonNullable body).
  // =========================================================================

  /** `pc` reaches a backward-arm fork in at most `n` zero-width steps. */
  ghost predicate ColdF(c: RB.code, pc: nat, n: nat)
    decreases n
  {
    n > 0 &&
    (AR.BackForkAt(c, pc)
     || (match NR.GetPcRE(c, pc)
         case Some(Jmp(np)) => np >= 0 && ColdF(c, np as nat, n - 1)
         case Some(Fork(x, y)) =>
           (x >= 0 && ColdF(c, x as nat, n - 1)) || (y >= 0 && ColdF(c, y as nat, n - 1))
         case Some(SetQuantToClock(_, _)) => ColdF(c, pc + 1, n - 1)
         case Some(SetRegisterToCP(_)) => ColdF(c, pc + 1, n - 1)
         case Some(AnchorAssertion(_)) => ColdF(c, pc + 1, n - 1)
         case Some(CheckOracle(_)) => ColdF(c, pc + 1, n - 1)
         case Some(NegCheckOracle(_)) => ColdF(c, pc + 1, n - 1)
         case Some(BeginLoop) => ColdF(c, pc + 1, n - 1)
         case _ => false))
  }

  /** `pc` reaches a backward-arm fork through zero-width instructions. */
  ghost predicate ColdRE(c: RB.code, pc: nat) {
    exists n: nat :: ColdF(c, pc, n)
  }

  /** Fuel monotonicity for `ColdF`. */
  lemma ColdFMono(c: RB.code, pc: nat, n: nat, n': nat)
    requires n <= n' && ColdF(c, pc, n)
    ensures ColdF(c, pc, n')
    decreases n
  {
  }

  /** Cold at a block's head propagates to the block's end: the only way a
      zero-width path leaves a represented block is the fall-through (loop
      bodies sink into their `EndLoop`, nested do-while forks hide behind
      NonNullable bodies), and the residual path is a sub-derivation. */
  lemma ColdPropagatesF(re: R.regex, c: RB.code, pc1: nat, pc2: nat, n: nat)
    requires NR.LookBehindFragmentRE(re) && NR.NfaRepRE(re, c, pc1, pc2)
    requires ColdF(c, pc1, n)
    ensures ColdF(c, pc2, n)
    decreases n, CP.rsize(re), 1
  {
    match re
    case Re_empty =>
      assert pc1 == pc2;
    case Re_character(ch) =>
      assert !AR.BackForkAt(c, pc1);
      assert false;
    case Re_anchor(a) =>
      assert !AR.BackForkAt(c, pc1);
      assert ColdF(c, pc1 + 1, n - 1);
      ColdFMono(c, pc2, n - 1, n);
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc2))
        && NR.NfaRepRE(r2, c, e1 + 1, pc2);
      NR.NfaRepIncrRE(r1, c, pc1 + 1, e1);
      NR.NfaRepIncrRE(r2, c, e1 + 1, pc2);
      assert !AR.BackForkAt(c, pc1);
      if ColdF(c, pc1 + 1, n - 1) {
        ColdPropagatesF(r1, c, pc1 + 1, e1, n - 1);
        // Cold at the join Jmp routes to pc2
        assert !AR.BackForkAt(c, e1);
        assert ColdF(c, pc2, n - 2);
        ColdFMono(c, pc2, n - 2, n);
      } else {
        assert ColdF(c, e1 + 1, n - 1);
        ColdPropagatesF(r2, c, e1 + 1, pc2, n - 1);
        ColdFMono(c, pc2, n - 1, n);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, c, pc1, e1) && NR.NfaRepRE(r2, c, e1, pc2);
      ColdPropagatesF(r1, c, pc1, e1, n);
      ColdPropagatesF(r2, c, e1, pc2, n);
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pc2 == e1 + 1;
      assert !AR.BackForkAt(c, pc1);
      assert ColdF(c, pc1 + 1, n - 1);
      ColdPropagatesF(r1, c, pc1 + 1, e1, n - 1);
      assert !AR.BackForkAt(c, e1);
      assert ColdF(c, pc2, n - 2);
      ColdFMono(c, pc2, n - 2, n);
    case Re_lookaround(lid, la, r1) =>
      // one zero-width gate instruction: ColdF crosses it exactly as it
      // crosses an anchor (the body lives in the per-lid tables, not here)
      assert !AR.BackForkAt(c, pc1);
      assert ColdF(c, pc1 + 1, n - 1);
      ColdFMono(c, pc2, n - 1, n);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        // the star: the body is a Cold sink (EndLoop has no edge)
        var e1: nat :| NR.GetPcRE(c, pc1) == Some(if q.greedy then RB.Fork(pc1 + 1, e1 + 2) else RB.Fork(e1 + 2, pc1 + 1))
          && NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, c, pc1 + 3, e1)
          && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(pc1))
          && pc2 == e1 + 2;
        NR.NfaRepIncrRE(r1, c, pc1 + 3, e1);
        assert !AR.BackForkAt(c, pc1);
        if ColdF(c, pc1 + 1, n - 1) {
          assert !AR.BackForkAt(c, pc1 + 1);
          assert ColdF(c, pc1 + 2, n - 2);
          assert !AR.BackForkAt(c, pc1 + 2);
          assert ColdF(c, pc1 + 3, n - 3);
          ColdPropagatesF(r1, c, pc1 + 3, e1, n - 3);
          assert !AR.BackForkAt(c, e1);
          assert false;   // EndLoop has no Cold edge
        } else {
          assert ColdF(c, pc2, n - 1);
          ColdFMono(c, pc2, n - 1, n);
        }
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, c, pc1, pc2);
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        ColdPropagatesMinF(mn, qid, r1, c, pc1, em, n);
        ColdPropagatesOptF(kx, q.greedy, qid, r1, c, em, pc2, n);
      } else {
        // the do-while: the NonNullable body walls off its own fork
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, c, pc1, pc2);
        var mn1 := (q.min - 1) as nat;
        ColdPropagatesMinF(mn1, qid, r1, c, pc1, em, n);
        assert !AR.BackForkAt(c, em);
        assert ColdF(c, em + 1, n - 1);
        ColdNNF(r1, c, em + 1, e1, n - 1);
        assert false;
      }
  }

  /** `ColdPropagatesF` along a forced-copy chain. */
  lemma ColdPropagatesMinF(k: nat, qid: R.quantid, r1: R.regex, c: RB.code, pcb: nat, pce: nat, n: nat)
    requires NR.LookBehindFragmentRE(r1) && NR.NfaRepMinRE(k, qid, r1, c, pcb, pce)
    requires ColdF(c, pcb, n)
    ensures ColdF(c, pce, n)
    decreases n, CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(c, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, c, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, c, e1, pce);
    assert !AR.BackForkAt(c, pcb);
    assert ColdF(c, pcb + 1, n - 1);
    ColdPropagatesF(r1, c, pcb + 1, e1, n - 1);
    ColdPropagatesMinF(k - 1, qid, r1, c, e1, pce, n - 1);
    ColdFMono(c, pce, n - 1, n);
  }

  /** `ColdPropagatesF` along an optional-layer chain (each layer's body is a
      Cold sink; only the skip arm carries the path forward). */
  lemma ColdPropagatesOptF(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, c: RB.code, pcb: nat, pce: nat, n: nat)
    requires NR.LookBehindFragmentRE(r1) && NR.NfaRepOptRE(k, greedy, qid, r1, c, pcb, pce)
    requires ColdF(c, pcb, n)
    ensures ColdF(c, pce, n)
    decreases n, CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(c, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(c, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(c, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, c, pcb + 3, e1)
      && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, c, e1 + 1, pce);
    NR.NfaRepIncrRE(r1, c, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, c, e1 + 1, pce);
    assert !AR.BackForkAt(c, pcb);
    if ColdF(c, pcb + 1, n - 1) {
      assert !AR.BackForkAt(c, pcb + 1);
      assert ColdF(c, pcb + 2, n - 2);
      assert !AR.BackForkAt(c, pcb + 2);
      assert ColdF(c, pcb + 3, n - 3);
      ColdPropagatesF(r1, c, pcb + 3, e1, n - 3);
      assert !AR.BackForkAt(c, e1);
      assert false;   // EndLoop has no Cold edge
    } else {
      assert ColdF(c, pce, n - 1);
      ColdFMono(c, pce, n - 1, n);
    }
  }

  /** A NonNullable block's head is never Cold: every zero-width path into it
      dies before the fall-through (the block cannot be crossed without a
      read), and any nested backward fork hides behind a NonNullable body of
      its own. */
  lemma ColdNNF(re: R.regex, c: RB.code, pc1: nat, pc2: nat, n: nat)
    requires NR.LookBehindFragmentRE(re) && NR.NfaRepRE(re, c, pc1, pc2)
    requires R.nullable(re) == R.NonNullable
    requires ColdF(c, pc1, n)
    ensures false
    decreases n, CP.rsize(re), 0
  {
    match re
    case Re_empty =>            // nullable: vacuous
    case Re_character(ch) =>
      assert !AR.BackForkAt(c, pc1);
    case Re_anchor(a) =>        // CDN: vacuous
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      // null_or: NonNullable needs both branches NonNullable
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc2))
        && NR.NfaRepRE(r2, c, e1 + 1, pc2);
      NR.NfaRepIncrRE(r1, c, pc1 + 1, e1);
      NR.NfaRepIncrRE(r2, c, e1 + 1, pc2);
      assert !AR.BackForkAt(c, pc1);
      if ColdF(c, pc1 + 1, n - 1) {
        ColdNNF(r1, c, pc1 + 1, e1, n - 1);
      } else {
        ColdNNF(r2, c, e1 + 1, pc2, n - 1);
      }
    case Re_con(r1, r2) =>
      // null_and: NonNullable when either side is
      var e1: nat :| NR.NfaRepRE(r1, c, pc1, e1) && NR.NfaRepRE(r2, c, e1, pc2);
      if R.nullable(r1) == R.NonNullable {
        ColdNNF(r1, c, pc1, e1, n);
      } else {
        assert R.nullable(r2) == R.NonNullable;
        ColdPropagatesF(r1, c, pc1, e1, n);
        ColdNNF(r2, c, e1, pc2, n);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pc2 == e1 + 1;
      assert !AR.BackForkAt(c, pc1);
      ColdNNF(r1, c, pc1 + 1, e1, n - 1);
    case Re_quant(nul, qid, q, r1) =>
      // min == 0 yields CINullable, so min > 0 and the body is NonNullable
      assert q.min > 0 && R.nullable(r1) == R.NonNullable;
      if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, c, pc1, pc2);
        var mn := q.min as nat;
        var eb: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qid, false))
          && NR.NfaRepRE(r1, c, pc1 + 1, eb)
          && NR.NfaRepMinRE(mn - 1, qid, r1, c, eb, em);
        assert !AR.BackForkAt(c, pc1);
        ColdNNF(r1, c, pc1 + 1, eb, n - 1);
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, c, pc1, pc2);
        var mn1 := (q.min - 1) as nat;
        if mn1 > 0 {
          var eb: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qid, false))
            && NR.NfaRepRE(r1, c, pc1 + 1, eb)
            && NR.NfaRepMinRE(mn1 - 1, qid, r1, c, eb, em);
          assert !AR.BackForkAt(c, pc1);
          ColdNNF(r1, c, pc1 + 1, eb, n - 1);
        } else {
          assert em == pc1;
          assert !AR.BackForkAt(c, pc1);
          ColdNNF(r1, c, pc1 + 1, e1, n - 1);
        }
      }
  }

  // =========================================================================
  // The static corollaries the invariant threading consumes
  // =========================================================================

  /** The entry pc of a compiled fragment is never Cold: a Cold path would
      propagate to the final `Accept`, which has no Cold edge. */
  lemma NotColdEntryRE(re: R.regex, c: RB.code, endl: nat)
    requires NR.LookBehindFragmentRE(re) && NR.NfaRepRE(re, c, 0, endl)
    requires NR.GetPcRE(c, endl) == Some(RB.Accept)
    ensures !ColdRE(c, 0)
  {
    if ColdRE(c, 0) {
      var n: nat :| ColdF(c, 0, n);
      ColdPropagatesF(re, c, 0, endl, n);
      assert !AR.BackForkAt(c, endl);
      assert false;
    }
  }

  /** L4 depth-k (ADDITIVE): `NotColdEntryRE` under the nested fragment (uses
      `ColdPropagatesFNested`). */
  lemma NotColdEntryRENested(re: R.regex, c: RB.code, endl: nat)
    requires NR.NestedFragmentRE(re) && NR.NfaRepRE(re, c, 0, endl)
    requires NR.GetPcRE(c, endl) == Some(RB.Accept)
    ensures !ColdRE(c, 0)
  {
    if ColdRE(c, 0) {
      var n: nat :| ColdF(c, 0, n);
      ColdPropagatesFNested(re, c, 0, endl, n);
      assert !AR.BackForkAt(c, endl);
      assert false;
    }
  }

  /** `BeginLoopColdSafeAt` for forced-copy chains. */
  lemma BeginLoopColdSafeAtMin(k: nat, qid: R.quantid, r1: R.regex, c: RB.code, pcb: nat, pce: nat, p: nat)
    requires NR.LookBehindFragmentRE(r1) && NR.NfaRepMinRE(k, qid, r1, c, pcb, pce)
    requires pcb <= p < pce
    requires NR.GetPcRE(c, p) == Some(RB.BeginLoop)
    ensures !ColdRE(c, p + 1)
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(c, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, c, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, c, e1, pce);
    NR.NfaRepIncrRE(r1, c, pcb + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, c, e1, pce);
    if pcb + 1 <= p < e1 {
      BeginLoopColdSafeAt(r1, c, pcb + 1, e1, p);
    } else {
      assert p != pcb;
      BeginLoopColdSafeAtMin(k - 1, qid, r1, c, e1, pce, p);
    }
  }

  /** `BeginLoopColdSafeAt` for optional-layer chains. */
  lemma BeginLoopColdSafeAtOpt(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, c: RB.code, pcb: nat, pce: nat, p: nat)
    requires NR.LookBehindFragmentRE(r1) && NR.NfaRepOptRE(k, greedy, qid, r1, c, pcb, pce)
    requires pcb <= p < pce
    requires NR.GetPcRE(c, p) == Some(RB.BeginLoop)
    ensures !ColdRE(c, p + 1)
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(c, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(c, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(c, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, c, pcb + 3, e1)
      && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, c, e1 + 1, pce);
    NR.NfaRepIncrRE(r1, c, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, c, e1 + 1, pce);
    if p == pcb + 2 {
      if ColdRE(c, p + 1) {
        var n: nat :| ColdF(c, pcb + 3, n);
        ColdPropagatesF(r1, c, pcb + 3, e1, n);
        assert !AR.BackForkAt(c, e1);
        assert false;
      }
    } else if pcb + 3 <= p < e1 {
      BeginLoopColdSafeAt(r1, c, pcb + 3, e1, p);
    } else {
      assert p != pcb && p != pcb + 1 && p != e1;
      BeginLoopColdSafeAtOpt(k - 1, greedy, qid, r1, c, e1 + 1, pce, p);
    }
  }

  /** Every `BeginLoop` in represented plus-fragment code opens a loop body
      whose head is not Cold — the star/layer bodies sink into their
      `EndLoop`, and a do-while's fork hides behind its NonNullable body. The
      static fact the invariant's true→false transition (the VM's `BeginLoop`
      step) consumes. */
  lemma BeginLoopColdSafeAt(re: R.regex, c: RB.code, pcb: nat, pce: nat, p: nat)
    requires NR.LookBehindFragmentRE(re) && NR.NfaRepRE(re, c, pcb, pce)
    requires pcb <= p < pce
    requires NR.GetPcRE(c, p) == Some(RB.BeginLoop)
    ensures !ColdRE(c, p + 1)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
    case Re_anchor(a) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(c, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, c, pcb + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, c, e1 + 1, pce);
      NR.NfaRepIncrRE(r1, c, pcb + 1, e1);
      NR.NfaRepIncrRE(r2, c, e1 + 1, pce);
      if pcb + 1 <= p < e1 {
        BeginLoopColdSafeAt(r1, c, pcb + 1, e1, p);
      } else {
        assert p != pcb && p != e1;
        BeginLoopColdSafeAt(r2, c, e1 + 1, pce, p);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, c, pcb, e1) && NR.NfaRepRE(r2, c, e1, pce);
      NR.NfaRepIncrRE(r1, c, pcb, e1);
      NR.NfaRepIncrRE(r2, c, e1, pce);
      if p < e1 {
        BeginLoopColdSafeAt(r1, c, pcb, e1, p);
      } else {
        BeginLoopColdSafeAt(r2, c, e1, pce, p);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(c, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, c, pcb + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1;
      NR.NfaRepIncrRE(r1, c, pcb + 1, e1);
      assert p != pcb && p != e1;
      BeginLoopColdSafeAt(r1, c, pcb + 1, e1, p);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| NR.GetPcRE(c, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
          && NR.GetPcRE(c, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(c, pcb + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, c, pcb + 3, e1)
          && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(pcb))
          && pce == e1 + 2;
        NR.NfaRepIncrRE(r1, c, pcb + 3, e1);
        if p == pcb + 2 {
          if ColdRE(c, p + 1) {
            var n: nat :| ColdF(c, pcb + 3, n);
            ColdPropagatesF(r1, c, pcb + 3, e1, n);
            assert !AR.BackForkAt(c, e1);
            assert false;
          }
        } else {
          assert p != pcb && p != pcb + 1 && p != e1 && p != e1 + 1;
          assert pcb + 3 <= p < e1;
          BeginLoopColdSafeAt(r1, c, pcb + 3, e1, p);
        }
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, c, pcb, pce);
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        NR.NfaRepIncrMinRE(mn, qid, r1, c, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid, r1, c, em, pce);
        if p < em {
          BeginLoopColdSafeAtMin(mn, qid, r1, c, pcb, em, p);
        } else {
          BeginLoopColdSafeAtOpt(kx, q.greedy, qid, r1, c, em, pce, p);
        }
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, c, pcb, pce);
        var mn1 := (q.min - 1) as nat;
        NR.NfaRepIncrMinRE(mn1, qid, r1, c, pcb, em);
        NR.NfaRepIncrRE(r1, c, em + 1, e1);
        if p < em {
          BeginLoopColdSafeAtMin(mn1, qid, r1, c, pcb, em, p);
        } else {
          assert p != em && p != e1;
          assert em + 1 <= p < e1;
          BeginLoopColdSafeAt(r1, c, em + 1, e1, p);
        }
      }
  }

  // =========================================================================
  // L4 depth-k (ADDITIVE): the Cold-propagation + BeginLoop-Cold tower
  // generalized from `LookBehindFragmentRE` to the arbitrary-nesting
  // `NestedFragmentRE`. Every `Re_lookaround` case is a SINGLE zero-width gate
  // (the body lives in the per-lid tables, not in this code), so no case
  // descends into the body — the proofs are depth-agnostic verbatim copies with
  // the fragment swap + recursion redirected to the `*Nested` siblings. The
  // `ColdFMono`/`NfaRepIncr*`/`NfaRep*Inv`/`AR.BackForkAt` helpers are already
  // fragment-blind and reused directly.
  // =========================================================================

  /** `ColdNNF` under the nested fragment. */
  lemma ColdNNFNested(re: R.regex, c: RB.code, pc1: nat, pc2: nat, n: nat)
    requires NR.NestedFragmentRE(re) && NR.NfaRepRE(re, c, pc1, pc2)
    requires R.nullable(re) == R.NonNullable
    requires ColdF(c, pc1, n)
    ensures false
    decreases n, CP.rsize(re), 0
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
      assert !AR.BackForkAt(c, pc1);
    case Re_anchor(a) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc2))
        && NR.NfaRepRE(r2, c, e1 + 1, pc2);
      NR.NfaRepIncrRE(r1, c, pc1 + 1, e1);
      NR.NfaRepIncrRE(r2, c, e1 + 1, pc2);
      assert !AR.BackForkAt(c, pc1);
      if ColdF(c, pc1 + 1, n - 1) {
        ColdNNFNested(r1, c, pc1 + 1, e1, n - 1);
      } else {
        ColdNNFNested(r2, c, e1 + 1, pc2, n - 1);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, c, pc1, e1) && NR.NfaRepRE(r2, c, e1, pc2);
      if R.nullable(r1) == R.NonNullable {
        ColdNNFNested(r1, c, pc1, e1, n);
      } else {
        assert R.nullable(r2) == R.NonNullable;
        ColdPropagatesFNested(r1, c, pc1, e1, n);
        ColdNNFNested(r2, c, e1, pc2, n);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pc2 == e1 + 1;
      assert !AR.BackForkAt(c, pc1);
      ColdNNFNested(r1, c, pc1 + 1, e1, n - 1);
    case Re_quant(nul, qid, q, r1) =>
      assert q.min > 0 && R.nullable(r1) == R.NonNullable;
      if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, c, pc1, pc2);
        var mn := q.min as nat;
        var eb: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qid, false))
          && NR.NfaRepRE(r1, c, pc1 + 1, eb)
          && NR.NfaRepMinRE(mn - 1, qid, r1, c, eb, em);
        assert !AR.BackForkAt(c, pc1);
        ColdNNFNested(r1, c, pc1 + 1, eb, n - 1);
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, c, pc1, pc2);
        var mn1 := (q.min - 1) as nat;
        if mn1 > 0 {
          var eb: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qid, false))
            && NR.NfaRepRE(r1, c, pc1 + 1, eb)
            && NR.NfaRepMinRE(mn1 - 1, qid, r1, c, eb, em);
          assert !AR.BackForkAt(c, pc1);
          ColdNNFNested(r1, c, pc1 + 1, eb, n - 1);
        } else {
          assert em == pc1;
          assert !AR.BackForkAt(c, pc1);
          ColdNNFNested(r1, c, pc1 + 1, e1, n - 1);
        }
      }
  }

  /** `ColdPropagatesMinF` under the nested fragment. */
  lemma ColdPropagatesMinFNested(k: nat, qid: R.quantid, r1: R.regex, c: RB.code, pcb: nat, pce: nat, n: nat)
    requires NR.NestedFragmentRE(r1) && NR.NfaRepMinRE(k, qid, r1, c, pcb, pce)
    requires ColdF(c, pcb, n)
    ensures ColdF(c, pce, n)
    decreases n, CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(c, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, c, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, c, e1, pce);
    assert !AR.BackForkAt(c, pcb);
    assert ColdF(c, pcb + 1, n - 1);
    ColdPropagatesFNested(r1, c, pcb + 1, e1, n - 1);
    ColdPropagatesMinFNested(k - 1, qid, r1, c, e1, pce, n - 1);
    ColdFMono(c, pce, n - 1, n);
  }

  /** `ColdPropagatesOptF` under the nested fragment. */
  lemma ColdPropagatesOptFNested(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, c: RB.code, pcb: nat, pce: nat, n: nat)
    requires NR.NestedFragmentRE(r1) && NR.NfaRepOptRE(k, greedy, qid, r1, c, pcb, pce)
    requires ColdF(c, pcb, n)
    ensures ColdF(c, pce, n)
    decreases n, CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(c, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(c, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(c, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, c, pcb + 3, e1)
      && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, c, e1 + 1, pce);
    NR.NfaRepIncrRE(r1, c, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, c, e1 + 1, pce);
    assert !AR.BackForkAt(c, pcb);
    if ColdF(c, pcb + 1, n - 1) {
      assert !AR.BackForkAt(c, pcb + 1);
      assert ColdF(c, pcb + 2, n - 2);
      assert !AR.BackForkAt(c, pcb + 2);
      assert ColdF(c, pcb + 3, n - 3);
      ColdPropagatesFNested(r1, c, pcb + 3, e1, n - 3);
      assert !AR.BackForkAt(c, e1);
      assert false;
    } else {
      assert ColdF(c, pce, n - 1);
      ColdFMono(c, pce, n - 1, n);
    }
  }

  /** `ColdPropagatesF` under the nested fragment. */
  lemma ColdPropagatesFNested(re: R.regex, c: RB.code, pc1: nat, pc2: nat, n: nat)
    requires NR.NestedFragmentRE(re) && NR.NfaRepRE(re, c, pc1, pc2)
    requires ColdF(c, pc1, n)
    ensures ColdF(c, pc2, n)
    decreases n, CP.rsize(re), 1
  {
    match re
    case Re_empty =>
      assert pc1 == pc2;
    case Re_character(ch) =>
      assert !AR.BackForkAt(c, pc1);
      assert false;
    case Re_anchor(a) =>
      assert !AR.BackForkAt(c, pc1);
      assert ColdF(c, pc1 + 1, n - 1);
      ColdFMono(c, pc2, n - 1, n);
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc2))
        && NR.NfaRepRE(r2, c, e1 + 1, pc2);
      NR.NfaRepIncrRE(r1, c, pc1 + 1, e1);
      NR.NfaRepIncrRE(r2, c, e1 + 1, pc2);
      assert !AR.BackForkAt(c, pc1);
      if ColdF(c, pc1 + 1, n - 1) {
        ColdPropagatesFNested(r1, c, pc1 + 1, e1, n - 1);
        assert !AR.BackForkAt(c, e1);
        assert ColdF(c, pc2, n - 2);
        ColdFMono(c, pc2, n - 2, n);
      } else {
        assert ColdF(c, e1 + 1, n - 1);
        ColdPropagatesFNested(r2, c, e1 + 1, pc2, n - 1);
        ColdFMono(c, pc2, n - 1, n);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, c, pc1, e1) && NR.NfaRepRE(r2, c, e1, pc2);
      ColdPropagatesFNested(r1, c, pc1, e1, n);
      ColdPropagatesFNested(r2, c, e1, pc2, n);
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pc2 == e1 + 1;
      assert !AR.BackForkAt(c, pc1);
      assert ColdF(c, pc1 + 1, n - 1);
      ColdPropagatesFNested(r1, c, pc1 + 1, e1, n - 1);
      assert !AR.BackForkAt(c, e1);
      assert ColdF(c, pc2, n - 2);
      ColdFMono(c, pc2, n - 2, n);
    case Re_lookaround(lid, la, r1) =>
      assert !AR.BackForkAt(c, pc1);
      assert ColdF(c, pc1 + 1, n - 1);
      ColdFMono(c, pc2, n - 1, n);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| NR.GetPcRE(c, pc1) == Some(if q.greedy then RB.Fork(pc1 + 1, e1 + 2) else RB.Fork(e1 + 2, pc1 + 1))
          && NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, c, pc1 + 3, e1)
          && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(pc1))
          && pc2 == e1 + 2;
        NR.NfaRepIncrRE(r1, c, pc1 + 3, e1);
        assert !AR.BackForkAt(c, pc1);
        if ColdF(c, pc1 + 1, n - 1) {
          assert !AR.BackForkAt(c, pc1 + 1);
          assert ColdF(c, pc1 + 2, n - 2);
          assert !AR.BackForkAt(c, pc1 + 2);
          assert ColdF(c, pc1 + 3, n - 3);
          ColdPropagatesFNested(r1, c, pc1 + 3, e1, n - 3);
          assert !AR.BackForkAt(c, e1);
          assert false;
        } else {
          assert ColdF(c, pc2, n - 1);
          ColdFMono(c, pc2, n - 1, n);
        }
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, c, pc1, pc2);
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        ColdPropagatesMinFNested(mn, qid, r1, c, pc1, em, n);
        ColdPropagatesOptFNested(kx, q.greedy, qid, r1, c, em, pc2, n);
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, c, pc1, pc2);
        var mn1 := (q.min - 1) as nat;
        ColdPropagatesMinFNested(mn1, qid, r1, c, pc1, em, n);
        assert !AR.BackForkAt(c, em);
        assert ColdF(c, em + 1, n - 1);
        ColdNNFNested(r1, c, em + 1, e1, n - 1);
        assert false;
      }
  }

  /** `BeginLoopColdSafeAtMin` under the nested fragment. */
  lemma BeginLoopColdSafeAtMinNested(k: nat, qid: R.quantid, r1: R.regex, c: RB.code, pcb: nat, pce: nat, p: nat)
    requires NR.NestedFragmentRE(r1) && NR.NfaRepMinRE(k, qid, r1, c, pcb, pce)
    requires pcb <= p < pce
    requires NR.GetPcRE(c, p) == Some(RB.BeginLoop)
    ensures !ColdRE(c, p + 1)
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(c, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, c, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, c, e1, pce);
    NR.NfaRepIncrRE(r1, c, pcb + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, c, e1, pce);
    if pcb + 1 <= p < e1 {
      BeginLoopColdSafeAtNested(r1, c, pcb + 1, e1, p);
    } else {
      assert p != pcb;
      BeginLoopColdSafeAtMinNested(k - 1, qid, r1, c, e1, pce, p);
    }
  }

  /** `BeginLoopColdSafeAtOpt` under the nested fragment. */
  lemma BeginLoopColdSafeAtOptNested(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, c: RB.code, pcb: nat, pce: nat, p: nat)
    requires NR.NestedFragmentRE(r1) && NR.NfaRepOptRE(k, greedy, qid, r1, c, pcb, pce)
    requires pcb <= p < pce
    requires NR.GetPcRE(c, p) == Some(RB.BeginLoop)
    ensures !ColdRE(c, p + 1)
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(c, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(c, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(c, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, c, pcb + 3, e1)
      && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, c, e1 + 1, pce);
    NR.NfaRepIncrRE(r1, c, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, c, e1 + 1, pce);
    if p == pcb + 2 {
      if ColdRE(c, p + 1) {
        var n: nat :| ColdF(c, pcb + 3, n);
        ColdPropagatesFNested(r1, c, pcb + 3, e1, n);
        assert !AR.BackForkAt(c, e1);
        assert false;
      }
    } else if pcb + 3 <= p < e1 {
      BeginLoopColdSafeAtNested(r1, c, pcb + 3, e1, p);
    } else {
      assert p != pcb && p != pcb + 1 && p != e1;
      BeginLoopColdSafeAtOptNested(k - 1, greedy, qid, r1, c, e1 + 1, pce, p);
    }
  }

  /** `BeginLoopColdSafeAt` under the nested fragment. */
  lemma BeginLoopColdSafeAtNested(re: R.regex, c: RB.code, pcb: nat, pce: nat, p: nat)
    requires NR.NestedFragmentRE(re) && NR.NfaRepRE(re, c, pcb, pce)
    requires pcb <= p < pce
    requires NR.GetPcRE(c, p) == Some(RB.BeginLoop)
    ensures !ColdRE(c, p + 1)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
    case Re_anchor(a) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(c, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, c, pcb + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, c, e1 + 1, pce);
      NR.NfaRepIncrRE(r1, c, pcb + 1, e1);
      NR.NfaRepIncrRE(r2, c, e1 + 1, pce);
      if pcb + 1 <= p < e1 {
        BeginLoopColdSafeAtNested(r1, c, pcb + 1, e1, p);
      } else {
        assert p != pcb && p != e1;
        BeginLoopColdSafeAtNested(r2, c, e1 + 1, pce, p);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, c, pcb, e1) && NR.NfaRepRE(r2, c, e1, pce);
      NR.NfaRepIncrRE(r1, c, pcb, e1);
      NR.NfaRepIncrRE(r2, c, e1, pce);
      if p < e1 {
        BeginLoopColdSafeAtNested(r1, c, pcb, e1, p);
      } else {
        BeginLoopColdSafeAtNested(r2, c, e1, pce, p);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(c, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, c, pcb + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1;
      NR.NfaRepIncrRE(r1, c, pcb + 1, e1);
      assert p != pcb && p != e1;
      BeginLoopColdSafeAtNested(r1, c, pcb + 1, e1, p);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| NR.GetPcRE(c, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
          && NR.GetPcRE(c, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(c, pcb + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, c, pcb + 3, e1)
          && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(pcb))
          && pce == e1 + 2;
        NR.NfaRepIncrRE(r1, c, pcb + 3, e1);
        if p == pcb + 2 {
          if ColdRE(c, p + 1) {
            var n: nat :| ColdF(c, pcb + 3, n);
            ColdPropagatesFNested(r1, c, pcb + 3, e1, n);
            assert !AR.BackForkAt(c, e1);
            assert false;
          }
        } else {
          assert p != pcb && p != pcb + 1 && p != e1 && p != e1 + 1;
          assert pcb + 3 <= p < e1;
          BeginLoopColdSafeAtNested(r1, c, pcb + 3, e1, p);
        }
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, c, pcb, pce);
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        NR.NfaRepIncrMinRE(mn, qid, r1, c, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid, r1, c, em, pce);
        if p < em {
          BeginLoopColdSafeAtMinNested(mn, qid, r1, c, pcb, em, p);
        } else {
          BeginLoopColdSafeAtOptNested(kx, q.greedy, qid, r1, c, em, pce, p);
        }
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, c, pcb, pce);
        var mn1 := (q.min - 1) as nat;
        NR.NfaRepIncrMinRE(mn1, qid, r1, c, pcb, em);
        NR.NfaRepIncrRE(r1, c, em + 1, e1);
        if p < em {
          BeginLoopColdSafeAtMinNested(mn1, qid, r1, c, pcb, em, p);
        } else {
          assert p != em && p != e1;
          assert em + 1 <= p < e1;
          BeginLoopColdSafeAtNested(r1, c, em + 1, e1, p);
        }
      }
  }

  // Node ids are bounded by the max functions the pipeline sizes register
  // files with.
  /** Every capture id in `re` is at most `R.max_group(re)` — grounds the
      engine's capture-register file size. */
  lemma CapIdsLEMaxGroup(re: R.regex)
    ensures forall g: nat :: g in PIV.CapIds(re) ==> g <= R.max_group(re)
    decreases re
  {
    match re
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) => CapIdsLEMaxGroup(r1); CapIdsLEMaxGroup(r2);
    case Re_con(r1, r2) => CapIdsLEMaxGroup(r1); CapIdsLEMaxGroup(r2);
    case Re_quant(_, _, _, r1) => CapIdsLEMaxGroup(r1);
    case Re_capture(cid, r1) => CapIdsLEMaxGroup(r1);
    case Re_lookaround(_, _, r1) => CapIdsLEMaxGroup(r1);
  }

  /** Every quant id in `re` is at most `R.max_quant(re)` — grounds the
      engine's quant-register file size. */
  lemma QuantIdsLEMaxQuant(re: R.regex)
    ensures forall q: nat :: q in PIV.QuantIds(re) ==> q <= R.max_quant(re)
    decreases re
  {
    match re
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) => QuantIdsLEMaxQuant(r1); QuantIdsLEMaxQuant(r2);
    case Re_con(r1, r2) => QuantIdsLEMaxQuant(r1); QuantIdsLEMaxQuant(r2);
    case Re_quant(_, qid, _, r1) => QuantIdsLEMaxQuant(r1);
    case Re_capture(_, r1) => QuantIdsLEMaxQuant(r1);
    case Re_lookaround(_, _, r1) => QuantIdsLEMaxQuant(r1);
  }

  // The Reset analog: at a pc holding SetQuantToClock(qid, false), the path
  // claims assemble into PathPresentQ — the sole positional hypothesis of
  // GmOfLiveResetGMReset (the rest is clock-backbone).
  /** The reset-site analog of `NestInvOpenSite`: at a `pc` holding quant
      `qid`'s `SetQuantToClock` (reset) instruction, `NestInvRE`'s path claims
      assemble into `PathPresentQ` — the sole positional hypothesis
      `GmOfLiveResetGMReset` needs (the rest follows from the clock
      backbone). */
  /** `NestInvResetSite` for forced-copy chains: the site is either a copy
      head (pinning `qid` to this quantifier's own id) or sits inside a body,
      where the path claims descend at the stamp threshold. */
  lemma NestInvResetSiteMin(k: nat, qn: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                            cc: seq<int>, qc: seq<int>, mx: int, qid: nat)
    requires NR.NfaRepMinRE(k, qn, r1, code, pcb, pce)
    requires PIV.CapUnique(r1) && PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    requires NestInvMinRE(k, qn, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
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
            && NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, AI.get_idx(qc, qn))
          else NestInvMinRE(k - 1, qn, r1, code, e1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    if pc == pcb {
      // the copy head: the instruction pins qid == qn.
      assert (qid as int) == qn;
    } else if pcb + 1 <= pc < e1 {
      var qv := AI.get_idx(qc, qn);
      NestInvResetSite(r1, code, pcb + 1, e1, pc, cc, qc, qv, qid);
    } else {
      NestInvResetSiteMin(k - 1, qn, r1, code, e1, pce, pc, cc, qc, mx, qid);
    }
  }

  /** `NestInvResetSite` for optional-layer chains. */
  lemma NestInvResetSiteOpt(k: nat, greedy: bool, qn: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                            cc: seq<int>, qc: seq<int>, mx: int, qid: nat)
    requires NR.NfaRepOptRE(k, greedy, qn, r1, code, pcb, pce)
    requires PIV.CapUnique(r1) && PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    requires NestInvOptRE(k, greedy, qn, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
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
            AI.get_idx(qc, qn) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qn))
          else if pcb + 3 <= pc < e1 then
            AI.get_idx(qc, qn) >= mx
            && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qn))
          else if pc == e1 then AI.get_idx(qc, qn) >= mx
          else NestInvOptRE(k - 1, greedy, qn, r1, code, e1 + 1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    if pc == pcb + 1 {
      // the layer stamp: the instruction pins qid == qn.
      assert (qid as int) == qn;
    } else if pc == pcb || pc == pcb + 2 || pc == e1 {
      assert false;                                 // Fork/BeginLoop/EndLoop
    } else if pcb + 3 <= pc < e1 {
      var qv := AI.get_idx(qc, qn);
      NestInvResetSite(r1, code, pcb + 3, e1, pc, cc, qc, qv, qid);
    } else {
      NestInvResetSiteOpt(k - 1, greedy, qn, r1, code, e1 + 1, pce, pc, cc, qc, mx, qid);
    }
  }

  lemma NestInvResetSite(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                         cc: seq<int>, qc: seq<int>, mx: int, qid: nat)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestInvRE(re, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
    ensures qid in PIV.QuantIds(re)
    ensures qid in PIV.QuantIdsOutsideLooks(re)   // L3a: SetQuantToClock sites are outside-look
    ensures PIV.PathPresentQ(re, cc, qc, mx, qid)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
      assert pc == pcb;
      assert false;
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && if pc == pcb then AllStaleRE(r1, cc, mx) && AllStaleRE(r2, cc, mx)
           else if pcb + 1 <= pc < e1 then
             NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else if pc == e1 then true
           else NestInvRE(r2, code, e1 + 1, pce, pc, cc, qc, mx);
      if pc == pcb {
        assert false;
      } else if pcb + 1 <= pc < e1 {
        NestInvResetSite(r1, code, pcb + 1, e1, pc, cc, qc, mx, qid);
      } else if pc == e1 {
        assert false;
      } else {
        NestInvResetSite(r2, code, e1 + 1, pce, pc, cc, qc, mx, qid);
        assert qid !in PIV.QuantIds(r1) by {
          if qid in PIV.QuantIds(r1) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && if pc < e1 then NestInvRE(r1, code, pcb, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else NestInvRE(r2, code, e1, pce, pc, cc, qc, mx);
      if pc < e1 {
        NestInvResetSite(r1, code, pcb, e1, pc, cc, qc, mx, qid);
      } else {
        NestInvResetSite(r2, code, e1, pce, pc, cc, qc, mx, qid);
        assert qid !in PIV.QuantIds(r1) by {
          if qid in PIV.QuantIds(r1) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
      }
    case Re_quant(nul, qid0, q, r1) =>
      assert qid0 >= 0;                             // QuantUnique
      if q.max.Some? {
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid0, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid0, r1, code, em, pce)
          && (if pc < em then NestInvMinRE(mn, qid0, r1, code, pcb, em, pc, cc, qc, mx)
              else NestInvOptRE(kx, q.greedy, qid0, r1, code, em, pce, pc, cc, qc, mx));
        NR.NfaRepIncrMinRE(mn, qid0, r1, code, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid0, r1, code, em, pce);
        if pc < em {
          NestInvResetSiteMin(mn, qid0, r1, code, pcb, em, pc, cc, qc, mx, qid);
        } else {
          NestInvResetSiteOpt(kx, q.greedy, qid0, r1, code, em, pce, pc, cc, qc, mx, qid);
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
          && (if pc < em then NestInvMinRE(mn1, qid0, r1, code, pcb, em, pc, cc, qc, mx)
              else if pc == em then true
              else if em + 1 <= pc < e1 then
                AI.get_idx(qc, qid0) >= mx
                && NestInvRE(r1, code, em + 1, e1, pc, cc, qc, AI.get_idx(qc, qid0))
              else AI.get_idx(qc, qid0) >= mx);
        NR.NfaRepIncrMinRE(mn1, qid0, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          NestInvResetSiteMin(mn1, qid0, r1, code, pcb, em, pc, cc, qc, mx, qid);
        } else if pc == em {
          // THE last-copy clock-mark: the instruction pins qid == qid0
          assert (qid as int) == qid0;
        } else if em + 1 <= pc < e1 {
          var qv := AI.get_idx(qc, qid0);
          NestInvResetSite(r1, code, em + 1, e1, pc, cc, qc, qv, qid);
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
             AI.get_idx(qc, qid0) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qid0))
           else if pcb + 3 <= pc < e1 then
             AI.get_idx(qc, qid0) >= mx
             && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid0))
           else AI.get_idx(qc, qid0) >= mx;
      if pc == pcb + 1 {
        // THE reset site: the instruction pins qid0 == qid.
        assert qid0 == qid as int;
        assert qid in PIV.QuantIds(re);
        // PathPresentQ base case at qid's own node.
      } else if pc == pcb || pc == pcb + 2 || pc == e1 || pc == e1 + 1 {
        assert false;                               // Fork/BeginLoop/EndLoop/Jmp
      } else {
        assert pcb + 3 <= pc < e1;
        var qv := AI.get_idx(qc, qid0);
        NestInvResetSite(r1, code, pcb + 3, e1, pc, cc, qc, qv, qid);
        assert (qid0 as nat) != qid by { assert (qid0 as nat) !in PIV.QuantIds(r1); }  // QuantUnique
        assert qv >= mx;
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && if pc == pcb then
             (AI.get_idx(cc, CP.start_reg(cid)) < mx || AI.get_idx(cc, CP.start_reg(cid)) < 0)
             && AllStaleRE(r1, cc, mx)
           else
             AI.get_idx(cc, CP.start_reg(cid)) >= mx
             && AI.get_idx(cc, CP.start_reg(cid)) >= 0
             && (pcb + 1 <= pc < e1 ==> NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      if pc == pcb || pc == e1 {
        assert false;                               // SetRegisterToCP ≠ SetQuantToClock
      } else {
        assert pcb + 1 <= pc < e1;
        NestInvResetSite(r1, code, pcb + 1, e1, pc, cc, qc, mx, qid);
        // ancestor clause of PathPresentQ: own start fresh.
      }
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
  }

  // ==========================================================================
  // L3a (E): PATH PRESENCE TO A LOOKAROUND NODE. The outer half of the (E)
  // path hypothesis `PIV.PathPresentLk(re, .., g)` for a group `g` INSIDE look
  // `lid`'s body: the descent from the root to the `Re_lookaround(lid, ..)`
  // node itself, carrying the same quant/ancestor-capture clock claims as
  // `PathPresentLk` but stopping AT the look node (whose own `lc[lid] >= mx`
  // clause is the consumer's, threaded via `MxAtLidLk`). Established at the
  // gate-crossing site from the thread's positional invariant (`NestInvLookSite`
  // — the `CheckOracle` analog of `NestInvResetSite`), composed with the
  // body-side `PIV.BodyPathPresentLk` by `LookPathCompose`.
  //
  // Look-BLIND by design (no `lc` argument): in the lookbehind fragment every
  // look body is `LookFreeRE`, so the path to a look node crosses no other
  // look node — the single `lc[lid]` clause is peeled off to the consumer.
  // ==========================================================================

  /** `LookFreeRE` has no lookaround ids. */
  lemma LookFreeNoLookIdsN(r: R.regex)
    requires NR.LookFreeRE(r)
    ensures LTB.LookIds(r) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookFreeNoLookIdsN(r1); LookFreeNoLookIdsN(r2);
    case Re_con(r1, r2) => LookFreeNoLookIdsN(r1); LookFreeNoLookIdsN(r2);
    case Re_quant(_, _, _, r1) => LookFreeNoLookIdsN(r1);
    case Re_capture(_, r1) => LookFreeNoLookIdsN(r1);
    case _ =>
  }

  /** The body of the `lid`-labelled lookaround node in `r`. */
  ghost function LookBodyOfRE(r: R.regex, lid: nat): R.regex
    requires lid in LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) then LookBodyOfRE(r1, lid) else LookBodyOfRE(r2, lid)
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) then LookBodyOfRE(r1, lid) else LookBodyOfRE(r2, lid)
    case Re_quant(_, _, _, r1) => LookBodyOfRE(r1, lid)
    case Re_capture(_, r1) => LookBodyOfRE(r1, lid)
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid then r1 else LookBodyOfRE(r1, lid)
  }

  /** The body's shape facts, from the fragment: look-free plus-fragment. */
  lemma LookBodyOfFragment(r: R.regex, lid: nat)
    requires NR.LookBehindFragmentRE(r)
    requires lid in LTB.LookIds(r)
    ensures NR.LookFreeRE(LookBodyOfRE(r, lid))
    ensures NR.PlusFragmentRE(LookBodyOfRE(r, lid))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyOfFragment(r1, lid); } else { LookBodyOfFragment(r2, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyOfFragment(r1, lid); } else { LookBodyOfFragment(r2, lid); }
    case Re_quant(_, _, _, r1) => LookBodyOfFragment(r1, lid);
    case Re_capture(_, r1) => LookBodyOfFragment(r1, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        // fragment: the body is look-free, so no foreign lid lives below it
        assert NR.LookFreeRE(r1);
        LookFreeNoLookIdsN(r1);
        assert false;
      }
  }

  /** (L4 NESTED) The body's shape facts under the POSITIVE-nesting sub-fragment:
      the body is itself in the nested fragment (looks may nest to any depth) and
      keeps the negative-look-free discipline. The depth-1 `LookBodyOfFragment`
      forces the body look-free; here the else-branch recurses because a nested
      body genuinely owns foreign lids. */
  lemma LookBodyOfFragmentNested(r: R.regex, lid: nat)
    requires NR.NestedFragmentRE(r) && NR.NegLooksLookFreeRE(r)
    requires lid in LTB.LookIds(r)
    ensures NR.NestedFragmentRE(LookBodyOfRE(r, lid))
    ensures NR.NegLooksLookFreeRE(LookBodyOfRE(r, lid))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyOfFragmentNested(r1, lid); } else { LookBodyOfFragmentNested(r2, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyOfFragmentNested(r1, lid); } else { LookBodyOfFragmentNested(r2, lid); }
    case Re_quant(_, _, _, r1) => LookBodyOfFragmentNested(r1, lid);
    case Re_capture(_, r1) => LookBodyOfFragmentNested(r1, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
        // body is r1; NestedFragmentRE(r1) & NegLooksLookFreeRE(r1) hold at the node
      } else {
        // a nested body genuinely owns foreign lids — recurse into r1
        LookBodyOfFragmentNested(r1, lid);
      }
  }

  /** The body's captures are inside-look captures of `r` (hence captures of `r`). */
  lemma LookBodyCapsIn(r: R.regex, lid: nat)
    requires lid in LTB.LookIds(r)
    ensures PIV.CapIds(LookBodyOfRE(r, lid)) <= PIV.CapIdsInLooks(r)
    ensures PIV.CapIds(LookBodyOfRE(r, lid)) <= PIV.CapIds(r)
    decreases r
  {
    PIV.CapIdsSplit(r);
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyCapsIn(r1, lid); } else { LookBodyCapsIn(r2, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyCapsIn(r1, lid); } else { LookBodyCapsIn(r2, lid); }
    case Re_quant(_, _, _, r1) => LookBodyCapsIn(r1, lid);
    case Re_capture(_, r1) => LookBodyCapsIn(r1, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        LookBodyCapsIn(r1, lid);
      }
  }

  /** A look body's own look ids are among `r`'s look ids — the `LookIds`
      analogue of `LookBodyCapsIn`. Pure structural induction (no fragment). */
  lemma LookBodyLookIdsIn(r: R.regex, lid: nat)
    requires lid in LTB.LookIds(r)
    ensures LTB.LookIds(LookBodyOfRE(r, lid)) <= LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyLookIdsIn(r1, lid); } else { LookBodyLookIdsIn(r2, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyLookIdsIn(r1, lid); } else { LookBodyLookIdsIn(r2, lid); }
    case Re_quant(_, _, _, r1) => LookBodyLookIdsIn(r1, lid);
    case Re_capture(_, r1) => LookBodyLookIdsIn(r1, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        LookBodyLookIdsIn(r1, lid);
      }
  }

  // ==========================================================================
  // (L4 NESTED) TOP-LEVEL looks: the look ids whose `CheckOracle` compiles into
  // the MAIN code (a lookaround body lives in a separate per-lookaround table,
  // NOT inline — see `NfaRepRE`'s `Re_lookaround` case, a single instruction).
  // `TopLookIds` does NOT descend into lookaround bodies, so it names exactly
  // those looks not nested inside any other look. The gate-site navigation
  // (`LookSiteTopNested`) lands only on these; `TopLookNotNested` turns
  // top-level-ness into the disjointness the capture-fold frame needs.
  // ==========================================================================

  /** The TOP-LEVEL look ids of `re`: like `LTB.LookIds` but STOPS at each
      lookaround node (does not recurse into the body). */
  ghost function TopLookIds(re: R.regex): set<nat>
    decreases re
  {
    match re
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => TopLookIds(r1) + TopLookIds(r2)
    case Re_con(r1, r2) => TopLookIds(r1) + TopLookIds(r2)
    case Re_quant(_, _, _, r1) => TopLookIds(r1)
    case Re_capture(_, r1) => TopLookIds(r1)
    case Re_lookaround(lid, _, _) => if lid >= 0 then {lid as nat} else {}
  }

  /** `TopLookIds ⊆ LookIds`. */
  lemma TopLookIdsIn(re: R.regex)
    ensures TopLookIds(re) <= LTB.LookIds(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => TopLookIdsIn(r1); TopLookIdsIn(r2);
    case Re_con(r1, r2) => TopLookIdsIn(r1); TopLookIdsIn(r2);
    case Re_quant(_, _, _, r1) => TopLookIdsIn(r1);
    case Re_capture(_, r1) => TopLookIdsIn(r1);
    case _ =>
  }

  /** THE TOP-LEVEL FRAME: a top-level look `lid0` sits inside NO look body.
      Under `LookUnique`, `lid0`'s single occurrence is at re's top structure
      (`TopLookIds`), so it cannot also occur below any lookaround node. */
  lemma TopLookNotNested(r: R.regex, lid0: nat, lid: nat)
    requires LTB.LookUnique(r)
    requires lid0 in TopLookIds(r)
    requires lid in LTB.LookIds(r)
    ensures lid0 !in LTB.LookIds(LookBodyOfRE(r, lid))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        assert LookBodyOfRE(r, lid) == LookBodyOfRE(r1, lid);
        if lid0 in TopLookIds(r1) {
          TopLookNotNested(r1, lid0, lid);
        } else {
          // lid0 in TopLookIds(r2) ⊆ LookIds(r2); disjoint from r1's looks,
          // and lid's body sits under r1.
          assert lid0 in TopLookIds(r2);
          TopLookIdsIn(r2);
          LookBodyLookIdsIn(r1, lid);
        }
      } else {
        assert lid in LTB.LookIds(r2);
        assert LookBodyOfRE(r, lid) == LookBodyOfRE(r2, lid);
        if lid0 in TopLookIds(r2) {
          TopLookNotNested(r2, lid0, lid);
        } else {
          assert lid0 in TopLookIds(r1);
          TopLookIdsIn(r1);
          LookBodyLookIdsIn(r2, lid);
        }
      }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        assert LookBodyOfRE(r, lid) == LookBodyOfRE(r1, lid);
        if lid0 in TopLookIds(r1) {
          TopLookNotNested(r1, lid0, lid);
        } else {
          assert lid0 in TopLookIds(r2);
          TopLookIdsIn(r2);
          LookBodyLookIdsIn(r1, lid);
        }
      } else {
        assert lid in LTB.LookIds(r2);
        assert LookBodyOfRE(r, lid) == LookBodyOfRE(r2, lid);
        if lid0 in TopLookIds(r2) {
          TopLookNotNested(r2, lid0, lid);
        } else {
          assert lid0 in TopLookIds(r1);
          TopLookIdsIn(r1);
          LookBodyLookIdsIn(r2, lid);
        }
      }
    case Re_quant(_, _, _, r1) =>
      assert LookBodyOfRE(r, lid) == LookBodyOfRE(r1, lid);
      TopLookNotNested(r1, lid0, lid);
    case Re_capture(_, r1) =>
      assert LookBodyOfRE(r, lid) == LookBodyOfRE(r1, lid);
      TopLookNotNested(r1, lid0, lid);
    case Re_lookaround(lidn, _, r1) =>
      // lid0 == lidn (the only top-level id here). LookUnique ⟹ lidn !in
      // LookIds(r1), so lidn sits in no body under this node.
      assert lidn >= 0 && (lidn as nat) == lid0;
      assert (lidn as nat) !in LTB.LookIds(r1);
      if lidn >= 0 && (lidn as nat) == lid {
        assert LookBodyOfRE(r, lid) == r1;
      } else {
        assert lid in LTB.LookIds(r1);
        assert LookBodyOfRE(r, lid) == LookBodyOfRE(r1, lid);
        LookBodyLookIdsIn(r1, lid);   // LookIds(body) ⊆ LookIds(r1), which lacks lidn
      }
  }

  /** Path presence TO the `lid` node: every quantifier on the descent has its
      stamp in scope and every ancestor capture's start clock is fresh and in
      scope — `PIV.PathPresentLk`'s outer clauses, stopped AT the look node
      (its own `lc` clause is the consumer's, thresholded by `MxAtLidLk`). */
  ghost predicate LookPathPresent(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, lid: nat)
    requires lid in LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) then LookPathPresent(r1, cc, qc, mx, lid)
      else LookPathPresent(r2, cc, qc, mx, lid)
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) then LookPathPresent(r1, cc, qc, mx, lid)
      else LookPathPresent(r2, cc, qc, mx, lid)
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      qv >= mx && LookPathPresent(r1, cc, qc, qv, lid)
    case Re_capture(cid, r1) =>
      AI.get_idx(cc, CP.start_reg(cid)) >= 0 && AI.get_idx(cc, CP.start_reg(cid)) >= mx
      && LookPathPresent(r1, cc, qc, mx, lid)
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid then true
      else LookPathPresent(r1, cc, qc, -1, lid)
  }

  /** The `mx` threshold in force AT the `lid` node (the `MxAtGidLk` analog). */
  ghost function MxAtLidLk(r: R.regex, qc: seq<int>, mx: int, lid: nat): int
    requires lid in LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) then MxAtLidLk(r1, qc, mx, lid) else MxAtLidLk(r2, qc, mx, lid)
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) then MxAtLidLk(r1, qc, mx, lid) else MxAtLidLk(r2, qc, mx, lid)
    case Re_quant(_, qid, _, r1) => MxAtLidLk(r1, qc, AI.get_idx(qc, qid), lid)
    case Re_capture(_, r1) => MxAtLidLk(r1, qc, mx, lid)
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid then mx else MxAtLidLk(r1, qc, -1, lid)
  }

  /** `MxAtLidLk` thresholds are the `mx` parameter or a stored quant clock, so
      the clock backbone bounds them (the `MxAtGidLE` analog). */
  lemma MxAtLidLE(r: R.regex, qc: seq<int>, mx: int, lid: nat, S: int)
    requires lid in LTB.LookIds(r)
    requires -1 <= S && mx <= S
    requires forall k :: AI.get_idx(qc, k) <= S
    ensures MxAtLidLk(r, qc, mx, lid) <= S
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { MxAtLidLE(r1, qc, mx, lid, S); } else { MxAtLidLE(r2, qc, mx, lid, S); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { MxAtLidLE(r1, qc, mx, lid, S); } else { MxAtLidLE(r2, qc, mx, lid, S); }
    case Re_quant(_, qid, _, r1) => MxAtLidLE(r1, qc, AI.get_idx(qc, qid), lid, S);
    case Re_capture(_, r1) => MxAtLidLE(r1, qc, mx, lid, S);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {} else { MxAtLidLE(r1, qc, -1, lid, S); }
  }

  /** THE COMPOSE STEP: outer path presence to the look node + the look's own
      clock clause + body-side path presence assemble into the full
      `PIV.PathPresentLk(r, .., g)`, and the `mx` reaching `g` is the body's
      own (`-1`-rooted) threshold — the look node resets `mx`, so the outer
      prefix is invisible to `MxAtGidLk`. */
  lemma LookPathCompose(r: R.regex, body: R.regex, cc: seq<int>, lc: seq<int>, qc: seq<int>,
                        mx: int, lid: nat, g: nat)
    requires NR.LookBehindFragmentRE(r) && PIV.CapUnique(r)
    requires lid in LTB.LookIds(r)
    requires body == LookBodyOfRE(r, lid)
    requires g in PIV.CapIds(body)
    requires LookPathPresent(r, cc, qc, mx, lid)
    requires AI.get_idx(lc, lid as int) >= 0
    requires AI.get_idx(lc, lid as int) >= MxAtLidLk(r, qc, mx, lid)
    requires PIV.PathPresentLk(body, cc, lc, qc, -1, g)
    ensures g in PIV.CapIds(r)
    ensures PIV.PathPresentLk(r, cc, lc, qc, mx, g)
    ensures PIV.MxAtGidLk(r, cc, lc, qc, mx, g) == PIV.MxAtGidLk(body, cc, lc, qc, -1, g)
    decreases r
  {
    LookBodyCapsIn(r, lid);
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        LookBodyCapsIn(r1, lid);
        assert g in PIV.CapIds(r1);
        LookPathCompose(r1, body, cc, lc, qc, mx, lid, g);
      } else {
        LookBodyCapsIn(r2, lid);
        assert g in PIV.CapIds(r2);
        assert g !in PIV.CapIds(r1) by {
          if g in PIV.CapIds(r1) { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
        LookPathCompose(r2, body, cc, lc, qc, mx, lid, g);
      }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        LookBodyCapsIn(r1, lid);
        assert g in PIV.CapIds(r1);
        LookPathCompose(r1, body, cc, lc, qc, mx, lid, g);
      } else {
        LookBodyCapsIn(r2, lid);
        assert g in PIV.CapIds(r2);
        assert g !in PIV.CapIds(r1) by {
          if g in PIV.CapIds(r1) { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
        LookPathCompose(r2, body, cc, lc, qc, mx, lid, g);
      }
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      assert qv >= mx;                               // LookPathPresent
      LookPathCompose(r1, body, cc, lc, qc, qv, lid, g);
    case Re_capture(cid, r1) =>
      LookBodyCapsIn(r1, lid);
      assert g in PIV.CapIds(r1);
      assert cid >= 0 && (cid as nat) !in PIV.CapIds(r1);   // CapUnique
      assert (cid as nat) != g;
      assert AI.get_idx(cc, CP.start_reg(cid)) >= 0
          && AI.get_idx(cc, CP.start_reg(cid)) >= mx;       // LookPathPresent
      LookPathCompose(r1, body, cc, lc, qc, mx, lid, g);
    case Re_lookaround(lid0, la, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
        assert body == r1;
        assert MxAtLidLk(r, qc, mx, lid) == mx;
        assert AI.get_idx(lc, lid0) >= 0 && AI.get_idx(lc, lid0) >= mx;
      } else {
        // fragment: bodies are look-free, so no foreign look sits on the path
        assert NR.LookFreeRE(r1);
        LookFreeNoLookIdsN(r1);
        assert lid in LTB.LookIds(r1);
        assert false;
      }
  }

  /** THE DECOMPOSE STEP (inverse of `LookPathCompose`): full path presence at
      an inside-look `g` peels into the outer path presence TO the owner node,
      the look's own clock clause, and the body-side presence — and the `mx`
      reaching `g` is the body's own (the look node resets it). */
  lemma LookPathDecompose(r: R.regex, body: R.regex, cc: seq<int>, lc: seq<int>, qc: seq<int>,
                          mx: int, lid: nat, g: nat)
    requires NR.LookBehindFragmentRE(r) && PIV.CapUnique(r)
    requires lid in LTB.LookIds(r)
    requires body == LookBodyOfRE(r, lid)
    requires g in PIV.CapIds(body)
    requires g in PIV.CapIds(r)
    requires PIV.PathPresentLk(r, cc, lc, qc, mx, g)
    ensures LookPathPresent(r, cc, qc, mx, lid)
    ensures AI.get_idx(lc, lid as int) >= 0
    ensures AI.get_idx(lc, lid as int) >= MxAtLidLk(r, qc, mx, lid)
    ensures PIV.PathPresentLk(body, cc, lc, qc, -1, g)
    ensures PIV.MxAtGidLk(r, cc, lc, qc, mx, g) == PIV.MxAtGidLk(body, cc, lc, qc, -1, g)
    decreases r
  {
    LookBodyCapsIn(r, lid);
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        LookBodyCapsIn(r1, lid);
        assert g in PIV.CapIds(r1);
        LookPathDecompose(r1, body, cc, lc, qc, mx, lid, g);
      } else {
        LookBodyCapsIn(r2, lid);
        assert g in PIV.CapIds(r2);
        assert g !in PIV.CapIds(r1) by {
          if g in PIV.CapIds(r1) { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
        LookPathDecompose(r2, body, cc, lc, qc, mx, lid, g);
      }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        LookBodyCapsIn(r1, lid);
        assert g in PIV.CapIds(r1);
        LookPathDecompose(r1, body, cc, lc, qc, mx, lid, g);
      } else {
        LookBodyCapsIn(r2, lid);
        assert g in PIV.CapIds(r2);
        assert g !in PIV.CapIds(r1) by {
          if g in PIV.CapIds(r1) { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
        LookPathDecompose(r2, body, cc, lc, qc, mx, lid, g);
      }
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      assert qv >= mx;                               // PathPresentLk
      LookPathDecompose(r1, body, cc, lc, qc, qv, lid, g);
    case Re_capture(cid, r1) =>
      LookBodyCapsIn(r1, lid);
      assert g in PIV.CapIds(r1);
      assert cid >= 0 && (cid as nat) !in PIV.CapIds(r1);   // CapUnique
      assert (cid as nat) != g;
      LookPathDecompose(r1, body, cc, lc, qc, mx, lid, g);
    case Re_lookaround(lid0, la, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
        assert body == r1;
        assert MxAtLidLk(r, qc, mx, lid) == mx;
        // PathPresentLk's look clause supplies the lc facts and the body walk
      } else {
        assert NR.LookFreeRE(r1);
        LookFreeNoLookIdsN(r1);
        assert lid in LTB.LookIds(r1);
        assert false;
      }
  }

  /** `PathPresentLk`/`MxAtGidLk` read the register banks only at `r`'s own
      capture-start slots, quant slots and look slots — congruence under
      agreement there (the body-side transport: the reconstructed bank agrees
      with the fresh replay's on `CaptureRegs(body)`). */
  lemma PathPresentLkAgree(r: R.regex, cc1: seq<int>, lc1: seq<int>, qc1: seq<int>,
                           cc2: seq<int>, lc2: seq<int>, qc2: seq<int>, mx: int, g: nat)
    requires g in PIV.CapIds(r)
    requires forall c: nat :: c in PIV.CapIds(r) ==>
      AI.get_idx(cc1, CP.start_reg(c as int)) == AI.get_idx(cc2, CP.start_reg(c as int))
    requires forall q: nat :: q in PIV.QuantIds(r) ==>
      AI.get_idx(qc1, q as int) == AI.get_idx(qc2, q as int)
    requires forall l: nat :: l in LTB.LookIds(r) ==>
      AI.get_idx(lc1, l as int) == AI.get_idx(lc2, l as int)
    ensures PIV.PathPresentLk(r, cc1, lc1, qc1, mx, g) == PIV.PathPresentLk(r, cc2, lc2, qc2, mx, g)
    ensures PIV.MxAtGidLk(r, cc1, lc1, qc1, mx, g) == PIV.MxAtGidLk(r, cc2, lc2, qc2, mx, g)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      assert PIV.CapIds(r1) <= PIV.CapIds(r) && PIV.CapIds(r2) <= PIV.CapIds(r);
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r) && PIV.QuantIds(r2) <= PIV.QuantIds(r);
      assert LTB.LookIds(r1) <= LTB.LookIds(r) && LTB.LookIds(r2) <= LTB.LookIds(r);
      if g in PIV.CapIds(r1) { PathPresentLkAgree(r1, cc1, lc1, qc1, cc2, lc2, qc2, mx, g); }
      else { PathPresentLkAgree(r2, cc1, lc1, qc1, cc2, lc2, qc2, mx, g); }
    case Re_con(r1, r2) =>
      assert PIV.CapIds(r1) <= PIV.CapIds(r) && PIV.CapIds(r2) <= PIV.CapIds(r);
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r) && PIV.QuantIds(r2) <= PIV.QuantIds(r);
      assert LTB.LookIds(r1) <= LTB.LookIds(r) && LTB.LookIds(r2) <= LTB.LookIds(r);
      if g in PIV.CapIds(r1) { PathPresentLkAgree(r1, cc1, lc1, qc1, cc2, lc2, qc2, mx, g); }
      else { PathPresentLkAgree(r2, cc1, lc1, qc1, cc2, lc2, qc2, mx, g); }
    case Re_quant(_, qid, _, r1) =>
      assert PIV.CapIds(r1) <= PIV.CapIds(r);
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r);
      assert LTB.LookIds(r1) <= LTB.LookIds(r);
      assert AI.get_idx(qc1, qid) == AI.get_idx(qc2, qid) by {
        if qid >= 0 { assert (qid as nat) in PIV.QuantIds(r); }
      }
      PathPresentLkAgree(r1, cc1, lc1, qc1, cc2, lc2, qc2, AI.get_idx(qc1, qid), g);
    case Re_capture(cid, r1) =>
      assert PIV.CapIds(r1) <= PIV.CapIds(r);
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r);
      assert LTB.LookIds(r1) <= LTB.LookIds(r);
      assert AI.get_idx(cc1, CP.start_reg(cid)) == AI.get_idx(cc2, CP.start_reg(cid)) by {
        if cid >= 0 { assert (cid as nat) in PIV.CapIds(r); }
        else { assert CP.start_reg(cid) < 0; }
      }
      if cid >= 0 && (cid as nat) == g {
      } else {
        assert g in PIV.CapIds(r1);
        PathPresentLkAgree(r1, cc1, lc1, qc1, cc2, lc2, qc2, mx, g);
      }
    case Re_lookaround(lid0, _, r1) =>
      assert PIV.CapIds(r1) <= PIV.CapIds(r);
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r);
      assert LTB.LookIds(r1) <= LTB.LookIds(r);
      assert AI.get_idx(lc1, lid0) == AI.get_idx(lc2, lid0) by {
        if lid0 >= 0 { assert (lid0 as nat) in LTB.LookIds(r); }
      }
      PathPresentLkAgree(r1, cc1, lc1, qc1, cc2, lc2, qc2, -1, g);
  }

  /** `LookPathPresent`/`MxAtLidLk` read the banks only at OUTSIDE-look slots
      (fragment: the path to a look node crosses no look body) — congruence
      under outside-look agreement (the outer transport: the reconstructed
      bank agrees with the winning thread's outside the look registers). */
  lemma LookPathPresentAgree(r: R.regex, cc1: seq<int>, qc1: seq<int>,
                             cc2: seq<int>, qc2: seq<int>, mx: int, lid: nat)
    requires NR.LookBehindFragmentRE(r)
    requires lid in LTB.LookIds(r)
    requires forall c: nat :: c in PIV.CapIdsOutsideLooks(r) ==>
      AI.get_idx(cc1, CP.start_reg(c as int)) == AI.get_idx(cc2, CP.start_reg(c as int))
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(r) ==>
      AI.get_idx(qc1, q as int) == AI.get_idx(qc2, q as int)
    ensures LookPathPresent(r, cc1, qc1, mx, lid) == LookPathPresent(r, cc2, qc2, mx, lid)
    ensures MxAtLidLk(r, qc1, mx, lid) == MxAtLidLk(r, qc2, mx, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      assert PIV.CapIdsOutsideLooks(r1) <= PIV.CapIdsOutsideLooks(r)
          && PIV.CapIdsOutsideLooks(r2) <= PIV.CapIdsOutsideLooks(r);
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r)
          && PIV.QuantIdsOutsideLooks(r2) <= PIV.QuantIdsOutsideLooks(r);
      if lid in LTB.LookIds(r1) { LookPathPresentAgree(r1, cc1, qc1, cc2, qc2, mx, lid); }
      else { LookPathPresentAgree(r2, cc1, qc1, cc2, qc2, mx, lid); }
    case Re_con(r1, r2) =>
      assert PIV.CapIdsOutsideLooks(r1) <= PIV.CapIdsOutsideLooks(r)
          && PIV.CapIdsOutsideLooks(r2) <= PIV.CapIdsOutsideLooks(r);
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r)
          && PIV.QuantIdsOutsideLooks(r2) <= PIV.QuantIdsOutsideLooks(r);
      if lid in LTB.LookIds(r1) { LookPathPresentAgree(r1, cc1, qc1, cc2, qc2, mx, lid); }
      else { LookPathPresentAgree(r2, cc1, qc1, cc2, qc2, mx, lid); }
    case Re_quant(_, qid, _, r1) =>
      assert PIV.CapIdsOutsideLooks(r1) <= PIV.CapIdsOutsideLooks(r);
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r);
      assert AI.get_idx(qc1, qid) == AI.get_idx(qc2, qid) by {
        if qid >= 0 { assert (qid as nat) in PIV.QuantIdsOutsideLooks(r); }
      }
      LookPathPresentAgree(r1, cc1, qc1, cc2, qc2, AI.get_idx(qc1, qid), lid);
    case Re_capture(cid, r1) =>
      assert PIV.CapIdsOutsideLooks(r1) <= PIV.CapIdsOutsideLooks(r);
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r);
      assert AI.get_idx(cc1, CP.start_reg(cid)) == AI.get_idx(cc2, CP.start_reg(cid)) by {
        if cid >= 0 { assert (cid as nat) in PIV.CapIdsOutsideLooks(r); }
        else { assert CP.start_reg(cid) < 0; }
      }
      LookPathPresentAgree(r1, cc1, qc1, cc2, qc2, mx, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        assert NR.LookFreeRE(r1);
        LookFreeNoLookIdsN(r1);
        assert lid in LTB.LookIds(r1);
        assert false;
      }
  }

  // --------------------------------------------------------------------------
  // The gate-site extraction: at a pc holding look `lid`'s `CheckOracle`, the
  // thread's nesting claims assemble into `LookPathPresent` — the `CheckOracle`
  // analog of `NestInvResetSite`, same chain-companion structure.
  // --------------------------------------------------------------------------

  /** `NestInvLookSite` for forced-copy chains. */
  lemma NestInvLookSiteMin(k: nat, qn: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                           cc: seq<int>, qc: seq<int>, mx: int, lid: int)
    requires NR.NfaRepMinRE(k, qn, r1, code, pcb, pce)
    requires NR.LookBehindFragmentRE(r1) && LTB.LookUnique(r1)
    requires pcb <= pc < pce
    requires NestInvMinRE(k, qn, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    ensures lid >= 0 && (lid as nat) in LTB.LookIds(r1)
    ensures AI.get_idx(qc, qn) >= mx
    ensures LookPathPresent(r1, cc, qc, AI.get_idx(qc, qn), lid as nat)
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qn, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qn, r1, code, e1, pce)
      && (if pc == pcb then true
          else if pcb + 1 <= pc < e1 then
            AI.get_idx(qc, qn) >= mx
            && NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, AI.get_idx(qc, qn))
          else NestInvMinRE(k - 1, qn, r1, code, e1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    if pc == pcb {
      assert false;                                 // SetQuantToClock ≠ CheckOracle
    } else if pcb + 1 <= pc < e1 {
      var qv := AI.get_idx(qc, qn);
      NestInvLookSite(r1, code, pcb + 1, e1, pc, cc, qc, qv, lid);
    } else {
      NestInvLookSiteMin(k - 1, qn, r1, code, e1, pce, pc, cc, qc, mx, lid);
    }
  }

  /** `NestInvLookSite` for optional-layer chains. */
  lemma NestInvLookSiteOpt(k: nat, greedy: bool, qn: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                           cc: seq<int>, qc: seq<int>, mx: int, lid: int)
    requires NR.NfaRepOptRE(k, greedy, qn, r1, code, pcb, pce)
    requires NR.LookBehindFragmentRE(r1) && LTB.LookUnique(r1)
    requires pcb <= pc < pce
    requires NestInvOptRE(k, greedy, qn, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    ensures lid >= 0 && (lid as nat) in LTB.LookIds(r1)
    ensures AI.get_idx(qc, qn) >= mx
    ensures LookPathPresent(r1, cc, qc, AI.get_idx(qc, qn), lid as nat)
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
            AI.get_idx(qc, qn) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qn))
          else if pcb + 3 <= pc < e1 then
            AI.get_idx(qc, qn) >= mx
            && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qn))
          else if pc == e1 then AI.get_idx(qc, qn) >= mx
          else NestInvOptRE(k - 1, greedy, qn, r1, code, e1 + 1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 {
      assert false;                                 // Fork/SetQuantToClock/BeginLoop/EndLoop
    } else if pcb + 3 <= pc < e1 {
      var qv := AI.get_idx(qc, qn);
      NestInvLookSite(r1, code, pcb + 3, e1, pc, cc, qc, qv, lid);
    } else {
      NestInvLookSiteOpt(k - 1, greedy, qn, r1, code, e1 + 1, pce, pc, cc, qc, mx, lid);
    }
  }

  // ==========================================================================
  // (L4 NESTED) The gate-site extraction chain, generalized from the depth-1
  // `LookBehindFragmentRE` to the full `NestedFragmentRE`. The bodies are
  // VERBATIM copies of `NestInvLookSite{,Min,Opt}`: those lemmas never consume
  // look-freeness of a lookaround body — a lookaround compiles to a SINGLE
  // `CheckOracle`/`NegCheckOracle` in the MAIN code (its body lives in a
  // separate per-lookaround table, NOT inline), so the main-code navigation
  // reaches only TOP-LEVEL looks and the `Re_lookaround` case just asserts
  // `pc == pcb` and pins `lid == lid0`. The fragment hypothesis flows purely to
  // feed the recursion; swapping it for `NestedFragmentRE` (which decomposes
  // identically on alt/con/quant/capture and only relaxes the lookaround leaf)
  // leaves every proof step intact.
  // ==========================================================================

  /** (L4 NESTED) `NestInvLookSiteMin` under `NestedFragmentRE`. */
  lemma NestInvLookSiteMinNested(k: nat, qn: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                                 cc: seq<int>, qc: seq<int>, mx: int, lid: int)
    requires NR.NfaRepMinRE(k, qn, r1, code, pcb, pce)
    requires NR.NestedFragmentRE(r1) && LTB.LookUnique(r1)
    requires pcb <= pc < pce
    requires NestInvMinRE(k, qn, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    ensures lid >= 0 && (lid as nat) in LTB.LookIds(r1)
    ensures AI.get_idx(qc, qn) >= mx
    ensures LookPathPresent(r1, cc, qc, AI.get_idx(qc, qn), lid as nat)
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qn, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qn, r1, code, e1, pce)
      && (if pc == pcb then true
          else if pcb + 1 <= pc < e1 then
            AI.get_idx(qc, qn) >= mx
            && NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, AI.get_idx(qc, qn))
          else NestInvMinRE(k - 1, qn, r1, code, e1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    if pc == pcb {
      assert false;                                 // SetQuantToClock ≠ CheckOracle
    } else if pcb + 1 <= pc < e1 {
      var qv := AI.get_idx(qc, qn);
      NestInvLookSiteNested(r1, code, pcb + 1, e1, pc, cc, qc, qv, lid);
    } else {
      NestInvLookSiteMinNested(k - 1, qn, r1, code, e1, pce, pc, cc, qc, mx, lid);
    }
  }

  /** (L4 NESTED) `NestInvLookSiteOpt` under `NestedFragmentRE`. */
  lemma NestInvLookSiteOptNested(k: nat, greedy: bool, qn: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                                 cc: seq<int>, qc: seq<int>, mx: int, lid: int)
    requires NR.NfaRepOptRE(k, greedy, qn, r1, code, pcb, pce)
    requires NR.NestedFragmentRE(r1) && LTB.LookUnique(r1)
    requires pcb <= pc < pce
    requires NestInvOptRE(k, greedy, qn, r1, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    ensures lid >= 0 && (lid as nat) in LTB.LookIds(r1)
    ensures AI.get_idx(qc, qn) >= mx
    ensures LookPathPresent(r1, cc, qc, AI.get_idx(qc, qn), lid as nat)
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
            AI.get_idx(qc, qn) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qn))
          else if pcb + 3 <= pc < e1 then
            AI.get_idx(qc, qn) >= mx
            && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qn))
          else if pc == e1 then AI.get_idx(qc, qn) >= mx
          else NestInvOptRE(k - 1, greedy, qn, r1, code, e1 + 1, pce, pc, cc, qc, mx));
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 {
      assert false;                                 // Fork/SetQuantToClock/BeginLoop/EndLoop
    } else if pcb + 3 <= pc < e1 {
      var qv := AI.get_idx(qc, qn);
      NestInvLookSiteNested(r1, code, pcb + 3, e1, pc, cc, qc, qv, lid);
    } else {
      NestInvLookSiteOptNested(k - 1, greedy, qn, r1, code, e1 + 1, pce, pc, cc, qc, mx, lid);
    }
  }

  /** (L4 NESTED) `NestInvLookSite` under `NestedFragmentRE`. */
  lemma NestInvLookSiteNested(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                              cc: seq<int>, qc: seq<int>, mx: int, lid: int)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires NR.NestedFragmentRE(re) && LTB.LookUnique(re)
    requires pcb <= pc < pce
    requires NestInvRE(re, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    ensures lid >= 0 && (lid as nat) in LTB.LookIds(re)
    ensures LookPathPresent(re, cc, qc, mx, lid as nat)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
      assert pc == pcb;
      assert false;
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && if pc == pcb then AllStaleRE(r1, cc, mx) && AllStaleRE(r2, cc, mx)
           else if pcb + 1 <= pc < e1 then
             NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else if pc == e1 then true
           else NestInvRE(r2, code, e1 + 1, pce, pc, cc, qc, mx);
      if pc == pcb {
        assert false;
      } else if pcb + 1 <= pc < e1 {
        NestInvLookSiteNested(r1, code, pcb + 1, e1, pc, cc, qc, mx, lid);
      } else if pc == e1 {
        assert false;
      } else {
        NestInvLookSiteNested(r2, code, e1 + 1, pce, pc, cc, qc, mx, lid);
        assert (lid as nat) !in LTB.LookIds(r1) by {
          if (lid as nat) in LTB.LookIds(r1) {
            assert (lid as nat) in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && if pc < e1 then NestInvRE(r1, code, pcb, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else NestInvRE(r2, code, e1, pce, pc, cc, qc, mx);
      if pc < e1 {
        NestInvLookSiteNested(r1, code, pcb, e1, pc, cc, qc, mx, lid);
      } else {
        NestInvLookSiteNested(r2, code, e1, pce, pc, cc, qc, mx, lid);
        assert (lid as nat) !in LTB.LookIds(r1) by {
          if (lid as nat) in LTB.LookIds(r1) {
            assert (lid as nat) in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
      }
    case Re_quant(nul, qid0, q, r1) =>
      if q.max.Some? {
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid0, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid0, r1, code, em, pce)
          && (if pc < em then NestInvMinRE(mn, qid0, r1, code, pcb, em, pc, cc, qc, mx)
              else NestInvOptRE(kx, q.greedy, qid0, r1, code, em, pce, pc, cc, qc, mx));
        NR.NfaRepIncrMinRE(mn, qid0, r1, code, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid0, r1, code, em, pce);
        if pc < em {
          NestInvLookSiteMinNested(mn, qid0, r1, code, pcb, em, pc, cc, qc, mx, lid);
        } else {
          NestInvLookSiteOptNested(kx, q.greedy, qid0, r1, code, em, pce, pc, cc, qc, mx, lid);
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
          && (if pc < em then NestInvMinRE(mn1, qid0, r1, code, pcb, em, pc, cc, qc, mx)
              else if pc == em then true
              else if em + 1 <= pc < e1 then
                AI.get_idx(qc, qid0) >= mx
                && NestInvRE(r1, code, em + 1, e1, pc, cc, qc, AI.get_idx(qc, qid0))
              else AI.get_idx(qc, qid0) >= mx);
        NR.NfaRepIncrMinRE(mn1, qid0, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          NestInvLookSiteMinNested(mn1, qid0, r1, code, pcb, em, pc, cc, qc, mx, lid);
        } else if pc == em {
          assert false;                             // SetQuantToClock ≠ CheckOracle
        } else if em + 1 <= pc < e1 {
          var qv := AI.get_idx(qc, qid0);
          NestInvLookSiteNested(r1, code, em + 1, e1, pc, cc, qc, qv, lid);
        } else {
          assert pc == e1;
          assert false;                             // Fork ≠ CheckOracle
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
             AI.get_idx(qc, qid0) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qid0))
           else if pcb + 3 <= pc < e1 then
             AI.get_idx(qc, qid0) >= mx
             && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid0))
           else AI.get_idx(qc, qid0) >= mx;
      if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 || pc == e1 + 1 {
        assert false;                               // Fork/SetQuantToClock/BeginLoop/EndLoop/Jmp
      } else {
        assert pcb + 3 <= pc < e1;
        var qv := AI.get_idx(qc, qid0);
        NestInvLookSiteNested(r1, code, pcb + 3, e1, pc, cc, qc, qv, lid);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && if pc == pcb then
             (AI.get_idx(cc, CP.start_reg(cid)) < mx || AI.get_idx(cc, CP.start_reg(cid)) < 0)
             && AllStaleRE(r1, cc, mx)
           else
             AI.get_idx(cc, CP.start_reg(cid)) >= mx
             && AI.get_idx(cc, CP.start_reg(cid)) >= 0
             && (pcb + 1 <= pc < e1 ==> NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      if pc == pcb || pc == e1 {
        assert false;                               // SetRegisterToCP ≠ CheckOracle
      } else {
        assert pcb + 1 <= pc < e1;
        NestInvLookSiteNested(r1, code, pcb + 1, e1, pc, cc, qc, mx, lid);
      }
    case Re_lookaround(lid0, la, r1) =>
      // the whole block is the single gate instruction; a positive flavour
      // compiles to CheckOracle(lid0), pinning lid == lid0.
      assert pc == pcb;
      assert la.Lookahead? || la.Lookbehind?;       // NegCheckOracle otherwise
      assert lid == lid0;
      assert lid0 >= 0;                             // LookUnique
      assert (lid as nat) in LTB.LookIds(re);
    case Re_anchor(_) =>
      assert pc == pcb;
      assert false;
  }

  /** THE GATE-SITE EXTRACTION: at a `pc` holding look `lid`'s `CheckOracle`,
      `NestInvRE`'s path claims assemble into `LookPathPresent(re, cc, qc, mx,
      lid)` — every enclosing quantifier's stamp is in scope and every ancestor
      capture's start clock is fresh. The look's own `lc[lid]` clause is the
      consumer's: at the crossing the stamp is BRAND NEW, so it beats
      `MxAtLidLk` via `MxAtLidLE` and the clock backbone. */
  lemma NestInvLookSite(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                        cc: seq<int>, qc: seq<int>, mx: int, lid: int)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires NR.LookBehindFragmentRE(re) && LTB.LookUnique(re)
    requires pcb <= pc < pce
    requires NestInvRE(re, code, pcb, pce, pc, cc, qc, mx)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    ensures lid >= 0 && (lid as nat) in LTB.LookIds(re)
    ensures LookPathPresent(re, cc, qc, mx, lid as nat)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
      assert pc == pcb;
      assert false;
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce)
        && if pc == pcb then AllStaleRE(r1, cc, mx) && AllStaleRE(r2, cc, mx)
           else if pcb + 1 <= pc < e1 then
             NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else if pc == e1 then true
           else NestInvRE(r2, code, e1 + 1, pce, pc, cc, qc, mx);
      if pc == pcb {
        assert false;
      } else if pcb + 1 <= pc < e1 {
        NestInvLookSite(r1, code, pcb + 1, e1, pc, cc, qc, mx, lid);
      } else if pc == e1 {
        assert false;
      } else {
        NestInvLookSite(r2, code, e1 + 1, pce, pc, cc, qc, mx, lid);
        assert (lid as nat) !in LTB.LookIds(r1) by {
          if (lid as nat) in LTB.LookIds(r1) {
            assert (lid as nat) in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && if pc < e1 then NestInvRE(r1, code, pcb, e1, pc, cc, qc, mx) && AllStaleRE(r2, cc, mx)
           else NestInvRE(r2, code, e1, pce, pc, cc, qc, mx);
      if pc < e1 {
        NestInvLookSite(r1, code, pcb, e1, pc, cc, qc, mx, lid);
      } else {
        NestInvLookSite(r2, code, e1, pce, pc, cc, qc, mx, lid);
        assert (lid as nat) !in LTB.LookIds(r1) by {
          if (lid as nat) in LTB.LookIds(r1) {
            assert (lid as nat) in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
      }
    case Re_quant(nul, qid0, q, r1) =>
      if q.max.Some? {
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var em: nat :| NR.NfaRepMinRE(mn, qid0, r1, code, pcb, em)
          && NR.NfaRepOptRE(kx, q.greedy, qid0, r1, code, em, pce)
          && (if pc < em then NestInvMinRE(mn, qid0, r1, code, pcb, em, pc, cc, qc, mx)
              else NestInvOptRE(kx, q.greedy, qid0, r1, code, em, pce, pc, cc, qc, mx));
        NR.NfaRepIncrMinRE(mn, qid0, r1, code, pcb, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid0, r1, code, em, pce);
        if pc < em {
          NestInvLookSiteMin(mn, qid0, r1, code, pcb, em, pc, cc, qc, mx, lid);
        } else {
          NestInvLookSiteOpt(kx, q.greedy, qid0, r1, code, em, pce, pc, cc, qc, mx, lid);
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
          && (if pc < em then NestInvMinRE(mn1, qid0, r1, code, pcb, em, pc, cc, qc, mx)
              else if pc == em then true
              else if em + 1 <= pc < e1 then
                AI.get_idx(qc, qid0) >= mx
                && NestInvRE(r1, code, em + 1, e1, pc, cc, qc, AI.get_idx(qc, qid0))
              else AI.get_idx(qc, qid0) >= mx);
        NR.NfaRepIncrMinRE(mn1, qid0, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          NestInvLookSiteMin(mn1, qid0, r1, code, pcb, em, pc, cc, qc, mx, lid);
        } else if pc == em {
          assert false;                             // SetQuantToClock ≠ CheckOracle
        } else if em + 1 <= pc < e1 {
          var qv := AI.get_idx(qc, qid0);
          NestInvLookSite(r1, code, em + 1, e1, pc, cc, qc, qv, lid);
        } else {
          assert pc == e1;
          assert false;                             // Fork ≠ CheckOracle
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
             AI.get_idx(qc, qid0) >= mx && AllStaleRE(r1, cc, AI.get_idx(qc, qid0))
           else if pcb + 3 <= pc < e1 then
             AI.get_idx(qc, qid0) >= mx
             && NestInvRE(r1, code, pcb + 3, e1, pc, cc, qc, AI.get_idx(qc, qid0))
           else AI.get_idx(qc, qid0) >= mx;
      if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 || pc == e1 + 1 {
        assert false;                               // Fork/SetQuantToClock/BeginLoop/EndLoop/Jmp
      } else {
        assert pcb + 3 <= pc < e1;
        var qv := AI.get_idx(qc, qid0);
        NestInvLookSite(r1, code, pcb + 3, e1, pc, cc, qc, qv, lid);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && if pc == pcb then
             (AI.get_idx(cc, CP.start_reg(cid)) < mx || AI.get_idx(cc, CP.start_reg(cid)) < 0)
             && AllStaleRE(r1, cc, mx)
           else
             AI.get_idx(cc, CP.start_reg(cid)) >= mx
             && AI.get_idx(cc, CP.start_reg(cid)) >= 0
             && (pcb + 1 <= pc < e1 ==> NestInvRE(r1, code, pcb + 1, e1, pc, cc, qc, mx));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      if pc == pcb || pc == e1 {
        assert false;                               // SetRegisterToCP ≠ CheckOracle
      } else {
        assert pcb + 1 <= pc < e1;
        NestInvLookSite(r1, code, pcb + 1, e1, pc, cc, qc, mx, lid);
        // ancestor clause: own start fresh (from the NestInv claims above).
      }
    case Re_lookaround(lid0, la, r1) =>
      // the whole block is the single gate instruction; a positive flavour
      // compiles to CheckOracle(lid0), pinning lid == lid0.
      assert pc == pcb;
      assert la.Lookahead? || la.Lookbehind?;       // NegCheckOracle otherwise
      assert lid == lid0;
      assert lid0 >= 0;                             // LookUnique
      assert (lid as nat) in LTB.LookIds(re);
    case Re_anchor(_) =>
      assert pc == pcb;
      assert false;
  }

  // ==========================================================================
  // L3a (E3): PRESERVATION BRICKS for the look-path carrier. The composite
  // carries, per (thread, gmt) pair, `LookPathPresent` + the lc-dominance pair
  // for every lid owning a leaf-present inside-look group. These bricks are
  // the per-instruction effects: a fresh capture stamp is monotone, a quant
  // re-stamp off the path is invisible, a quant re-stamp ON the path is
  // vacated by the B-side Reset (the ownership brick), and a gate crossing
  // establishes the fact outright from the thread's positional invariant.
  // ==========================================================================

  /** Congruence in the quant bank alone: the descent reads `qc` only at `r`'s
      own quant slots. */
  lemma LookPathPresentQcAgree(r: R.regex, cc: seq<int>, qc: seq<int>, qc': seq<int>,
                               mx: int, lid: nat)
    requires lid in LTB.LookIds(r)
    requires forall q: nat :: q in PIV.QuantIds(r) ==>
      AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
    ensures LookPathPresent(r, cc, qc, mx, lid) == LookPathPresent(r, cc, qc', mx, lid)
    ensures MxAtLidLk(r, qc, mx, lid) == MxAtLidLk(r, qc', mx, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r) && PIV.QuantIds(r2) <= PIV.QuantIds(r);
      if lid in LTB.LookIds(r1) { LookPathPresentQcAgree(r1, cc, qc, qc', mx, lid); }
      else { LookPathPresentQcAgree(r2, cc, qc, qc', mx, lid); }
    case Re_con(r1, r2) =>
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r) && PIV.QuantIds(r2) <= PIV.QuantIds(r);
      if lid in LTB.LookIds(r1) { LookPathPresentQcAgree(r1, cc, qc, qc', mx, lid); }
      else { LookPathPresentQcAgree(r2, cc, qc, qc', mx, lid); }
    case Re_quant(_, qid, _, r1) =>
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r);
      assert AI.get_idx(qc, qid) == AI.get_idx(qc', qid) by {
        if qid >= 0 { assert (qid as nat) in PIV.QuantIds(r); }
      }
      LookPathPresentQcAgree(r1, cc, qc, qc', AI.get_idx(qc, qid), lid);
    case Re_capture(_, r1) =>
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r);
      LookPathPresentQcAgree(r1, cc, qc, qc', mx, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        assert PIV.QuantIds(r1) <= PIV.QuantIds(r);
        LookPathPresentQcAgree(r1, cc, qc, qc', -1, lid);
      }
  }

  /** A FRESH capture-clock write is monotone for the path claims: every slot
      either keeps its value or jumps to a stamp `>= B` that beats every stored
      quant clock (hence every `mx` on the path). `MxAtLidLk` reads no capture
      slot, so the threshold is unchanged. */
  lemma LookPathPresentFreshCap(r: R.regex, cc: seq<int>, cc': seq<int>, qc: seq<int>,
                                mx: int, lid: nat, B: int)
    requires lid in LTB.LookIds(r)
    requires -1 <= B && mx <= B
    requires forall k :: AI.get_idx(qc, k) <= B
    requires forall j: int :: AI.get_idx(cc', j) == AI.get_idx(cc, j)
                           || (AI.get_idx(cc', j) >= 0 && AI.get_idx(cc', j) >= B)
    requires LookPathPresent(r, cc, qc, mx, lid)
    ensures LookPathPresent(r, cc', qc, mx, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookPathPresentFreshCap(r1, cc, cc', qc, mx, lid, B); }
      else { LookPathPresentFreshCap(r2, cc, cc', qc, mx, lid, B); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookPathPresentFreshCap(r1, cc, cc', qc, mx, lid, B); }
      else { LookPathPresentFreshCap(r2, cc, cc', qc, mx, lid, B); }
    case Re_quant(_, qid, _, r1) =>
      var qv := AI.get_idx(qc, qid);
      assert qv <= B;
      LookPathPresentFreshCap(r1, cc, cc', qc, qv, lid, B);
    case Re_capture(cid, r1) =>
      assert AI.get_idx(cc', CP.start_reg(cid)) >= 0
          && AI.get_idx(cc', CP.start_reg(cid)) >= mx;
      LookPathPresentFreshCap(r1, cc, cc', qc, mx, lid, B);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        LookPathPresentFreshCap(r1, cc, cc', qc, -1, lid, B);
      }
  }

  /** `QidBody`'s look ids are among `r`'s (a subtree). */
  lemma QidBodyLookIdsSub(r: R.regex, qid: nat)
    requires qid in PIV.QuantIds(r)
    ensures LTB.LookIds(PIV.QidBody(r, qid)) <= LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if qid in PIV.QuantIds(r1) { QidBodyLookIdsSub(r1, qid); } else { QidBodyLookIdsSub(r2, qid); }
    case Re_con(r1, r2) =>
      if qid in PIV.QuantIds(r1) { QidBodyLookIdsSub(r1, qid); } else { QidBodyLookIdsSub(r2, qid); }
    case Re_quant(_, qid0, _, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid {} else { QidBodyLookIdsSub(r1, qid); }
    case Re_capture(_, r1) => QidBodyLookIdsSub(r1, qid);
    case Re_lookaround(_, _, r1) => QidBodyLookIdsSub(r1, qid);
  }

  /** OFF-PATH quant re-stamp: if `lid`'s node is NOT inside `qid`'s body,
      `qid` never sits on the descent to `lid`, so a bank differing only at
      `qid`'s slot leaves the path claims and threshold unchanged. */
  lemma LookPathPresentQuantOffPath(r: R.regex, cc: seq<int>, qc: seq<int>, qc': seq<int>,
                                    mx: int, lid: nat, qid: nat)
    requires PIV.QuantUnique(r)
    requires lid in LTB.LookIds(r) && qid in PIV.QuantIds(r)
    requires lid !in LTB.LookIds(PIV.QidBody(r, qid))
    requires forall j: int :: j != qid as int ==> AI.get_idx(qc', j) == AI.get_idx(qc, j)
    ensures LookPathPresent(r, cc, qc, mx, lid) == LookPathPresent(r, cc, qc', mx, lid)
    ensures MxAtLidLk(r, qc, mx, lid) == MxAtLidLk(r, qc', mx, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        if qid in PIV.QuantIds(r1) {
          LookPathPresentQuantOffPath(r1, cc, qc, qc', mx, lid, qid);
        } else {
          assert qid in PIV.QuantIds(r2);
          assert forall q: nat :: q in PIV.QuantIds(r1) ==>
            AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
          by {
            forall q: nat | q in PIV.QuantIds(r1)
              ensures AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
            {
              assert q != qid by {
                if q == qid { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
              }
            }
          }
          LookPathPresentQcAgree(r1, cc, qc, qc', mx, lid);
        }
      } else {
        if qid in PIV.QuantIds(r2) {
          assert qid !in PIV.QuantIds(r1) by {
            if qid in PIV.QuantIds(r1) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
          }
          assert PIV.QidBody(r, qid) == PIV.QidBody(r2, qid);
          LookPathPresentQuantOffPath(r2, cc, qc, qc', mx, lid, qid);
        } else {
          assert qid in PIV.QuantIds(r1);
          assert forall q: nat :: q in PIV.QuantIds(r2) ==>
            AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
          by {
            forall q: nat | q in PIV.QuantIds(r2)
              ensures AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
            {
              assert q != qid by {
                if q == qid { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
              }
            }
          }
          LookPathPresentQcAgree(r2, cc, qc, qc', mx, lid);
        }
      }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        if qid in PIV.QuantIds(r1) {
          LookPathPresentQuantOffPath(r1, cc, qc, qc', mx, lid, qid);
        } else {
          assert qid in PIV.QuantIds(r2);
          assert forall q: nat :: q in PIV.QuantIds(r1) ==>
            AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
          by {
            forall q: nat | q in PIV.QuantIds(r1)
              ensures AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
            {
              assert q != qid by {
                if q == qid { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
              }
            }
          }
          LookPathPresentQcAgree(r1, cc, qc, qc', mx, lid);
        }
      } else {
        if qid in PIV.QuantIds(r2) {
          assert qid !in PIV.QuantIds(r1) by {
            if qid in PIV.QuantIds(r1) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
          }
          assert PIV.QidBody(r, qid) == PIV.QidBody(r2, qid);
          LookPathPresentQuantOffPath(r2, cc, qc, qc', mx, lid, qid);
        } else {
          assert qid in PIV.QuantIds(r1);
          assert forall q: nat :: q in PIV.QuantIds(r2) ==>
            AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
          by {
            forall q: nat | q in PIV.QuantIds(r2)
              ensures AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
            {
              assert q != qid by {
                if q == qid { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
              }
            }
          }
          LookPathPresentQcAgree(r2, cc, qc, qc', mx, lid);
        }
      }
    case Re_quant(_, qid0, _, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid {
        // qid IS an ancestor of every look in this subtree — contradiction
        assert PIV.QidBody(r, qid) == r1;
        assert lid in LTB.LookIds(r1);
        assert false;
      } else {
        assert qid in PIV.QuantIds(r1);
        assert AI.get_idx(qc, qid0) == AI.get_idx(qc', qid0) by {
          if qid0 >= 0 { assert (qid0 as nat) != qid; }
          else { assert qid0 != qid as int; }
        }
        LookPathPresentQuantOffPath(r1, cc, qc, qc', AI.get_idx(qc, qid0), lid, qid);
      }
    case Re_capture(_, r1) =>
      LookPathPresentQuantOffPath(r1, cc, qc, qc', mx, lid, qid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        assert lid in LTB.LookIds(r1);
        LookPathPresentQuantOffPath(r1, cc, qc, qc', -1, lid, qid);
      }
  }

  /** ON-PATH ownership: if `lid`'s node sits inside `qid`'s body, the look's
      captures are inside `qid`'s reset scope (`CapIds(QidBody)`) — so the
      B-side `Reset` at `qid`'s stamp removes every group `lid` owns, vacating
      the carrier's hypothesis for `lid`. */
  lemma LookBodyCapsUnderQid(r: R.regex, qid: nat, lid: nat)
    requires PIV.QuantUnique(r) && LTB.LookUnique(r)
    requires qid in PIV.QuantIds(r) && lid in LTB.LookIds(r)
    requires lid in LTB.LookIds(PIV.QidBody(r, qid))
    ensures PIV.CapIds(LookBodyOfRE(r, lid)) <= PIV.CapIds(PIV.QidBody(r, qid))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if qid in PIV.QuantIds(r1) {
        QidBodyLookIdsSub(r1, qid);
        assert lid in LTB.LookIds(r1);
        LookBodyCapsUnderQid(r1, qid, lid);
      } else {
        QidBodyLookIdsSub(r2, qid);
        assert lid in LTB.LookIds(r2);
        assert lid !in LTB.LookIds(r1) by {
          if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); }
        }
        LookBodyCapsUnderQid(r2, qid, lid);
      }
    case Re_con(r1, r2) =>
      if qid in PIV.QuantIds(r1) {
        QidBodyLookIdsSub(r1, qid);
        assert lid in LTB.LookIds(r1);
        LookBodyCapsUnderQid(r1, qid, lid);
      } else {
        QidBodyLookIdsSub(r2, qid);
        assert lid in LTB.LookIds(r2);
        assert lid !in LTB.LookIds(r1) by {
          if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); }
        }
        LookBodyCapsUnderQid(r2, qid, lid);
      }
    case Re_quant(_, qid0, _, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid {
        assert PIV.QidBody(r, qid) == r1;
        LookBodyCapsIn(r1, lid);
        PIV.CapIdsSplit(r1);
      } else {
        LookBodyCapsUnderQid(r1, qid, lid);
      }
    case Re_capture(_, r1) =>
      LookBodyCapsUnderQid(r1, qid, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
        // QidBody descends into r1, but lid's own node is HERE: qid in
        // QuantIds(r1) with lid in LookIds(QidBody(r1, qid)) <= LookIds(r1)
        // contradicts lid !in LookIds(r1) (LookUnique).
        QidBodyLookIdsSub(r1, qid);
        assert lid in LTB.LookIds(r1);
        assert false;
      } else {
        LookBodyCapsUnderQid(r1, qid, lid);
      }
  }

  /** Distinct lids own DISJOINT capture ids (the re-structural version of the
      table-level `LmOfBodiesDisjoint`): each body's captures sit under exactly
      one branch and `CapUnique` makes sibling branches share none. */
  lemma LookBodiesCapsDisjoint(r: R.regex, l1: nat, l2: nat)
    requires NR.LookBehindFragmentRE(r)
    requires PIV.CapUnique(r) && LTB.LookUnique(r)
    requires l1 in LTB.LookIds(r) && l2 in LTB.LookIds(r) && l1 != l2
    ensures PIV.CapIds(LookBodyOfRE(r, l1)) * PIV.CapIds(LookBodyOfRE(r, l2)) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if l1 in LTB.LookIds(r1) && l2 in LTB.LookIds(r1) {
        LookBodiesCapsDisjoint(r1, l1, l2);
      } else if l1 !in LTB.LookIds(r1) && l2 !in LTB.LookIds(r1) {
        LookBodiesCapsDisjoint(r2, l1, l2);
      } else {
        // split: one body per branch; CapUnique makes the branches disjoint
        if l1 in LTB.LookIds(r1) {
          LookBodyCapsIn(r1, l1); LookBodyCapsIn(r2, l2);
        } else {
          LookBodyCapsIn(r2, l1); LookBodyCapsIn(r1, l2);
        }
        forall g: nat | g in PIV.CapIds(LookBodyOfRE(r, l1)) * PIV.CapIds(LookBodyOfRE(r, l2))
          ensures false
        {
          assert g in PIV.CapIds(r1) * PIV.CapIds(r2);
        }
      }
    case Re_con(r1, r2) =>
      if l1 in LTB.LookIds(r1) && l2 in LTB.LookIds(r1) {
        LookBodiesCapsDisjoint(r1, l1, l2);
      } else if l1 !in LTB.LookIds(r1) && l2 !in LTB.LookIds(r1) {
        LookBodiesCapsDisjoint(r2, l1, l2);
      } else {
        if l1 in LTB.LookIds(r1) {
          LookBodyCapsIn(r1, l1); LookBodyCapsIn(r2, l2);
        } else {
          LookBodyCapsIn(r2, l1); LookBodyCapsIn(r1, l2);
        }
        forall g: nat | g in PIV.CapIds(LookBodyOfRE(r, l1)) * PIV.CapIds(LookBodyOfRE(r, l2))
          ensures false
        {
          assert g in PIV.CapIds(r1) * PIV.CapIds(r2);
        }
      }
    case Re_quant(_, _, _, r1) => LookBodiesCapsDisjoint(r1, l1, l2);
    case Re_capture(_, r1) => LookBodiesCapsDisjoint(r1, l1, l2);
    case Re_lookaround(lid0, _, r1) =>
      // both lids under one look node: at most one can BE the node (l1 != l2),
      // and the body is where the other lives — but a body inside r contains
      // both only if both are in LookIds(r1), where the node's own lid cannot
      // recur (LookUnique).
      // fragment: the body is look-free, so it contains no look at all —
      // whichever of l1/l2 is not THIS node has nowhere to live.
      assert NR.LookFreeRE(r1);
      LookFreeNoLookIdsN(r1);
      if lid0 >= 0 && (lid0 as nat) == l1 {
        assert l2 in LTB.LookIds(r1);
        assert false;
      } else if lid0 >= 0 && (lid0 as nat) == l2 {
        assert l1 in LTB.LookIds(r1);
        assert false;
      } else {
        assert l1 in LTB.LookIds(r1);
        assert false;
      }
  }

  /** The FOREST generalization of `LookBodiesCapsDisjoint` (nesting-aware, and
      fragment-INDEPENDENT — pure structure + unique ids). For two distinct look
      ids, either their bodies' captures are DISJOINT (sibling / unrelated
      nodes), or one node is NESTED in the other's body and then the inner
      body's captures are a SUBSET of the outer's. `LookBodiesCapsDisjoint`
      proved only the disjoint arm by forcing look-free bodies; under L4 nesting
      the capture pass needs this trichotomy (owner-of-g = the INNERMOST lid
      whose body contains g, resolved by the subset ordering). */
  lemma LookBodiesCapsDisjointOrNested(r: R.regex, l1: nat, l2: nat)
    requires PIV.CapUnique(r) && LTB.LookUnique(r)
    requires l1 in LTB.LookIds(r) && l2 in LTB.LookIds(r) && l1 != l2
    ensures (PIV.CapIds(LookBodyOfRE(r, l1)) * PIV.CapIds(LookBodyOfRE(r, l2)) == {})
         || (l2 in LTB.LookIds(LookBodyOfRE(r, l1))
             && PIV.CapIds(LookBodyOfRE(r, l2)) <= PIV.CapIds(LookBodyOfRE(r, l1)))
         || (l1 in LTB.LookIds(LookBodyOfRE(r, l2))
             && PIV.CapIds(LookBodyOfRE(r, l1)) <= PIV.CapIds(LookBodyOfRE(r, l2)))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if l1 in LTB.LookIds(r1) && l2 in LTB.LookIds(r1) {
        LookBodiesCapsDisjointOrNested(r1, l1, l2);
      } else if l1 !in LTB.LookIds(r1) && l2 !in LTB.LookIds(r1) {
        LookBodiesCapsDisjointOrNested(r2, l1, l2);
      } else {
        // split: one lid per branch; CapUnique makes their bodies' caps disjoint
        if l1 in LTB.LookIds(r1) { LookBodyCapsIn(r1, l1); LookBodyCapsIn(r2, l2); }
        else { LookBodyCapsIn(r2, l1); LookBodyCapsIn(r1, l2); }
        forall g: nat | g in PIV.CapIds(LookBodyOfRE(r, l1)) * PIV.CapIds(LookBodyOfRE(r, l2))
          ensures false
        { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); }
      }
    case Re_con(r1, r2) =>
      if l1 in LTB.LookIds(r1) && l2 in LTB.LookIds(r1) {
        LookBodiesCapsDisjointOrNested(r1, l1, l2);
      } else if l1 !in LTB.LookIds(r1) && l2 !in LTB.LookIds(r1) {
        LookBodiesCapsDisjointOrNested(r2, l1, l2);
      } else {
        if l1 in LTB.LookIds(r1) { LookBodyCapsIn(r1, l1); LookBodyCapsIn(r2, l2); }
        else { LookBodyCapsIn(r2, l1); LookBodyCapsIn(r1, l2); }
        forall g: nat | g in PIV.CapIds(LookBodyOfRE(r, l1)) * PIV.CapIds(LookBodyOfRE(r, l2))
          ensures false
        { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); }
      }
    case Re_quant(_, _, _, r1) => LookBodiesCapsDisjointOrNested(r1, l1, l2);
    case Re_capture(_, r1) => LookBodiesCapsDisjointOrNested(r1, l1, l2);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == l1 {
        // l1 IS this node (body r1); l2 != lid0, so l2 is NESTED in r1
        assert l2 in LTB.LookIds(r1);
        assert LookBodyOfRE(r, l1) == r1;
        assert LookBodyOfRE(r, l2) == LookBodyOfRE(r1, l2);   // lid0 != l2
        LookBodyCapsIn(r1, l2);                               // caps(body l2) <= caps(r1)
      } else if lid0 >= 0 && (lid0 as nat) == l2 {
        // symmetric: l2 IS this node, l1 nested in r1
        assert l1 in LTB.LookIds(r1);
        assert LookBodyOfRE(r, l2) == r1;
        assert LookBodyOfRE(r, l1) == LookBodyOfRE(r1, l1);
        LookBodyCapsIn(r1, l1);
      } else {
        // neither IS this node: both nested deeper in r1
        assert l1 in LTB.LookIds(r1) && l2 in LTB.LookIds(r1);
        assert LookBodyOfRE(r, l1) == LookBodyOfRE(r1, l1);
        assert LookBodyOfRE(r, l2) == LookBodyOfRE(r1, l2);
        LookBodiesCapsDisjointOrNested(r1, l1, l2);
      }
  }

  /** Every nested capture has a well-defined INNERMOST owner: a look id whose
      body contains `g` DIRECTLY (`g !in CapIdsInLooks` of that body — it is not
      buried in a still-deeper look). Constructed by descending into the branch
      / nested look that carries `g`. Combined with the trichotomy this owner is
      the subset-minimal container (see `InnermostOwnerMinimal`) — the lid whose
      replay reconstructs `g`'s value at L4. */
  lemma InnermostLookOwnerExists(r: R.regex, g: nat) returns (owner: nat)
    requires LTB.LookUnique(r)
    requires g in PIV.CapIdsInLooks(r)
    ensures owner in LTB.LookIds(r)
    ensures g in PIV.CapIds(LookBodyOfRE(r, owner))
    ensures g !in PIV.CapIdsInLooks(LookBodyOfRE(r, owner))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if g in PIV.CapIdsInLooks(r1) {
        owner := InnermostLookOwnerExists(r1, g);
      } else {
        owner := InnermostLookOwnerExists(r2, g);
        assert owner !in LTB.LookIds(r1);   // LookUnique: disjoint sibling lids
      }
    case Re_con(r1, r2) =>
      if g in PIV.CapIdsInLooks(r1) {
        owner := InnermostLookOwnerExists(r1, g);
      } else {
        owner := InnermostLookOwnerExists(r2, g);
        assert owner !in LTB.LookIds(r1);
      }
    case Re_quant(_, _, _, r1) => owner := InnermostLookOwnerExists(r1, g);
    case Re_capture(_, r1) => owner := InnermostLookOwnerExists(r1, g);
    case Re_lookaround(lid0, _, r1) =>
      // CapIdsInLooks(r) == CapIds(r1): either g is buried in a nested look
      // (recurse for a deeper owner), or it sits directly in r1 (this is it).
      if g in PIV.CapIdsInLooks(r1) {
        owner := InnermostLookOwnerExists(r1, g);
        assert (lid0 as nat) != owner;   // LookUnique: lid0 !in LookIds(r1)
      } else {
        PIV.CapIdsSplit(r1);             // g in CapIds(r1) \ CapIdsInLooks(r1)
        owner := lid0 as nat;
      }
  }

  /** `LookBodyOfRE` composes: finding an INNER lid in the whole tree is the same
      as finding it inside the OUTER lid's body (unique ids mean the inner node
      occurs exactly there). The lens that turns "nested in owner's body" into a
      capture fact about the whole tree. */
  lemma LookBodyCompose(r: R.regex, outer: nat, inner: nat)
    requires LTB.LookUnique(r)
    requires outer in LTB.LookIds(r)
    requires inner in LTB.LookIds(LookBodyOfRE(r, outer))
    ensures inner in LTB.LookIds(r)
    ensures LookBodyOfRE(r, inner) == LookBodyOfRE(LookBodyOfRE(r, outer), inner)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if outer in LTB.LookIds(r1) { LookBodyCompose(r1, outer, inner); assert inner in LTB.LookIds(r1); }
      else { LookBodyCompose(r2, outer, inner); assert inner !in LTB.LookIds(r1); }
    case Re_con(r1, r2) =>
      if outer in LTB.LookIds(r1) { LookBodyCompose(r1, outer, inner); assert inner in LTB.LookIds(r1); }
      else { LookBodyCompose(r2, outer, inner); assert inner !in LTB.LookIds(r1); }
    case Re_quant(_, _, _, r1) => LookBodyCompose(r1, outer, inner);
    case Re_capture(_, r1) => LookBodyCompose(r1, outer, inner);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == outer {
        // outer IS this node: its body is r1, and inner lives in r1
        assert LookBodyOfRE(r, outer) == r1;
        assert inner in LTB.LookIds(r1);
        assert (lid0 as nat) != inner;   // LookUnique: lid0 !in LookIds(r1)
      } else {
        // outer is nested deeper in r1
        assert outer in LTB.LookIds(r1);
        LookBodyCompose(r1, outer, inner);
        assert (lid0 as nat) != inner;
      }
  }

  /** The innermost owner is the SUBSET-MINIMAL container: any other look whose
      body holds `g` has a superset of the owner's captures. Rules out the
      trichotomy's disjoint arm (both bodies hold `g`) and its "l nested in
      owner" arm (that would bury `g` in a look inside owner's body, but the
      owner holds `g` DIRECTLY), leaving "owner nested in l" — the subset. */
  lemma InnermostOwnerMinimal(r: R.regex, g: nat, owner: nat, l: nat)
    requires PIV.CapUnique(r) && LTB.LookUnique(r)
    requires owner in LTB.LookIds(r) && g in PIV.CapIds(LookBodyOfRE(r, owner))
    requires g !in PIV.CapIdsInLooks(LookBodyOfRE(r, owner))
    requires l in LTB.LookIds(r) && g in PIV.CapIds(LookBodyOfRE(r, l))
    ensures PIV.CapIds(LookBodyOfRE(r, owner)) <= PIV.CapIds(LookBodyOfRE(r, l))
  {
    if owner == l {
    } else {
      LookBodiesCapsDisjointOrNested(r, owner, l);
      if PIV.CapIds(LookBodyOfRE(r, owner)) * PIV.CapIds(LookBodyOfRE(r, l)) == {} {
        assert g in PIV.CapIds(LookBodyOfRE(r, owner)) * PIV.CapIds(LookBodyOfRE(r, l));  // false
      } else if l in LTB.LookIds(LookBodyOfRE(r, owner))
                && PIV.CapIds(LookBodyOfRE(r, l)) <= PIV.CapIds(LookBodyOfRE(r, owner)) {
        // l nested in owner's body: g would then sit in a nested look — contradiction
        LookBodyCompose(r, owner, l);
        LookBodyCapsIn(LookBodyOfRE(r, owner), l);
        assert g in PIV.CapIdsInLooks(LookBodyOfRE(r, owner));
      } else {
        // owner nested in l: the subset holds
      }
    }
  }

  /** The structural body IS the table row's body: `LookTablesOk` records a
      `LookEntryOk` row at every look node, and the row at `lid` pins
      `fc.f_look_ast[lid]` — so the table body and `LookBodyOfRE` agree. */
  lemma LookBodyOfTablesTie(re: R.regex, fc: CP.FCompiled, lid: nat)
    requires LTB.LookTablesOk(re, fc)
    requires lid in LTB.LookIds(re)
    ensures var li: int := lid as int;   // (2026-08-28) cast-free trigger term for the exists
            exists la: R.lookaround :: LTB.LookEntryOk(fc, li, la, LookBodyOfRE(re, lid))
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyOfTablesTie(r1, fc, lid); }
      else { LookBodyOfTablesTie(r2, fc, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyOfTablesTie(r1, fc, lid); }
      else { LookBodyOfTablesTie(r2, fc, lid); }
    case Re_quant(_, _, _, r1) => LookBodyOfTablesTie(r1, fc, lid);
    case Re_capture(_, r1) => LookBodyOfTablesTie(r1, fc, lid);
    case Re_lookaround(lid0, la0, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
        assert LTB.LookEntryOk(fc, lid as int, la0, r1);
      } else {
        LookBodyOfTablesTie(r1, fc, lid);
      }
  }

  // ==========================================================================
  // L3a (E4): the DOMINANCE predicate for the CONVERSE carrier — the look
  // stamp beats EVERY quantifier clock on the path (not just the innermost
  // threshold): exactly the fact that survives an outer-quant re-stamp check
  // and breaks precisely when any enclosing quant re-stamps after the
  // crossing. "Dominance at the end" therefore means "no reset touched the
  // look's groups since the last crossing".
  // ==========================================================================
  ghost predicate LookPathDom(r: R.regex, L: int, qc: seq<int>, lid: nat)
    requires lid in LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) then LookPathDom(r1, L, qc, lid) else LookPathDom(r2, L, qc, lid)
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) then LookPathDom(r1, L, qc, lid) else LookPathDom(r2, L, qc, lid)
    case Re_quant(_, qid, _, r1) =>
      L >= AI.get_idx(qc, qid) && LookPathDom(r1, L, qc, lid)
    case Re_capture(_, r1) => LookPathDom(r1, L, qc, lid)
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid then true else LookPathDom(r1, L, qc, lid)
  }

  /** Under path presence the threshold at the look node bounds the running
      `mx` from below (the path-quant clocks form an increasing chain).
      Fragment-scoped: a foreign look on the path would reset the chain. */
  lemma MxAtLidGeMx(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, lid: nat)
    requires NR.LookBehindFragmentRE(r)
    requires lid in LTB.LookIds(r)
    requires LookPathPresent(r, cc, qc, mx, lid)
    ensures MxAtLidLk(r, qc, mx, lid) >= mx
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { MxAtLidGeMx(r1, cc, qc, mx, lid); }
      else { MxAtLidGeMx(r2, cc, qc, mx, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { MxAtLidGeMx(r1, cc, qc, mx, lid); }
      else { MxAtLidGeMx(r2, cc, qc, mx, lid); }
    case Re_quant(_, qid, _, r1) =>
      var qv := AI.get_idx(qc, qid);
      assert qv >= mx;                          // LookPathPresent
      MxAtLidGeMx(r1, cc, qc, qv, lid);
    case Re_capture(_, r1) => MxAtLidGeMx(r1, cc, qc, mx, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        assert NR.LookFreeRE(r1);
        LookFreeNoLookIdsN(r1);
        assert lid in LTB.LookIds(r1);
        assert false;
      }
  }

  /** Path presence + look-stamp-over-threshold yield FULL dominance: the
      quant clocks on the path form an increasing chain up to the threshold. */
  lemma LookPathDomIntro(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, lid: nat, L: int)
    requires NR.LookBehindFragmentRE(r)
    requires lid in LTB.LookIds(r)
    requires LookPathPresent(r, cc, qc, mx, lid)
    requires L >= MxAtLidLk(r, qc, mx, lid)
    ensures LookPathDom(r, L, qc, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookPathDomIntro(r1, cc, qc, mx, lid, L); }
      else { LookPathDomIntro(r2, cc, qc, mx, lid, L); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookPathDomIntro(r1, cc, qc, mx, lid, L); }
      else { LookPathDomIntro(r2, cc, qc, mx, lid, L); }
    case Re_quant(_, qid, _, r1) =>
      var qv := AI.get_idx(qc, qid);
      MxAtLidGeMx(r1, cc, qc, qv, lid);
      assert MxAtLidLk(r1, qc, qv, lid) >= qv;
      assert L >= qv;
      LookPathDomIntro(r1, cc, qc, qv, lid, L);
    case Re_capture(_, r1) =>
      LookPathDomIntro(r1, cc, qc, mx, lid, L);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        assert NR.LookFreeRE(r1);
        LookFreeNoLookIdsN(r1);
        assert lid in LTB.LookIds(r1);
        assert false;
      }
  }

  /** (DEEP reverse-recon — BODY-LEVEL dominance is TRIVIAL under no-anc-quants)
      For a look `lid` whose body owns a capture `g2` that sits under NO quantifier
      in `r` (`AncQuants(r, g2) == {}` — the fragment's `GNotUnderQuantL` shadow
      via `M.GNotUnderQuantLNoAncQuants`), the path from `r`'s root to `lid`'s node
      crosses NO `Re_quant` — so `LookPathDom(r, L, qc, lid)` holds for EVERY stamp
      `L >= -1` and EVERY quant bank `qc`, structurally. This is why the deep
      descent's per-LEVEL dominance obligations (inside look bodies) are free: an
      escaped-look scenario needs the look under a quantifier, which would put its
      captures under a quantifier inside an enclosing look — out of fragment. Only
      the TOP level (quants outside looks) needs the real dominance connective. */
  lemma LookPathDomNoAncQuants(r: R.regex, L: int, qc: seq<int>, lid: nat, g2: nat)
    requires PIV.CapUnique(r)
    requires lid in LTB.LookIds(r)
    requires g2 in PIV.CapIds(r)
    requires g2 in PIV.CapIds(LookBodyOfRE(r, lid))
    requires PIV.AncQuants(r, g2) == {}
    requires L >= -1
    ensures LookPathDom(r, L, qc, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        LookBodyCapsIn(r1, lid);                       // g2 in CapIds(r1)
        assert g2 in PIV.CapIds(r1);
        LookPathDomNoAncQuants(r1, L, qc, lid, g2);
      } else {
        LookBodyCapsIn(r2, lid);
        assert g2 in PIV.CapIds(r2);
        assert g2 !in PIV.CapIds(r1) by {
          if g2 in PIV.CapIds(r1) { assert g2 in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
        LookPathDomNoAncQuants(r2, L, qc, lid, g2);
      }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        LookBodyCapsIn(r1, lid);
        assert g2 in PIV.CapIds(r1);
        LookPathDomNoAncQuants(r1, L, qc, lid, g2);
      } else {
        LookBodyCapsIn(r2, lid);
        assert g2 in PIV.CapIds(r2);
        assert g2 !in PIV.CapIds(r1) by {
          if g2 in PIV.CapIds(r1) { assert g2 in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
        LookPathDomNoAncQuants(r2, L, qc, lid, g2);
      }
    case Re_quant(nul, qid, q, r1) =>
      // a real quant id on g2's path would land in AncQuants(r, g2) == {}.
      LookBodyCapsIn(r1, lid);
      assert g2 in PIV.CapIds(r1);
      assert qid < 0 by {
        if qid >= 0 { assert (qid as nat) in PIV.AncQuants(r, g2); }
      }
      assert AI.get_idx(qc, qid) == -1;                // out-of-range read
      LookPathDomNoAncQuants(r1, L, qc, lid, g2);
    case Re_capture(cid, r1) =>
      LookBodyCapsIn(r1, lid);
      assert g2 in PIV.CapIds(r1);
      assert !(cid >= 0 && (cid as nat) == g2);        // CapUnique: cid !in CapIds(r1)
      LookPathDomNoAncQuants(r1, L, qc, lid, g2);
    case Re_lookaround(lid0, la, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
        // LookPathDom returns true at the target node
      } else {
        LookBodyCapsIn(r1, lid);
        assert g2 in PIV.CapIds(r1);
        LookPathDomNoAncQuants(r1, L, qc, lid, g2);
      }
  }

  /** (FORWARD base) `PathPresentLk` transport for a DIRECT no-anc-quant capture:
      the path from the root to `g` crosses NO look node (g outside looks) and NO
      quant node (`AncQuants == {}`), so it reads ONLY capture-start clocks — two
      bank tuples agreeing there give the same verdict and the same `MxAtGidLk`.
      This moves the fresh-body-match presence onto the reconstructed banks with
      no look/quant agreement at all (which would be false at deep lids). */
  lemma PathPresentLkDirectAgree(r: R.regex, cc1: seq<int>, lc1: seq<int>, qc1: seq<int>,
                                 cc2: seq<int>, lc2: seq<int>, qc2: seq<int>, g: nat)
    requires PIV.CapUnique(r)
    requires g in PIV.CapIds(r) && g !in PIV.CapIdsInLooks(r)
    requires PIV.AncQuants(r, g) == {}
    requires forall c: nat :: c in PIV.CapIdsOutsideLooks(r) ==>
      AI.get_idx(cc1, CP.start_reg(c)) == AI.get_idx(cc2, CP.start_reg(c))
    requires PIV.PathPresentLk(r, cc2, lc2, qc2, -1, g)
    ensures PIV.PathPresentLk(r, cc1, lc1, qc1, -1, g)
    ensures PIV.MxAtGidLk(r, cc1, lc1, qc1, -1, g) == PIV.MxAtGidLk(r, cc2, lc2, qc2, -1, g)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if g in PIV.CapIds(r1) {
        assert forall c: nat :: c in PIV.CapIdsOutsideLooks(r1) ==> c in PIV.CapIdsOutsideLooks(r);
        PathPresentLkDirectAgree(r1, cc1, lc1, qc1, cc2, lc2, qc2, g);
      } else {
        assert forall c: nat :: c in PIV.CapIdsOutsideLooks(r2) ==> c in PIV.CapIdsOutsideLooks(r);
        PathPresentLkDirectAgree(r2, cc1, lc1, qc1, cc2, lc2, qc2, g);
      }
    case Re_con(r1, r2) =>
      if g in PIV.CapIds(r1) {
        assert forall c: nat :: c in PIV.CapIdsOutsideLooks(r1) ==> c in PIV.CapIdsOutsideLooks(r);
        PathPresentLkDirectAgree(r1, cc1, lc1, qc1, cc2, lc2, qc2, g);
      } else {
        assert forall c: nat :: c in PIV.CapIdsOutsideLooks(r2) ==> c in PIV.CapIdsOutsideLooks(r);
        PathPresentLkDirectAgree(r2, cc1, lc1, qc1, cc2, lc2, qc2, g);
      }
    case Re_quant(nul, qid, q, r1) =>
      assert qid < 0 by {
        if qid >= 0 { assert (qid as nat) in PIV.AncQuants(r, g); }
      }
      assert AI.get_idx(qc1, qid) == -1 == AI.get_idx(qc2, qid);
      PathPresentLkDirectAgree(r1, cc1, lc1, qc1, cc2, lc2, qc2, g);
    case Re_capture(cid, r1) =>
      if cid >= 0 && (cid as nat) == g {
        assert (g as int) == cid;
        assert AI.get_idx(cc1, CP.start_reg(cid)) == AI.get_idx(cc2, CP.start_reg(cid)) by {
          assert (cid as nat) in PIV.CapIdsOutsideLooks(r);
        }
      } else {
        assert g in PIV.CapIds(r1);
        assert AI.get_idx(cc1, CP.start_reg(cid)) == AI.get_idx(cc2, CP.start_reg(cid)) by {
          if cid >= 0 {
            assert (cid as nat) in PIV.CapIdsOutsideLooks(r);
          } else {
            assert CP.start_reg(cid) < 0;
            assert AI.get_idx(cc1, CP.start_reg(cid)) == -1 == AI.get_idx(cc2, CP.start_reg(cid));
          }
        }
        assert forall c: nat :: c in PIV.CapIdsOutsideLooks(r1) ==> c in PIV.CapIdsOutsideLooks(r);
        PathPresentLkDirectAgree(r1, cc1, lc1, qc1, cc2, lc2, qc2, g);
      }
    case Re_lookaround(lid, la, r1) =>
      // g inside a look's body would put g in CapIdsInLooks(r)
      assert g in PIV.CapIds(r1);
      assert g in PIV.CapIdsInLooks(r);
      assert false;
  }

  /** (FORWARD wrapper) TOP-look twin of `LookPathPresentAgree` for the NESTED
      fragment: for a TOP lid the presence path reads only OUTSIDE-look capture
      starts and OUTSIDE-look quant clocks (it never enters a look body —
      `TopLookIds(Re_lookaround) == {lid0}` kills the else-branch), so two bank
      pairs agreeing there give the same `LookPathPresent` verdict and the same
      `MxAtLidLk`. */
  lemma LookPathPresentAgreeTop(r: R.regex, cc1: seq<int>, qc1: seq<int>,
                                cc2: seq<int>, qc2: seq<int>, mx: int, lid: nat)
    requires NR.NestedFragmentRE(r) && LTB.LookUnique(r)
    requires lid in LTB.LookIds(r) && lid in TopLookIds(r)
    requires forall c: nat :: c in PIV.CapIdsOutsideLooks(r) ==>
      AI.get_idx(cc1, CP.start_reg(c as int)) == AI.get_idx(cc2, CP.start_reg(c as int))
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(r) ==>
      AI.get_idx(qc1, q as int) == AI.get_idx(qc2, q as int)
    ensures LookPathPresent(r, cc1, qc1, mx, lid) == LookPathPresent(r, cc2, qc2, mx, lid)
    ensures MxAtLidLk(r, qc1, mx, lid) == MxAtLidLk(r, qc2, mx, lid)
    decreases r
  {
    TopLookIdsIn(r);
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        assert lid in TopLookIds(r1) by {
          if lid !in TopLookIds(r1) {
            assert lid in TopLookIds(r2); TopLookIdsIn(r2);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        assert forall c: nat :: c in PIV.CapIdsOutsideLooks(r1) ==> c in PIV.CapIdsOutsideLooks(r);
        assert forall q0: nat :: q0 in PIV.QuantIdsOutsideLooks(r1) ==> q0 in PIV.QuantIdsOutsideLooks(r);
        LookPathPresentAgreeTop(r1, cc1, qc1, cc2, qc2, mx, lid);
      } else {
        assert lid in TopLookIds(r2) by { TopLookIdsIn(r1); }
        assert forall c: nat :: c in PIV.CapIdsOutsideLooks(r2) ==> c in PIV.CapIdsOutsideLooks(r);
        assert forall q0: nat :: q0 in PIV.QuantIdsOutsideLooks(r2) ==> q0 in PIV.QuantIdsOutsideLooks(r);
        LookPathPresentAgreeTop(r2, cc1, qc1, cc2, qc2, mx, lid);
      }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        assert lid in TopLookIds(r1) by {
          if lid !in TopLookIds(r1) {
            assert lid in TopLookIds(r2); TopLookIdsIn(r2);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        assert forall c: nat :: c in PIV.CapIdsOutsideLooks(r1) ==> c in PIV.CapIdsOutsideLooks(r);
        assert forall q0: nat :: q0 in PIV.QuantIdsOutsideLooks(r1) ==> q0 in PIV.QuantIdsOutsideLooks(r);
        LookPathPresentAgreeTop(r1, cc1, qc1, cc2, qc2, mx, lid);
      } else {
        assert lid in TopLookIds(r2) by { TopLookIdsIn(r1); }
        assert forall c: nat :: c in PIV.CapIdsOutsideLooks(r2) ==> c in PIV.CapIdsOutsideLooks(r);
        assert forall q0: nat :: q0 in PIV.QuantIdsOutsideLooks(r2) ==> q0 in PIV.QuantIdsOutsideLooks(r);
        LookPathPresentAgreeTop(r2, cc1, qc1, cc2, qc2, mx, lid);
      }
    case Re_quant(nul, qid, q, r1) =>
      assert AI.get_idx(qc1, qid) == AI.get_idx(qc2, qid) by {
        if qid >= 0 {
          assert (qid as nat) in PIV.QuantIdsOutsideLooks(r);   // own node, definitional
        } else {
          assert AI.get_idx(qc1, qid) == -1 == AI.get_idx(qc2, qid);
        }
      }
      assert forall c: nat :: c in PIV.CapIdsOutsideLooks(r1) ==> c in PIV.CapIdsOutsideLooks(r);
      assert forall q0: nat :: q0 in PIV.QuantIdsOutsideLooks(r1) ==> q0 in PIV.QuantIdsOutsideLooks(r);
      LookPathPresentAgreeTop(r1, cc1, qc1, cc2, qc2, AI.get_idx(qc1, qid), lid);
    case Re_capture(cid, r1) =>
      assert cid >= 0 ==> (cid as nat) in PIV.CapIdsOutsideLooks(r);
      assert AI.get_idx(cc1, CP.start_reg(cid)) == AI.get_idx(cc2, CP.start_reg(cid)) by {
        if cid >= 0 {
          assert (cid as nat) in PIV.CapIdsOutsideLooks(r);
        } else {
          assert CP.start_reg(cid) < 0;
        }
      }
      assert forall c: nat :: c in PIV.CapIdsOutsideLooks(r1) ==> c in PIV.CapIdsOutsideLooks(r);
      assert forall q0: nat :: q0 in PIV.QuantIdsOutsideLooks(r1) ==> q0 in PIV.QuantIdsOutsideLooks(r);
      LookPathPresentAgreeTop(r1, cc1, qc1, cc2, qc2, mx, lid);
    case Re_lookaround(lid0, la, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        assert lid !in TopLookIds(r);
        assert false;
      }
  }

  /** (FORWARD wrapper) For a TOP lid the Lk-presence path crosses no look node,
      so plain `LookPathPresent` already IS `LookPathPresentLk` (the two differ
      only at the else-lookaround branch, vacuous for top lids). */
  lemma LookPathPresentLkFromPresentTop(r: R.regex, cc: seq<int>, lc: seq<int>, qc: seq<int>,
                                        mx: int, lid: nat)
    requires NR.NestedFragmentRE(r) && LTB.LookUnique(r)
    requires lid in LTB.LookIds(r) && lid in TopLookIds(r)
    requires LookPathPresent(r, cc, qc, mx, lid)
    ensures LookPathPresentLk(r, cc, lc, qc, mx, lid)
    decreases r
  {
    TopLookIdsIn(r);
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        assert lid in TopLookIds(r1) by {
          if lid !in TopLookIds(r1) {
            assert lid in TopLookIds(r2); TopLookIdsIn(r2);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        LookPathPresentLkFromPresentTop(r1, cc, lc, qc, mx, lid);
      } else {
        assert lid in TopLookIds(r2) by { TopLookIdsIn(r1); }
        LookPathPresentLkFromPresentTop(r2, cc, lc, qc, mx, lid);
      }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        assert lid in TopLookIds(r1) by {
          if lid !in TopLookIds(r1) {
            assert lid in TopLookIds(r2); TopLookIdsIn(r2);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        LookPathPresentLkFromPresentTop(r1, cc, lc, qc, mx, lid);
      } else {
        assert lid in TopLookIds(r2) by { TopLookIdsIn(r1); }
        LookPathPresentLkFromPresentTop(r2, cc, lc, qc, mx, lid);
      }
    case Re_quant(nul, qid, q, r1) =>
      LookPathPresentLkFromPresentTop(r1, cc, lc, qc, AI.get_idx(qc, qid), lid);
    case Re_capture(cid, r1) =>
      LookPathPresentLkFromPresentTop(r1, cc, lc, qc, mx, lid);
    case Re_lookaround(lid0, la, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        assert lid !in TopLookIds(r);
        assert false;
      }
  }

  /** (L4 depth-k, ADDITIVE) TOP-look twin of `MxAtLidGeMx` for the NESTED
      fragment. The depth-1 `MxAtLidGeMx` requires `LookBehindFragmentRE` because
      its `Re_lookaround` else-branch (lid inside a look body) is discharged by
      `LookFreeRE(r1)` (`assert false`). For a TOP look (`lid in TopLookIds(r)`)
      that else-branch is VACUOUS outright (`TopLookIds(Re_lookaround) == {lid0}`,
      so `lid == lid0`), so the same increasing-chain argument runs under
      `NestedFragmentRE` with no look-free hypothesis. `LookUnique` routes the
      alt/con descent to the branch actually holding `lid`. */
  lemma MxAtLidGeMxTop(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, lid: nat)
    requires NR.NestedFragmentRE(r) && LTB.LookUnique(r)
    requires lid in LTB.LookIds(r)
    requires lid in TopLookIds(r)
    requires LookPathPresent(r, cc, qc, mx, lid)
    ensures MxAtLidLk(r, qc, mx, lid) >= mx
    decreases r
  {
    TopLookIdsIn(r);                        // lid in LookIds(r)
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        assert lid in TopLookIds(r1) by {
          if lid !in TopLookIds(r1) {
            assert lid in TopLookIds(r2); TopLookIdsIn(r2);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        MxAtLidGeMxTop(r1, cc, qc, mx, lid);
      } else {
        assert lid in LTB.LookIds(r2);
        assert lid in TopLookIds(r2) by {
          if lid !in TopLookIds(r2) {
            assert lid in TopLookIds(r1); TopLookIdsIn(r1);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        MxAtLidGeMxTop(r2, cc, qc, mx, lid);
      }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        assert lid in TopLookIds(r1) by {
          if lid !in TopLookIds(r1) {
            assert lid in TopLookIds(r2); TopLookIdsIn(r2);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        MxAtLidGeMxTop(r1, cc, qc, mx, lid);
      } else {
        assert lid in LTB.LookIds(r2);
        assert lid in TopLookIds(r2) by {
          if lid !in TopLookIds(r2) {
            assert lid in TopLookIds(r1); TopLookIdsIn(r1);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        MxAtLidGeMxTop(r2, cc, qc, mx, lid);
      }
    case Re_quant(_, qid, _, r1) =>
      var qv := AI.get_idx(qc, qid);
      assert qv >= mx;                       // LookPathPresent
      MxAtLidGeMxTop(r1, cc, qc, qv, lid);
    case Re_capture(_, r1) => MxAtLidGeMxTop(r1, cc, qc, mx, lid);
    case Re_lookaround(lid0, _, r1) =>
      // lid in TopLookIds(r) == {lid0 as nat} (lid0 >= 0 under LookUnique): lid == lid0.
      assert lid0 >= 0 && (lid0 as nat) == lid;
  }

  /** (L4 depth-k, ADDITIVE) TOP-look twin of `LookPathDomIntro` for the NESTED
      fragment. Assembles full dominance `LookPathDom(r, L, qc, lid)` from path
      presence + a look stamp `L` beating the node threshold `MxAtLidLk`, for a
      TOP look `lid` (path never crosses a look body). Identical increasing-chain
      argument to `LookPathDomIntro`, but the `Re_lookaround` else-branch is
      vacuous for a top look, so it runs under `NestedFragmentRE`. */
  lemma LookPathDomIntroTop(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, lid: nat, L: int)
    requires NR.NestedFragmentRE(r) && LTB.LookUnique(r)
    requires lid in LTB.LookIds(r)
    requires lid in TopLookIds(r)
    requires LookPathPresent(r, cc, qc, mx, lid)
    requires L >= MxAtLidLk(r, qc, mx, lid)
    ensures LookPathDom(r, L, qc, lid)
    decreases r
  {
    TopLookIdsIn(r);
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        assert lid in TopLookIds(r1) by {
          if lid !in TopLookIds(r1) {
            assert lid in TopLookIds(r2); TopLookIdsIn(r2);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        LookPathDomIntroTop(r1, cc, qc, mx, lid, L);
      } else {
        assert lid in LTB.LookIds(r2);
        assert lid in TopLookIds(r2) by {
          if lid !in TopLookIds(r2) {
            assert lid in TopLookIds(r1); TopLookIdsIn(r1);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        LookPathDomIntroTop(r2, cc, qc, mx, lid, L);
      }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        assert lid in TopLookIds(r1) by {
          if lid !in TopLookIds(r1) {
            assert lid in TopLookIds(r2); TopLookIdsIn(r2);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        LookPathDomIntroTop(r1, cc, qc, mx, lid, L);
      } else {
        assert lid in LTB.LookIds(r2);
        assert lid in TopLookIds(r2) by {
          if lid !in TopLookIds(r2) {
            assert lid in TopLookIds(r1); TopLookIdsIn(r1);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        LookPathDomIntroTop(r2, cc, qc, mx, lid, L);
      }
    case Re_quant(_, qid, _, r1) =>
      var qv := AI.get_idx(qc, qid);
      MxAtLidGeMxTop(r1, cc, qc, qv, lid);
      assert MxAtLidLk(r1, qc, qv, lid) >= qv;
      assert L >= qv;
      LookPathDomIntroTop(r1, cc, qc, qv, lid, L);
    case Re_capture(_, r1) =>
      LookPathDomIntroTop(r1, cc, qc, mx, lid, L);
    case Re_lookaround(lid0, _, r1) =>
      assert lid0 >= 0 && (lid0 as nat) == lid;
  }

  /** A stamp beating EVERY stored quant clock dominates any path outright. */
  lemma LookPathDomAll(r: R.regex, L: int, qc: seq<int>, lid: nat)
    requires lid in LTB.LookIds(r)
    requires forall k :: AI.get_idx(qc, k) <= L
    ensures LookPathDom(r, L, qc, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookPathDomAll(r1, L, qc, lid); } else { LookPathDomAll(r2, L, qc, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookPathDomAll(r1, L, qc, lid); } else { LookPathDomAll(r2, L, qc, lid); }
    case Re_quant(_, qid, _, r1) => LookPathDomAll(r1, L, qc, lid);
    case Re_capture(_, r1) => LookPathDomAll(r1, L, qc, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {} else { LookPathDomAll(r1, L, qc, lid); }
  }

  /** Dominance reads `qc` only at the subtree's own quant slots. */
  lemma LookPathDomQcAgree(r: R.regex, L: int, qc: seq<int>, qc': seq<int>, lid: nat)
    requires lid in LTB.LookIds(r)
    requires forall q: nat :: q in PIV.QuantIds(r) ==>
      AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
    ensures LookPathDom(r, L, qc, lid) == LookPathDom(r, L, qc', lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r) && PIV.QuantIds(r2) <= PIV.QuantIds(r);
      if lid in LTB.LookIds(r1) { LookPathDomQcAgree(r1, L, qc, qc', lid); }
      else { LookPathDomQcAgree(r2, L, qc, qc', lid); }
    case Re_con(r1, r2) =>
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r) && PIV.QuantIds(r2) <= PIV.QuantIds(r);
      if lid in LTB.LookIds(r1) { LookPathDomQcAgree(r1, L, qc, qc', lid); }
      else { LookPathDomQcAgree(r2, L, qc, qc', lid); }
    case Re_quant(_, qid, _, r1) =>
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r);
      assert AI.get_idx(qc, qid) == AI.get_idx(qc', qid) by {
        if qid >= 0 { assert (qid as nat) in PIV.QuantIds(r); }
      }
      LookPathDomQcAgree(r1, L, qc, qc', lid);
    case Re_capture(_, r1) =>
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r);
      LookPathDomQcAgree(r1, L, qc, qc', lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        assert PIV.QuantIds(r1) <= PIV.QuantIds(r);
        LookPathDomQcAgree(r1, L, qc, qc', lid);
      }
  }

  /** OFF-PATH re-stamp is invisible to dominance (mirror of
      `LookPathPresentQuantOffPath`). */
  lemma LookPathDomQuantOffPath(r: R.regex, L: int, qc: seq<int>, qc': seq<int>, lid: nat, qid: nat)
    requires PIV.QuantUnique(r)
    requires lid in LTB.LookIds(r) && qid in PIV.QuantIds(r)
    requires lid !in LTB.LookIds(PIV.QidBody(r, qid))
    requires forall j: int :: j != qid as int ==> AI.get_idx(qc', j) == AI.get_idx(qc, j)
    ensures LookPathDom(r, L, qc, lid) == LookPathDom(r, L, qc', lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        if qid in PIV.QuantIds(r1) {
          LookPathDomQuantOffPath(r1, L, qc, qc', lid, qid);
        } else {
          assert forall q: nat :: q in PIV.QuantIds(r1) ==>
            AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
          by {
            forall q: nat | q in PIV.QuantIds(r1)
              ensures AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
            {
              assert q != qid by {
                if q == qid { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
              }
            }
          }
          LookPathDomQcAgree(r1, L, qc, qc', lid);
        }
      } else {
        if qid in PIV.QuantIds(r2) {
          assert qid !in PIV.QuantIds(r1) by {
            if qid in PIV.QuantIds(r1) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
          }
          assert PIV.QidBody(r, qid) == PIV.QidBody(r2, qid);
          LookPathDomQuantOffPath(r2, L, qc, qc', lid, qid);
        } else {
          assert qid in PIV.QuantIds(r1);
          assert forall q: nat :: q in PIV.QuantIds(r2) ==>
            AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
          by {
            forall q: nat | q in PIV.QuantIds(r2)
              ensures AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
            {
              assert q != qid by {
                if q == qid { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
              }
            }
          }
          LookPathDomQcAgree(r2, L, qc, qc', lid);
        }
      }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        if qid in PIV.QuantIds(r1) {
          LookPathDomQuantOffPath(r1, L, qc, qc', lid, qid);
        } else {
          assert forall q: nat :: q in PIV.QuantIds(r1) ==>
            AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
          by {
            forall q: nat | q in PIV.QuantIds(r1)
              ensures AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
            {
              assert q != qid by {
                if q == qid { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
              }
            }
          }
          LookPathDomQcAgree(r1, L, qc, qc', lid);
        }
      } else {
        if qid in PIV.QuantIds(r2) {
          assert qid !in PIV.QuantIds(r1) by {
            if qid in PIV.QuantIds(r1) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
          }
          assert PIV.QidBody(r, qid) == PIV.QidBody(r2, qid);
          LookPathDomQuantOffPath(r2, L, qc, qc', lid, qid);
        } else {
          assert qid in PIV.QuantIds(r1);
          assert forall q: nat :: q in PIV.QuantIds(r2) ==>
            AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
          by {
            forall q: nat | q in PIV.QuantIds(r2)
              ensures AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
            {
              assert q != qid by {
                if q == qid { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
              }
            }
          }
          LookPathDomQcAgree(r2, L, qc, qc', lid);
        }
      }
    case Re_quant(_, qid0, _, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid {
        assert PIV.QidBody(r, qid) == r1;
        assert lid in LTB.LookIds(r1);
        assert false;
      } else {
        assert qid in PIV.QuantIds(r1);
        assert AI.get_idx(qc, qid0) == AI.get_idx(qc', qid0) by {
          if qid0 >= 0 { assert (qid0 as nat) != qid; }
          else { assert qid0 != qid as int; }
        }
        LookPathDomQuantOffPath(r1, L, qc, qc', lid, qid);
      }
    case Re_capture(_, r1) =>
      LookPathDomQuantOffPath(r1, L, qc, qc', lid, qid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        assert lid in LTB.LookIds(r1);
        LookPathDomQuantOffPath(r1, L, qc, qc', lid, qid);
      }
  }

  /** ON-PATH re-stamp above the look stamp BREAKS dominance: the descent to
      `lid` passes through `qid`'s node, whose clause fails. */
  lemma LookPathDomOnPathBreaks(r: R.regex, L: int, qc': seq<int>, lid: nat, qid: nat)
    requires NR.LookBehindFragmentRE(r) && LTB.LookUnique(r)
    requires lid in LTB.LookIds(r) && qid in PIV.QuantIds(r)
    requires lid in LTB.LookIds(PIV.QidBody(r, qid))
    requires AI.get_idx(qc', qid as int) > L
    ensures !LookPathDom(r, L, qc', lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if qid in PIV.QuantIds(r1) {
        QidBodyLookIdsSub(r1, qid);
        assert lid in LTB.LookIds(r1);
        LookPathDomOnPathBreaks(r1, L, qc', lid, qid);
      } else {
        QidBodyLookIdsSub(r2, qid);
        assert lid in LTB.LookIds(r2);
        assert lid !in LTB.LookIds(r1) by {
          if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); }
        }
        LookPathDomOnPathBreaks(r2, L, qc', lid, qid);
      }
    case Re_con(r1, r2) =>
      if qid in PIV.QuantIds(r1) {
        QidBodyLookIdsSub(r1, qid);
        assert lid in LTB.LookIds(r1);
        LookPathDomOnPathBreaks(r1, L, qc', lid, qid);
      } else {
        QidBodyLookIdsSub(r2, qid);
        assert lid in LTB.LookIds(r2);
        assert lid !in LTB.LookIds(r1) by {
          if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); }
        }
        LookPathDomOnPathBreaks(r2, L, qc', lid, qid);
      }
    case Re_quant(_, qid0, _, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid {
        assert AI.get_idx(qc', qid0) > L;     // the node's own clause fails
      } else {
        LookPathDomOnPathBreaks(r1, L, qc', lid, qid);
      }
    case Re_capture(_, r1) =>
      LookPathDomOnPathBreaks(r1, L, qc', lid, qid);
    case Re_lookaround(lid0, _, r1) =>
      // fragment: the body is look-free, so no qid-body below can hold lid.
      assert NR.LookFreeRE(r1);
      LookFreeNoLookIdsN(r1);
      QidBodyLookIdsSub(r1, qid);
      assert lid in LTB.LookIds(PIV.QidBody(r1, qid));
      assert false;
  }

  /** (L4 depth-k, ADDITIVE) the NESTED-fragment counterpart of
      `LookPathDomOnPathBreaks`. Identical alt/con/quant/capture descent; the
      `Re_lookaround` case is no longer vacuous (the body may hold looks), so it
      RECURSES into the body instead of `assert false`: `QuantIds`/`QidBody`
      descend transparently through a look node, and `LookPathDom` reduces to
      the body (the outer lid is `LookUnique`-distinct from any body lid). */
  lemma LookPathDomOnPathBreaksNested(r: R.regex, L: int, qc': seq<int>, lid: nat, qid: nat)
    requires NR.NestedFragmentRE(r) && LTB.LookUnique(r)
    requires lid in LTB.LookIds(r) && qid in PIV.QuantIds(r)
    requires lid in LTB.LookIds(PIV.QidBody(r, qid))
    requires AI.get_idx(qc', qid as int) > L
    ensures !LookPathDom(r, L, qc', lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if qid in PIV.QuantIds(r1) {
        QidBodyLookIdsSub(r1, qid);
        assert lid in LTB.LookIds(r1);
        LookPathDomOnPathBreaksNested(r1, L, qc', lid, qid);
      } else {
        QidBodyLookIdsSub(r2, qid);
        assert lid in LTB.LookIds(r2);
        assert lid !in LTB.LookIds(r1) by {
          if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); }
        }
        LookPathDomOnPathBreaksNested(r2, L, qc', lid, qid);
      }
    case Re_con(r1, r2) =>
      if qid in PIV.QuantIds(r1) {
        QidBodyLookIdsSub(r1, qid);
        assert lid in LTB.LookIds(r1);
        LookPathDomOnPathBreaksNested(r1, L, qc', lid, qid);
      } else {
        QidBodyLookIdsSub(r2, qid);
        assert lid in LTB.LookIds(r2);
        assert lid !in LTB.LookIds(r1) by {
          if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); }
        }
        LookPathDomOnPathBreaksNested(r2, L, qc', lid, qid);
      }
    case Re_quant(_, qid0, _, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid {
        assert AI.get_idx(qc', qid0) > L;     // the node's own clause fails
      } else {
        LookPathDomOnPathBreaksNested(r1, L, qc', lid, qid);
      }
    case Re_capture(_, r1) =>
      LookPathDomOnPathBreaksNested(r1, L, qc', lid, qid);
    case Re_lookaround(lid0, _, r1) =>
      // (L4) the body may hold looks: QuantIds/QidBody descend, so qid lives in
      // r1 and lid in LookIds(QidBody(r1,qid)) <= LookIds(r1). The outer lid0 is
      // LookUnique-distinct from every body lid, so LookPathDom reduces to r1.
      QidBodyLookIdsSub(r1, qid);
      assert lid in LTB.LookIds(r1);
      assert (lid0 as nat) != lid;                    // LookUnique: lid0 !in LookIds(r1)
      LookPathDomOnPathBreaksNested(r1, L, qc', lid, qid);
  }

  // ==========================================================================
  // (L4 depth-k, ADDITIVE) LOOK-CLOCK-AWARE path presence to a look node.
  //
  // The depth-1 `LookPathPresent(r, cc, qc, mx, lid)` records only the
  // CAPTURE/QUANT clocks on the descent to `lid` — it IGNORES ancestor look
  // clocks, because in the depth-1 fragment the path to a look never crosses a
  // look body. Under NESTING the path to an inner look `lid` DOES cross the
  // outer looks' nodes, and `PIV.PathPresentLk` (the predicate `GmOfLive`
  // membership reads) requires EACH of those ancestor look clocks be set and in
  // scope. `LookPathPresentLk` is `LookPathPresent` PLUS the ancestor-look-clock
  // clauses (exactly as `PathPresentLk` treats a look node) — the presence-to-
  // node primitive that composes with a body-side `PathPresentLk` into the full
  // `PathPresentLk(r, .., g)` under arbitrary positive nesting.
  // ==========================================================================
  ghost predicate LookPathPresentLk(r: R.regex, cc: seq<int>, lc: seq<int>, qc: seq<int>,
                                    mx: int, lid: nat)
    requires lid in LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) then LookPathPresentLk(r1, cc, lc, qc, mx, lid)
      else LookPathPresentLk(r2, cc, lc, qc, mx, lid)
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) then LookPathPresentLk(r1, cc, lc, qc, mx, lid)
      else LookPathPresentLk(r2, cc, lc, qc, mx, lid)
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      qv >= mx && LookPathPresentLk(r1, cc, lc, qc, qv, lid)
    case Re_capture(cid, r1) =>
      AI.get_idx(cc, CP.start_reg(cid)) >= 0 && AI.get_idx(cc, CP.start_reg(cid)) >= mx
      && LookPathPresentLk(r1, cc, lc, qc, mx, lid)
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid then true
      else AI.get_idx(lc, lid0) >= 0 && AI.get_idx(lc, lid0) >= mx
           && LookPathPresentLk(r1, cc, lc, qc, -1, lid)
  }

  /** (L4 depth-k) the NESTED counterpart of `LookPathCompose`. Same alt/con/
      quant/capture descent; the `Re_lookaround(lid0 != lid)` case is no longer
      vacuous (the body may nest looks), so it RECURSES into the body. The extra
      power over the depth-1 lemma is that the outer look node's OWN clock clause
      (which `PIV.PathPresentLk` demands) is now SUPPLIED by the look-clock-aware
      `LookPathPresentLk` premise — so the composition still lands the full
      `PIV.PathPresentLk(r, .., g)` at a DEEPLY-nested owner. */
  lemma LookPathComposeNested(r: R.regex, body: R.regex, cc: seq<int>, lc: seq<int>, qc: seq<int>,
                              mx: int, lid: nat, g: nat)
    requires NR.NestedFragmentRE(r) && PIV.CapUnique(r)
    requires lid in LTB.LookIds(r)
    requires body == LookBodyOfRE(r, lid)
    requires g in PIV.CapIds(body)
    requires LookPathPresentLk(r, cc, lc, qc, mx, lid)
    requires AI.get_idx(lc, lid as int) >= 0
    requires AI.get_idx(lc, lid as int) >= MxAtLidLk(r, qc, mx, lid)
    requires PIV.PathPresentLk(body, cc, lc, qc, -1, g)
    ensures g in PIV.CapIds(r)
    ensures PIV.PathPresentLk(r, cc, lc, qc, mx, g)
    ensures PIV.MxAtGidLk(r, cc, lc, qc, mx, g) == PIV.MxAtGidLk(body, cc, lc, qc, -1, g)
    decreases r
  {
    LookBodyCapsIn(r, lid);
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        LookBodyCapsIn(r1, lid);
        assert g in PIV.CapIds(r1);
        LookPathComposeNested(r1, body, cc, lc, qc, mx, lid, g);
      } else {
        LookBodyCapsIn(r2, lid);
        assert g in PIV.CapIds(r2);
        assert g !in PIV.CapIds(r1) by {
          if g in PIV.CapIds(r1) { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
        LookPathComposeNested(r2, body, cc, lc, qc, mx, lid, g);
      }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        LookBodyCapsIn(r1, lid);
        assert g in PIV.CapIds(r1);
        LookPathComposeNested(r1, body, cc, lc, qc, mx, lid, g);
      } else {
        LookBodyCapsIn(r2, lid);
        assert g in PIV.CapIds(r2);
        assert g !in PIV.CapIds(r1) by {
          if g in PIV.CapIds(r1) { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
        LookPathComposeNested(r2, body, cc, lc, qc, mx, lid, g);
      }
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      assert qv >= mx;                               // LookPathPresentLk
      LookPathComposeNested(r1, body, cc, lc, qc, qv, lid, g);
    case Re_capture(cid, r1) =>
      LookBodyCapsIn(r1, lid);
      assert g in PIV.CapIds(r1);
      assert cid >= 0 && (cid as nat) !in PIV.CapIds(r1);   // CapUnique
      assert (cid as nat) != g;
      assert AI.get_idx(cc, CP.start_reg(cid)) >= 0
          && AI.get_idx(cc, CP.start_reg(cid)) >= mx;       // LookPathPresentLk
      LookPathComposeNested(r1, body, cc, lc, qc, mx, lid, g);
    case Re_lookaround(lid0, la, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
        assert body == r1;
        assert MxAtLidLk(r, qc, mx, lid) == mx;
        assert AI.get_idx(lc, lid0) >= 0 && AI.get_idx(lc, lid0) >= mx;
      } else {
        // (L4) the outer look node: descend into the body, its lid0 clock
        // clause carried by the look-clock-aware premise.
        assert lid in LTB.LookIds(r1);
        assert body == LookBodyOfRE(r1, lid);
        assert AI.get_idx(lc, lid0) >= 0 && AI.get_idx(lc, lid0) >= mx;   // LookPathPresentLk
        assert LookPathPresentLk(r1, cc, lc, qc, -1, lid);
        assert MxAtLidLk(r, qc, mx, lid) == MxAtLidLk(r1, qc, -1, lid);
        LookBodyCapsIn(r1, lid);
        assert g in PIV.CapIds(r1);
        LookPathComposeNested(r1, body, cc, lc, qc, -1, lid, g);
      }
  }

  /** (L4 depth-k) the NESTED counterpart of `LookPathDecompose` (inverse of
      `LookPathComposeNested`): the full `PIV.PathPresentLk(r, .., g)` at a
      DEEPLY-nested inside-look `g` peels into the look-clock-aware path presence
      TO the owner (`LookPathPresentLk`, which now records the ancestor look
      clocks the outer path crosses), the owner's own clock clause, and the
      body-side presence. The `Re_lookaround(lid0 != lid)` case recurses. */
  lemma LookPathDecomposeNested(r: R.regex, body: R.regex, cc: seq<int>, lc: seq<int>, qc: seq<int>,
                                mx: int, lid: nat, g: nat)
    requires NR.NestedFragmentRE(r) && PIV.CapUnique(r)
    requires lid in LTB.LookIds(r)
    requires body == LookBodyOfRE(r, lid)
    requires g in PIV.CapIds(body)
    requires g in PIV.CapIds(r)
    requires PIV.PathPresentLk(r, cc, lc, qc, mx, g)
    ensures LookPathPresentLk(r, cc, lc, qc, mx, lid)
    ensures AI.get_idx(lc, lid as int) >= 0
    ensures AI.get_idx(lc, lid as int) >= MxAtLidLk(r, qc, mx, lid)
    ensures PIV.PathPresentLk(body, cc, lc, qc, -1, g)
    ensures PIV.MxAtGidLk(r, cc, lc, qc, mx, g) == PIV.MxAtGidLk(body, cc, lc, qc, -1, g)
    decreases r
  {
    LookBodyCapsIn(r, lid);
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        LookBodyCapsIn(r1, lid);
        assert g in PIV.CapIds(r1);
        LookPathDecomposeNested(r1, body, cc, lc, qc, mx, lid, g);
      } else {
        LookBodyCapsIn(r2, lid);
        assert g in PIV.CapIds(r2);
        assert g !in PIV.CapIds(r1) by {
          if g in PIV.CapIds(r1) { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
        LookPathDecomposeNested(r2, body, cc, lc, qc, mx, lid, g);
      }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        LookBodyCapsIn(r1, lid);
        assert g in PIV.CapIds(r1);
        LookPathDecomposeNested(r1, body, cc, lc, qc, mx, lid, g);
      } else {
        LookBodyCapsIn(r2, lid);
        assert g in PIV.CapIds(r2);
        assert g !in PIV.CapIds(r1) by {
          if g in PIV.CapIds(r1) { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
        LookPathDecomposeNested(r2, body, cc, lc, qc, mx, lid, g);
      }
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      assert qv >= mx;                               // PathPresentLk
      LookPathDecomposeNested(r1, body, cc, lc, qc, qv, lid, g);
    case Re_capture(cid, r1) =>
      LookBodyCapsIn(r1, lid);
      assert g in PIV.CapIds(r1);
      assert cid >= 0 && (cid as nat) !in PIV.CapIds(r1);   // CapUnique
      assert (cid as nat) != g;
      LookPathDecomposeNested(r1, body, cc, lc, qc, mx, lid, g);
    case Re_lookaround(lid0, la, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
        assert body == r1;
        assert MxAtLidLk(r, qc, mx, lid) == mx;
        // PathPresentLk's look clause supplies the lc facts and the body walk
      } else {
        // (L4) descend into the body; the outer look clock clause is recorded
        // in the produced LookPathPresentLk.
        assert lid in LTB.LookIds(r1);
        assert body == LookBodyOfRE(r1, lid);
        LookBodyCapsIn(r1, lid);
        assert g in PIV.CapIds(r1);
        assert AI.get_idx(lc, lid0) >= 0 && AI.get_idx(lc, lid0) >= mx;   // PathPresentLk
        LookPathDecomposeNested(r1, body, cc, lc, qc, -1, lid, g);
        assert MxAtLidLk(r, qc, mx, lid) == MxAtLidLk(r1, qc, -1, lid);
      }
  }

  /** (L4 depth-k) `LookPathPresentLk`/`MxAtLidLk` read the banks only at `r`'s
      OWN capture-start slots, quant slots and look slots — congruence under
      agreement there. The look-clock-aware analog of the depth-1
      `LookPathPresentAgree`, but keyed on ALL of `CapIds`/`QuantIds`/`LookIds`
      (not just the outside-look ones): under nesting the descent to a look node
      genuinely crosses inside-look captures/quants and ancestor look clocks. */
  lemma LookPathPresentLkAgree(r: R.regex, cc1: seq<int>, lc1: seq<int>, qc1: seq<int>,
                               cc2: seq<int>, lc2: seq<int>, qc2: seq<int>, mx: int, lid: nat)
    requires lid in LTB.LookIds(r)
    requires forall c: nat :: c in PIV.CapIds(r) ==>
      AI.get_idx(cc1, CP.start_reg(c as int)) == AI.get_idx(cc2, CP.start_reg(c as int))
    requires forall q: nat :: q in PIV.QuantIds(r) ==>
      AI.get_idx(qc1, q as int) == AI.get_idx(qc2, q as int)
    requires forall l: nat :: l in LTB.LookIds(r) ==>
      AI.get_idx(lc1, l as int) == AI.get_idx(lc2, l as int)
    ensures LookPathPresentLk(r, cc1, lc1, qc1, mx, lid) == LookPathPresentLk(r, cc2, lc2, qc2, mx, lid)
    ensures MxAtLidLk(r, qc1, mx, lid) == MxAtLidLk(r, qc2, mx, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      assert PIV.CapIds(r1) <= PIV.CapIds(r) && PIV.CapIds(r2) <= PIV.CapIds(r);
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r) && PIV.QuantIds(r2) <= PIV.QuantIds(r);
      assert LTB.LookIds(r1) <= LTB.LookIds(r) && LTB.LookIds(r2) <= LTB.LookIds(r);
      if lid in LTB.LookIds(r1) { LookPathPresentLkAgree(r1, cc1, lc1, qc1, cc2, lc2, qc2, mx, lid); }
      else { LookPathPresentLkAgree(r2, cc1, lc1, qc1, cc2, lc2, qc2, mx, lid); }
    case Re_con(r1, r2) =>
      assert PIV.CapIds(r1) <= PIV.CapIds(r) && PIV.CapIds(r2) <= PIV.CapIds(r);
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r) && PIV.QuantIds(r2) <= PIV.QuantIds(r);
      assert LTB.LookIds(r1) <= LTB.LookIds(r) && LTB.LookIds(r2) <= LTB.LookIds(r);
      if lid in LTB.LookIds(r1) { LookPathPresentLkAgree(r1, cc1, lc1, qc1, cc2, lc2, qc2, mx, lid); }
      else { LookPathPresentLkAgree(r2, cc1, lc1, qc1, cc2, lc2, qc2, mx, lid); }
    case Re_quant(_, qid, _, r1) =>
      assert PIV.CapIds(r1) <= PIV.CapIds(r);
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r);
      assert LTB.LookIds(r1) <= LTB.LookIds(r);
      assert AI.get_idx(qc1, qid) == AI.get_idx(qc2, qid) by {
        if qid >= 0 { assert (qid as nat) in PIV.QuantIds(r); }
      }
      LookPathPresentLkAgree(r1, cc1, lc1, qc1, cc2, lc2, qc2, AI.get_idx(qc1, qid), lid);
    case Re_capture(cid, r1) =>
      assert PIV.CapIds(r1) <= PIV.CapIds(r);
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r);
      assert LTB.LookIds(r1) <= LTB.LookIds(r);
      assert AI.get_idx(cc1, CP.start_reg(cid)) == AI.get_idx(cc2, CP.start_reg(cid)) by {
        if cid >= 0 { assert (cid as nat) in PIV.CapIds(r); }
        else { assert CP.start_reg(cid) < 0; }
      }
      LookPathPresentLkAgree(r1, cc1, lc1, qc1, cc2, lc2, qc2, mx, lid);
    case Re_lookaround(lid0, _, r1) =>
      assert PIV.CapIds(r1) == PIV.CapIds(r);
      assert PIV.QuantIds(r1) == PIV.QuantIds(r);
      assert LTB.LookIds(r1) <= LTB.LookIds(r);
      assert AI.get_idx(lc1, lid0) == AI.get_idx(lc2, lid0) by {
        if lid0 >= 0 { assert (lid0 as nat) in LTB.LookIds(r); }
      }
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        assert lid in LTB.LookIds(r1);
        LookPathPresentLkAgree(r1, cc1, lc1, qc1, cc2, lc2, qc2, -1, lid);
      }
  }

  /** (L4 depth-k) `LookPathPresentLk` is STRICTLY STRONGER than `LookPathPresent`:
      the two predicates agree on every case except `Re_lookaround(lid0 != lid)`,
      where `LookPathPresentLk` ADDS the crossed look's own clock clause
      (`lc[lid0] >= 0 && >= mx`) on top of the plain body recursion. So the
      look-clock-aware presence always entails the plain one — a trivial forgetful
      structural induction. (Used to feed the look-clock-UNAWARE `LookPathDomIntroTop`
      from the `LookPathDecomposeNested` output.) */
  lemma LookPathPresentLkImpliesPresent(r: R.regex, cc: seq<int>, lc: seq<int>, qc: seq<int>,
                                        mx: int, lid: nat)
    requires lid in LTB.LookIds(r)
    requires LookPathPresentLk(r, cc, lc, qc, mx, lid)
    ensures LookPathPresent(r, cc, qc, mx, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookPathPresentLkImpliesPresent(r1, cc, lc, qc, mx, lid); }
      else { LookPathPresentLkImpliesPresent(r2, cc, lc, qc, mx, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookPathPresentLkImpliesPresent(r1, cc, lc, qc, mx, lid); }
      else { LookPathPresentLkImpliesPresent(r2, cc, lc, qc, mx, lid); }
    case Re_quant(_, qid, _, r1) =>
      LookPathPresentLkImpliesPresent(r1, cc, lc, qc, AI.get_idx(qc, qid), lid);
    case Re_capture(_, r1) =>
      LookPathPresentLkImpliesPresent(r1, cc, lc, qc, mx, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        LookPathPresentLkImpliesPresent(r1, cc, lc, qc, -1, lid);
      }
  }

  /** (L4 depth-k — THE REVERSE-RECON CONNECTIVE, res-bank half) The KEY EXTRACTION:
      from FULL recon-bank liveness of an inside-look capture `g2` (`g2 in
      GmOfLive(re, res0, res1, res2)`), the top-ancestor look `A0`'s look clock
      DOMINATES its whole path — `LookPathDom(re, res1.a_clk[A0], res2.a_clk, A0)`.

      ROUTE: `GmOfLivePresenceExtractLkNested` turns liveness into look-aware path
      presence `PathPresentLk(re, res0.a_clk, res1.a_clk, res2.a_clk, -1, g2)`. Since
      `g2` sits in `A0`'s body and `A0` is a TOP look, `LookPathDecomposeNested`
      peels off the path-to-`A0` (`LookPathPresentLk`) together with `A0`'s own clock
      clause `res1.a_clk[A0] >= 0 && >= MxAtLidLk(re, res2.a_clk, -1, A0)`. Forgetting
      the crossed-look clocks (`LookPathPresentLkImpliesPresent`) yields the plain
      `LookPathPresent`, and `LookPathDomIntroTop` assembles the dominance from path
      presence + the look stamp beating the node threshold. Under FULL liveness this
      is a clean extraction — the escaped-matched-look failure mode of `res0`-live-
      alone never arises. */
  lemma LookPathDomFromLivenessRes(re: R.regex, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
                                   g2: nat, A0: nat)
    requires NR.NestedFragmentRE(re) && PIV.CapUnique(re) && LTB.LookUnique(re)
    requires g2 in PIV.CapIdsInLooks(re)
    requires forall c: nat :: c in PIV.CapIds(re) && AI.get_idx(res0.a_clk, CP.start_reg(c)) < 0
                             ==> AI.get_idx(res0.a_cp, CP.start_reg(c)) < 0
    requires g2 in PIV.GmOfLive(re, res0, res1, res2)
    requires A0 in TopLookIds(re) && A0 in LTB.LookIds(re)
    requires g2 in PIV.CapIds(LookBodyOfRE(re, A0))
    ensures LookPathDom(re, AI.get_idx(res1.a_clk, A0 as int), res2.a_clk, A0)
  {
    PIV.CapIdsSplit(re);                              // CapIdsInLooks(re) <= CapIds(re)
    assert g2 in PIV.CapIds(re);
    var cc := res0.a_clk;
    var lc := AReg.as_arrays(res1).1;                 // == res1.a_clk definitionally
    var qc := AReg.as_arrays(res2).1;                 // == res2.a_clk definitionally
    var body := LookBodyOfRE(re, A0);
    // (1) FULL liveness -> look-aware path presence at g2.
    GmOfLivePresenceExtractLkNested(re, res0, res1, res2, g2);
    assert PIV.PathPresentLk(re, cc, lc, qc, -1, g2);
    // (2) peel off the path-to-A0 + A0's own look-clock clause.
    LookPathDecomposeNested(re, body, cc, lc, qc, -1, A0, g2);
    assert LookPathPresentLk(re, cc, lc, qc, -1, A0);
    assert AI.get_idx(lc, A0 as int) >= 0;
    assert AI.get_idx(lc, A0 as int) >= MxAtLidLk(re, qc, -1, A0);
    // (3) forget crossed-look clocks -> plain path presence.
    LookPathPresentLkImpliesPresent(re, cc, lc, qc, -1, A0);
    assert LookPathPresent(re, cc, qc, -1, A0);
    // (4) assemble dominance from presence + the stamp beating the threshold.
    LookPathDomIntroTop(re, cc, qc, -1, A0, AI.get_idx(lc, A0 as int));
    assert LookPathDom(re, AI.get_idx(lc, A0 as int), qc, A0);
  }

  /** (L4 depth-k) TOP-look qc-congruence for `LookPathDom`: for a TOP look `lid`
      the path never enters a look body, so `LookPathDom` reads `qc` only at the
      OUTSIDE-look quants it crosses. Hence agreement on `QuantIdsOutsideLooks(r)`
      alone suffices — the exact frame the endpoint's recon quant frame supplies
      (`res2.a_clk == thread.quant_regs.a_clk` on `QuantIdsOutsideLooks(re)`).
      Same TopLookIds alt/con routing as `MxAtLidGeMxTop`. */
  lemma LookPathDomQcAgreeTop(r: R.regex, L: int, qc: seq<int>, qc': seq<int>, lid: nat)
    requires NR.NestedFragmentRE(r) && LTB.LookUnique(r)
    requires lid in LTB.LookIds(r)
    requires lid in TopLookIds(r)
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(r) ==>
      AI.get_idx(qc, q as int) == AI.get_idx(qc', q as int)
    ensures LookPathDom(r, L, qc, lid) == LookPathDom(r, L, qc', lid)
    decreases r
  {
    TopLookIdsIn(r);
    match r
    case Re_alt(r1, r2) =>
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r)
          && PIV.QuantIdsOutsideLooks(r2) <= PIV.QuantIdsOutsideLooks(r);
      if lid in LTB.LookIds(r1) {
        assert lid in TopLookIds(r1) by {
          if lid !in TopLookIds(r1) {
            assert lid in TopLookIds(r2); TopLookIdsIn(r2);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        LookPathDomQcAgreeTop(r1, L, qc, qc', lid);
      } else {
        assert lid in LTB.LookIds(r2);
        assert lid in TopLookIds(r2) by {
          if lid !in TopLookIds(r2) {
            assert lid in TopLookIds(r1); TopLookIdsIn(r1);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        LookPathDomQcAgreeTop(r2, L, qc, qc', lid);
      }
    case Re_con(r1, r2) =>
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r)
          && PIV.QuantIdsOutsideLooks(r2) <= PIV.QuantIdsOutsideLooks(r);
      if lid in LTB.LookIds(r1) {
        assert lid in TopLookIds(r1) by {
          if lid !in TopLookIds(r1) {
            assert lid in TopLookIds(r2); TopLookIdsIn(r2);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        LookPathDomQcAgreeTop(r1, L, qc, qc', lid);
      } else {
        assert lid in LTB.LookIds(r2);
        assert lid in TopLookIds(r2) by {
          if lid !in TopLookIds(r2) {
            assert lid in TopLookIds(r1); TopLookIdsIn(r1);
            assert lid in LTB.LookIds(r1) * LTB.LookIds(r2);
          }
        }
        LookPathDomQcAgreeTop(r2, L, qc, qc', lid);
      }
    case Re_quant(_, qid, _, r1) =>
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r);
      assert AI.get_idx(qc, qid) == AI.get_idx(qc', qid) by {
        if qid >= 0 { assert (qid as nat) in PIV.QuantIdsOutsideLooks(r); }
      }
      LookPathDomQcAgreeTop(r1, L, qc, qc', lid);
    case Re_capture(_, r1) =>
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r);
      LookPathDomQcAgreeTop(r1, L, qc, qc', lid);
    case Re_lookaround(lid0, _, r1) =>
      assert lid0 >= 0 && (lid0 as nat) == lid;
  }

  /** (L4 depth-k — THE REVERSE-RECON CONNECTIVE, thread-bank half) The res-bank
      connective transferred onto the WINNING THREAD's banks. Given the res->thread
      transfer facts at the TOP look `A0` — the look clock unchanged
      (`res1.a_clk[A0] == thread.look_regs.a_clk[A0]`, from `FLookLoopTopLookClk-
      StableFull`) and the recon quant frame outside looks (`res2.a_clk ==
      thread.quant_regs.a_clk` on `QuantIdsOutsideLooks(re)`, from the endpoint's
      `FLookLoopQuantFrame`) — the dominance carries over verbatim: the L stamp is
      the same look clock, and `LookPathDom` at a top look reads `qc` only on
      outside-look path quants (`LookPathDomQcAgreeTop`). This is the exact
      `LookPathDom`-on-thread the DIRECT descent package owes. */
  lemma LookPathDomFromLivenessThread(re: R.regex, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
                                      thread: AI.Thread, g2: nat, A0: nat)
    requires NR.NestedFragmentRE(re) && PIV.CapUnique(re) && LTB.LookUnique(re)
    requires g2 in PIV.CapIdsInLooks(re)
    requires forall c: nat :: c in PIV.CapIds(re) && AI.get_idx(res0.a_clk, CP.start_reg(c)) < 0
                             ==> AI.get_idx(res0.a_cp, CP.start_reg(c)) < 0
    requires g2 in PIV.GmOfLive(re, res0, res1, res2)
    requires A0 in TopLookIds(re) && A0 in LTB.LookIds(re)
    requires g2 in PIV.CapIds(LookBodyOfRE(re, A0))
    // res -> thread transfer facts at the TOP look A0.
    requires AI.get_idx(res1.a_clk, A0 as int) == AI.get_idx(thread.look_regs.a_clk, A0 as int)
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
      AI.get_idx(res2.a_clk, q as int) == AI.get_idx(thread.quant_regs.a_clk, q as int)
    ensures LookPathDom(re, AI.get_idx(thread.look_regs.a_clk, A0 as int), thread.quant_regs.a_clk, A0)
  {
    LookPathDomFromLivenessRes(re, res0, res1, res2, g2, A0);
    assert LookPathDom(re, AI.get_idx(res1.a_clk, A0 as int), res2.a_clk, A0);
    // look clock unchanged: rewrite the L stamp.
    assert AI.get_idx(res1.a_clk, A0 as int) == AI.get_idx(thread.look_regs.a_clk, A0 as int);
    // quant frame outside looks: LookPathDom at a top look reads only those.
    LookPathDomQcAgreeTop(re, AI.get_idx(thread.look_regs.a_clk, A0 as int),
                          res2.a_clk, thread.quant_regs.a_clk, A0);
  }

  /** (L4 depth-k) the NESTED counterpart of `PIV.FilterPresenceExtractLk`: a
      surviving start register under `filter_capture` yields the look-clock-aware
      `PIV.PathPresentLk` — under arbitrary positive nesting. The depth-1 lemma
      re-derives `LookBehindFragmentRE(body)` at each look node
      (`PlusIsLookBehindFragmentRE`); here the recursion is directly under
      `NestedFragmentRE`, and the outside-own frame steps route through the
      nested `PIV.FilterCaptureOutsideNested`. */
  lemma FilterPresenceExtractLkNested(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>,
                                      mx: int, gid: nat)
    requires NR.NestedFragmentRE(r)
    requires PIV.CapUnique(r)
    requires gid in PIV.CapIds(r)
    requires forall c: nat :: c in PIV.CapIds(r) && AI.get_idx(cc, CP.start_reg(c)) < 0
                             ==> AI.get_idx(cr, CP.start_reg(c)) < 0
    requires AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, mx), CP.start_reg(gid)) >= 0
    ensures PIV.PathPresentLk(r, cc, lc, qc, mx, gid)
    ensures AI.get_idx(cc, CP.start_reg(gid)) >= 0
    ensures AI.get_idx(cc, CP.start_reg(gid)) >= PIV.MxAtGidLk(r, cc, lc, qc, mx, gid)
    ensures AI.get_idx(cr, CP.start_reg(gid)) >= 0
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_lookaround(lid, la, r1) =>
      var lv := AI.get_idx(lc, lid);
      if lv < 0 || lv < mx {
        PIV.FilterAllClearsStart(r1, cr, gid);
        assert false;
      } else {
        FilterPresenceExtractLkNested(r1, cr, cc, lc, qc, -1, gid);
      }
    case Re_alt(r1, r2) =>
      var c1 := AI.filter_capture(r1, cr, cc, lc, qc, mx);
      if gid in PIV.CapIds(r1) {
        assert gid !in PIV.CapIds(r2) by { if gid in PIV.CapIds(r2) { assert gid in PIV.CapIds(r1) * PIV.CapIds(r2); } }
        PIV.FilterCaptureOutsideNested(r2, c1, cc, lc, qc, mx, gid);
        FilterPresenceExtractLkNested(r1, cr, cc, lc, qc, mx, gid);
      } else {
        assert gid in PIV.CapIds(r2) && gid !in PIV.CapIds(r1);
        forall c: nat | c in PIV.CapIds(r2) && AI.get_idx(cc, CP.start_reg(c)) < 0
          ensures AI.get_idx(c1, CP.start_reg(c)) < 0
        {
          assert c !in PIV.CapIds(r1) by { if c in PIV.CapIds(r1) { assert c in PIV.CapIds(r1) * PIV.CapIds(r2); } }
          PIV.FilterCaptureOutsideNested(r1, cr, cc, lc, qc, mx, c);
        }
        FilterPresenceExtractLkNested(r2, c1, cc, lc, qc, mx, gid);
        PIV.FilterCaptureOutsideNested(r1, cr, cc, lc, qc, mx, gid);
      }
    case Re_con(r1, r2) =>
      var c1 := AI.filter_capture(r1, cr, cc, lc, qc, mx);
      if gid in PIV.CapIds(r1) {
        assert gid !in PIV.CapIds(r2) by { if gid in PIV.CapIds(r2) { assert gid in PIV.CapIds(r1) * PIV.CapIds(r2); } }
        PIV.FilterCaptureOutsideNested(r2, c1, cc, lc, qc, mx, gid);
        FilterPresenceExtractLkNested(r1, cr, cc, lc, qc, mx, gid);
      } else {
        assert gid in PIV.CapIds(r2) && gid !in PIV.CapIds(r1);
        forall c: nat | c in PIV.CapIds(r2) && AI.get_idx(cc, CP.start_reg(c)) < 0
          ensures AI.get_idx(c1, CP.start_reg(c)) < 0
        {
          assert c !in PIV.CapIds(r1) by { if c in PIV.CapIds(r1) { assert c in PIV.CapIds(r1) * PIV.CapIds(r2); } }
          PIV.FilterCaptureOutsideNested(r1, cr, cc, lc, qc, mx, c);
        }
        FilterPresenceExtractLkNested(r2, c1, cc, lc, qc, mx, gid);
        PIV.FilterCaptureOutsideNested(r1, cr, cc, lc, qc, mx, gid);
      }
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < mx {
        PIV.FilterAllClearsStart(r1, cr, gid);
        assert false;
      } else {
        FilterPresenceExtractLkNested(r1, cr, cc, lc, qc, qv, gid);
      }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if cid >= 0 && (cid as nat) == gid {
        assert gid !in PIV.CapIds(r1);                        // CapUnique
        if start < 0 {
          PIV.FilterAllOutside(r1, cr, gid);
          assert AI.get_idx(cr, CP.start_reg(gid)) < 0;
          assert false;
        } else if start < mx {
          var cr2 := AI.set_idx(cr, CP.start_reg(cid), -1);
          PIV.FilterAllOutside(r1, cr2, gid);
          assert AI.get_idx(cr2, CP.start_reg(gid)) <= -1;
          assert false;
        } else {
          PIV.FilterCaptureOutsideNested(r1, cr, cc, lc, qc, mx, gid);
          assert PIV.MxAtGidLk(r, cc, lc, qc, mx, gid) == mx;
        }
      } else {
        assert gid in PIV.CapIds(r1);
        if start < 0 {
          PIV.FilterAllClearsStart(r1, cr, gid);
          assert false;
        } else if start < mx {
          var cr2 := AI.set_idx(cr, CP.start_reg(cid), -1);
          PIV.FilterAllClearsStart(r1, cr2, gid);
          assert false;
        } else {
          forall c: nat | c in PIV.CapIds(r1) && AI.get_idx(cc, CP.start_reg(c)) < 0
            ensures AI.get_idx(cr, CP.start_reg(c)) < 0 {}
          FilterPresenceExtractLkNested(r1, cr, cc, lc, qc, mx, gid);
        }
      }
  }

  /** (L4 depth-k) gm-level wrapper — the NESTED `PIV.GmOfLivePresenceExtractLk`:
      any group present in the live denotation (inside-look ones included, to any
      depth) is look-aware path-present with a fresh, set start clock. */
  lemma GmOfLivePresenceExtractLkNested(ast: R.regex, caps: AReg.Regs, look: AReg.Regs,
                                        quant: AReg.Regs, gid: nat)
    requires NR.NestedFragmentRE(ast)
    requires PIV.CapUnique(ast)
    requires gid in PIV.CapIds(ast)
    requires forall c: nat :: c in PIV.CapIds(ast) && AI.get_idx(caps.a_clk, CP.start_reg(c)) < 0
                             ==> AI.get_idx(caps.a_cp, CP.start_reg(c)) < 0
    requires gid in PIV.GmOfLive(ast, caps, look, quant)
    ensures PIV.PathPresentLk(ast, caps.a_clk, AReg.as_arrays(look).1, AReg.as_arrays(quant).1, -1, gid)
    ensures AI.get_idx(caps.a_clk, CP.start_reg(gid)) >= 0
    ensures AI.get_idx(caps.a_clk, CP.start_reg(gid))
              >= PIV.MxAtGidLk(ast, caps.a_clk, AReg.as_arrays(look).1, AReg.as_arrays(quant).1, -1, gid)
    ensures AI.get_idx(caps.a_cp, CP.start_reg(gid)) >= 0
  {
    var (cr, cc) := AReg.as_arrays(caps);
    var (_, lc) := AReg.as_arrays(look);
    var (_, qc) := AReg.as_arrays(quant);
    var f := AI.filter_reset(ast, caps, look, quant, -1);
    assert f == AI.filter_capture(ast, cr, cc, lc, qc, -1);
    assert AI.get_idx(f, CP.start_reg(gid)) >= 0;
    FilterPresenceExtractLkNested(ast, cr, cc, lc, qc, -1, gid);
  }

  /** (L4 depth-k) the NESTED `PIV.GmOfLiveKeepsPresentLk` — the FORWARD closing
      step: look-aware path presence + a set/in-scope start clock puts `gid` into
      the live denotation with the raw `LiveRange` value. The depth-1 lemma's
      proof uses no fragment fact at all (`FilterKeepsPresentLk`/
      `FilterCaptureKeepsOdd` need only `CapUnique`), so this is a pure
      fragment-relabel that re-exposes it under `NestedFragmentRE`. */
  lemma GmOfLiveKeepsPresentLkNested(re: R.regex, cap: AReg.Regs, look: AReg.Regs,
                                     quant: AReg.Regs, gid: nat)
    requires NR.NestedFragmentRE(re) && PIV.CapUnique(re)
    requires gid in PIV.CapIds(re)
    requires PIV.PathPresentLk(re, AReg.as_arrays(cap).1, AReg.as_arrays(look).1,
                               AReg.as_arrays(quant).1, -1, gid)
    requires AI.get_idx(AReg.as_arrays(cap).1, CP.start_reg(gid)) >= 0
    requires AI.get_idx(AReg.as_arrays(cap).0, CP.start_reg(gid)) >= 0   // value set
    requires AI.get_idx(AReg.as_arrays(cap).1, CP.start_reg(gid))
               >= PIV.MxAtGidLk(re, AReg.as_arrays(cap).1, AReg.as_arrays(look).1,
                                AReg.as_arrays(quant).1, -1, gid)
    ensures gid in PIV.GmOfLive(re, cap, look, quant)
    ensures PIV.GmOfLive(re, cap, look, quant)[gid]
              == PIV.LiveRange(AReg.as_arrays(cap).0, AReg.as_arrays(cap).1, gid)
  {
    var cr := AReg.as_arrays(cap).0;  var cc := AReg.as_arrays(cap).1;
    var lc := AReg.as_arrays(look).1; var qc := AReg.as_arrays(quant).1;
    var f := AI.filter_reset(re, cap, look, quant, -1);
    assert f == AI.filter_capture(re, cr, cc, lc, qc, -1);
    PIV.FilterKeepsPresentLk(re, cr, cc, lc, qc, -1, gid);
    PIV.FilterCaptureKeepsOdd(re, cr, cc, lc, qc, -1, CP.end_reg(gid));
    assert AI.get_idx(f, CP.start_reg(gid)) == AI.get_idx(cr, CP.start_reg(gid));
    assert AI.get_idx(f, CP.end_reg(gid)) == AI.get_idx(cr, CP.end_reg(gid));
    assert AI.get_idx(f, CP.start_reg(gid)) >= 0;
    assert PIV.LiveRange(f, cc, gid) == PIV.LiveRange(cr, cc, gid);
  }

  /** `QidBody`'s captures are among `r`'s (a subtree). */
  lemma QidBodyCapIdsSub(r: R.regex, qid: nat)
    requires qid in PIV.QuantIds(r)
    ensures PIV.CapIds(PIV.QidBody(r, qid)) <= PIV.CapIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if qid in PIV.QuantIds(r1) { QidBodyCapIdsSub(r1, qid); } else { QidBodyCapIdsSub(r2, qid); }
    case Re_con(r1, r2) =>
      if qid in PIV.QuantIds(r1) { QidBodyCapIdsSub(r1, qid); } else { QidBodyCapIdsSub(r2, qid); }
    case Re_quant(_, qid0, _, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid {} else { QidBodyCapIdsSub(r1, qid); }
    case Re_capture(_, r1) => QidBodyCapIdsSub(r1, qid);
    case Re_lookaround(_, _, r1) => QidBodyCapIdsSub(r1, qid);
  }

  /** An OUTSIDE-look quant whose body does NOT contain look `lid` owns a
      reset scope DISJOINT from `lid`'s captures — so its `Reset` never touches
      them (the converse carrier's off-path survival). */
  lemma LookBodyQidBodyDisjoint(r: R.regex, qid: nat, lid: nat)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r)
    requires qid in PIV.QuantIds(r) && qid in PIV.QuantIdsOutsideLooks(r)
    requires lid in LTB.LookIds(r)
    requires lid !in LTB.LookIds(PIV.QidBody(r, qid))
    ensures PIV.CapIds(LookBodyOfRE(r, lid)) * PIV.CapIds(PIV.QidBody(r, qid)) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if qid in PIV.QuantIds(r1) && lid in LTB.LookIds(r1) {
        assert qid in PIV.QuantIdsOutsideLooks(r1) by {
          assert qid !in PIV.QuantIds(r2) by {
            if qid in PIV.QuantIds(r2) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
          }
          PIV.QuantIdsSplit(r2);
          assert qid !in PIV.QuantIdsOutsideLooks(r2);
        }
        LookBodyQidBodyDisjoint(r1, qid, lid);
      } else if qid !in PIV.QuantIds(r1) && lid !in LTB.LookIds(r1) {
        assert qid in PIV.QuantIds(r2) && lid in LTB.LookIds(r2);
        assert qid in PIV.QuantIdsOutsideLooks(r2) by {
          PIV.QuantIdsSplit(r1);
          assert qid !in PIV.QuantIdsOutsideLooks(r1);
        }
        LookBodyQidBodyDisjoint(r2, qid, lid);
      } else {
        // different branches: both bodies live in disjoint capture spaces
        if qid in PIV.QuantIds(r1) {
          assert lid in LTB.LookIds(r2);
          QidBodyCapIdsSub(r1, qid); LookBodyCapsIn(r2, lid);
          forall g: nat | g in PIV.CapIds(LookBodyOfRE(r, lid)) * PIV.CapIds(PIV.QidBody(r, qid))
            ensures false
          { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); }
        } else {
          assert qid in PIV.QuantIds(r2) && lid in LTB.LookIds(r1);
          QidBodyCapIdsSub(r2, qid); LookBodyCapsIn(r1, lid);
          forall g: nat | g in PIV.CapIds(LookBodyOfRE(r, lid)) * PIV.CapIds(PIV.QidBody(r, qid))
            ensures false
          { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
      }
    case Re_con(r1, r2) =>
      if qid in PIV.QuantIds(r1) && lid in LTB.LookIds(r1) {
        assert qid in PIV.QuantIdsOutsideLooks(r1) by {
          assert qid !in PIV.QuantIds(r2) by {
            if qid in PIV.QuantIds(r2) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
          }
          PIV.QuantIdsSplit(r2);
          assert qid !in PIV.QuantIdsOutsideLooks(r2);
        }
        LookBodyQidBodyDisjoint(r1, qid, lid);
      } else if qid !in PIV.QuantIds(r1) && lid !in LTB.LookIds(r1) {
        assert qid in PIV.QuantIds(r2) && lid in LTB.LookIds(r2);
        assert qid in PIV.QuantIdsOutsideLooks(r2) by {
          PIV.QuantIdsSplit(r1);
          assert qid !in PIV.QuantIdsOutsideLooks(r1);
        }
        LookBodyQidBodyDisjoint(r2, qid, lid);
      } else {
        if qid in PIV.QuantIds(r1) {
          assert lid in LTB.LookIds(r2);
          QidBodyCapIdsSub(r1, qid); LookBodyCapsIn(r2, lid);
          forall g: nat | g in PIV.CapIds(LookBodyOfRE(r, lid)) * PIV.CapIds(PIV.QidBody(r, qid))
            ensures false
          { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); }
        } else {
          assert qid in PIV.QuantIds(r2) && lid in LTB.LookIds(r1);
          QidBodyCapIdsSub(r2, qid); LookBodyCapsIn(r1, lid);
          forall g: nat | g in PIV.CapIds(LookBodyOfRE(r, lid)) * PIV.CapIds(PIV.QidBody(r, qid))
            ensures false
          { assert g in PIV.CapIds(r1) * PIV.CapIds(r2); }
        }
      }
    case Re_quant(_, qid0, _, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid {
        // qid's body is r1 and every look of the node is in r1 — lid included:
        // contradicts the off-path hypothesis.
        assert PIV.QidBody(r, qid) == r1;
        assert lid in LTB.LookIds(r1);
        assert false;
      } else {
        LookBodyQidBodyDisjoint(r1, qid, lid);
      }
    case Re_capture(_, r1) =>
      LookBodyQidBodyDisjoint(r1, qid, lid);
    case Re_lookaround(lid0, _, r1) =>
      // an outside-look quant cannot sit below a look node
      assert PIV.QuantIdsOutsideLooks(r) == {};
      assert false;
  }

  /** Every inside-look capture has a structural OWNER lid. */
  lemma CapIdsInLooksHasOwner(r: R.regex, g: nat)
    requires LTB.LookUnique(r)
    requires g in PIV.CapIdsInLooks(r)
    ensures exists lid: nat :: lid in LTB.LookIds(r) && g in PIV.CapIds(LookBodyOfRE(r, lid))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if g in PIV.CapIdsInLooks(r1) {
        CapIdsInLooksHasOwner(r1, g);
        var lid: nat :| lid in LTB.LookIds(r1) && g in PIV.CapIds(LookBodyOfRE(r1, lid));
        assert LookBodyOfRE(r, lid) == LookBodyOfRE(r1, lid);
      } else {
        CapIdsInLooksHasOwner(r2, g);
        var lid: nat :| lid in LTB.LookIds(r2) && g in PIV.CapIds(LookBodyOfRE(r2, lid));
        assert lid !in LTB.LookIds(r1) by {
          if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); }
        }
        assert LookBodyOfRE(r, lid) == LookBodyOfRE(r2, lid);
      }
    case Re_con(r1, r2) =>
      if g in PIV.CapIdsInLooks(r1) {
        CapIdsInLooksHasOwner(r1, g);
        var lid: nat :| lid in LTB.LookIds(r1) && g in PIV.CapIds(LookBodyOfRE(r1, lid));
        assert LookBodyOfRE(r, lid) == LookBodyOfRE(r1, lid);
      } else {
        CapIdsInLooksHasOwner(r2, g);
        var lid: nat :| lid in LTB.LookIds(r2) && g in PIV.CapIds(LookBodyOfRE(r2, lid));
        assert lid !in LTB.LookIds(r1) by {
          if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); }
        }
        assert LookBodyOfRE(r, lid) == LookBodyOfRE(r2, lid);
      }
    case Re_quant(_, _, _, r1) =>
      CapIdsInLooksHasOwner(r1, g);
      var lid: nat :| lid in LTB.LookIds(r1) && g in PIV.CapIds(LookBodyOfRE(r1, lid));
      assert LookBodyOfRE(r, lid) == LookBodyOfRE(r1, lid);
    case Re_capture(_, r1) =>
      CapIdsInLooksHasOwner(r1, g);
      var lid: nat :| lid in LTB.LookIds(r1) && g in PIV.CapIds(LookBodyOfRE(r1, lid));
      assert LookBodyOfRE(r, lid) == LookBodyOfRE(r1, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 {
        assert (lid0 as nat) in LTB.LookIds(r);
        assert LookBodyOfRE(r, lid0 as nat) == r1;
        assert g in PIV.CapIds(r1);
      } else {
        assert false;                     // LookUnique forces lid0 >= 0
      }
  }

  /** GATE-CROSS ESTABLISHMENT: at look `lid`'s `CheckOracle` pc, the thread's
      positional invariant (`NestTopRE`, `pc < endl`) plus a FRESH look stamp
      that beats every stored quant clock yield the full carrier fact for
      `lid`: path presence + the lc-dominance pair. */
  lemma GateCrossLookNest(re: R.regex, code: RB.code, endl: nat, pc: nat,
                          cc: seq<int>, qc: seq<int>, lc': seq<int>, lid: int)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires NR.LookBehindFragmentRE(re) && LTB.LookUnique(re)
    requires pc < endl
    requires NestInvRE(re, code, 0, endl, pc, cc, qc, -1)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    requires AI.get_idx(lc', lid) >= 0
    requires forall k :: AI.get_idx(qc, k) <= AI.get_idx(lc', lid)
    ensures lid >= 0 && (lid as nat) in LTB.LookIds(re)
    ensures LookPathPresent(re, cc, qc, -1, lid as nat)
    ensures AI.get_idx(lc', lid) >= MxAtLidLk(re, qc, -1, lid as nat)
  {
    NestInvLookSite(re, code, 0, endl, pc, cc, qc, -1, lid);
    MxAtLidLE(re, qc, -1, lid as nat, AI.get_idx(lc', lid));
  }

  /** (L4 NESTED) `GateCrossLookNest` generalized to the full `NestedFragmentRE`
      — a PURE FRAGMENT SWAP. The only fragment-dependent step is
      `NestInvLookSite`, whose depth-general form `NestInvLookSiteNested` is a
      verbatim clone (see that chain's header); `MxAtLidLE` carries no fragment
      hypothesis. `LookBehindFragmentRE` is not otherwise consumed here. */
  lemma GateCrossLookNestNested(re: R.regex, code: RB.code, endl: nat, pc: nat,
                                cc: seq<int>, qc: seq<int>, lc': seq<int>, lid: int)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires NR.NestedFragmentRE(re) && LTB.LookUnique(re)
    requires pc < endl
    requires NestInvRE(re, code, 0, endl, pc, cc, qc, -1)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    requires AI.get_idx(lc', lid) >= 0
    requires forall k :: AI.get_idx(qc, k) <= AI.get_idx(lc', lid)
    ensures lid >= 0 && (lid as nat) in LTB.LookIds(re)
    ensures LookPathPresent(re, cc, qc, -1, lid as nat)
    ensures AI.get_idx(lc', lid) >= MxAtLidLk(re, qc, -1, lid as nat)
  {
    NestInvLookSiteNested(re, code, 0, endl, pc, cc, qc, -1, lid);
    MxAtLidLE(re, qc, -1, lid as nat, AI.get_idx(lc', lid));
  }

  // ==========================================================================
  // (L4 NESTED) TOP-LEVEL gate-site navigation: a `CheckOracle`/`NegCheckOracle`
  // in the MAIN code names a TOP-LEVEL look. Mirrors `PIV.LookCheckIdsRE`
  // (which lands `l in LookIds`), sharpened to `l in TopLookIds` — the main
  // code holds a look's single gate instruction and never inlines a body, so
  // the navigation reaches only looks not nested in another look. Under the
  // full `NestedFragmentRE`. `TopLookIds` decomposes trivially on
  // alt/con/quant/capture, so each recursive arm closes by the definitional
  // subset; the `Re_lookaround` node IS the top-level id.
  // ==========================================================================

  /** (L4 NESTED) `LookCheckIdsMinRE` sharpened to `TopLookIds`. */
  lemma LookSiteTopMinNested(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.NestedFragmentRE(r1) && LTB.LookUnique(r1)
    requires NR.NfaRepMinRE(k, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.CheckOracle? ==>
      var l := NR.GetPcRE(code, pc).value.col; l >= 0 && (l as nat) in TopLookIds(r1)
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.NegCheckOracle? ==>
      var l := NR.GetPcRE(code, pc).value.ncl; l >= 0 && (l as nat) in TopLookIds(r1)
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, start + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, endl);
    NR.NfaRepIncrRE(r1, code, start + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, endl);
    if pc == start {
    } else if pc < e1 {
      LookSiteTopNested(r1, code, start + 1, e1, pc);
    } else {
      LookSiteTopMinNested(k - 1, qid, r1, code, e1, endl, pc);
    }
  }

  /** (L4 NESTED) `LookCheckIdsOptRE` sharpened to `TopLookIds`. */
  lemma LookSiteTopOptNested(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.NestedFragmentRE(r1) && LTB.LookUnique(r1)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.CheckOracle? ==>
      var l := NR.GetPcRE(code, pc).value.col; l >= 0 && (l as nat) in TopLookIds(r1)
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.NegCheckOracle? ==>
      var l := NR.GetPcRE(code, pc).value.ncl; l >= 0 && (l as nat) in TopLookIds(r1)
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1))
      && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, start + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    NR.NfaRepIncrRE(r1, code, start + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    if pc <= start + 2 {
    } else if pc < e1 {
      LookSiteTopNested(r1, code, start + 3, e1, pc);
    } else if pc == e1 {
    } else {
      LookSiteTopOptNested(k - 1, greedy, qid, r1, code, e1 + 1, endl, pc);
    }
  }

  /** (L4 NESTED) A main-code `CheckOracle`/`NegCheckOracle` names a TOP-LEVEL
      look. `PIV.LookCheckIdsRE` sharpened `LookIds`→`TopLookIds`. */
  lemma LookSiteTopNested(re: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.NestedFragmentRE(re) && LTB.LookUnique(re)
    requires NR.NfaRepRE(re, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.CheckOracle? ==>
      var l := NR.GetPcRE(code, pc).value.col; l >= 0 && (l as nat) in TopLookIds(re)
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.NegCheckOracle? ==>
      var l := NR.GetPcRE(code, pc).value.ncl; l >= 0 && (l as nat) in TopLookIds(re)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(lid, la, r1) =>
      assert pc == start;
      assert lid >= 0;                                  // LookUnique
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(endl))
        && NR.NfaRepRE(r2, code, e1 + 1, endl);
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, endl);
      if pc == start {
      } else if pc < e1 {
        LookSiteTopNested(r1, code, start + 1, e1, pc);
      } else if pc == e1 {
      } else {
        LookSiteTopNested(r2, code, e1 + 1, endl, pc);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, endl);
      NR.NfaRepIncrRE(r1, code, start, e1);
      NR.NfaRepIncrRE(r2, code, e1, endl);
      if pc < e1 {
        LookSiteTopNested(r1, code, start, e1, pc);
      } else {
        LookSiteTopNested(r2, code, e1, endl, pc);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      if pc == start {
      } else if pc < e1 {
        LookSiteTopNested(r1, code, start + 1, e1, pc);
      } else {
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| NR.GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
          && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, code, start + 3, e1)
          && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(start))
          && endl == e1 + 2;
        NR.NfaRepIncrRE(r1, code, start + 3, e1);
        if pc <= start + 2 {
        } else if pc < e1 {
          LookSiteTopNested(r1, code, start + 3, e1, pc);
        } else {
        }
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if pc < em {
          LookSiteTopMinNested(q.min as nat, qid, r1, code, start, em, pc);
        } else {
          LookSiteTopOptNested((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, pc);
        }
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          LookSiteTopMinNested((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc == em {
        } else if pc < e1 {
          LookSiteTopNested(r1, code, em + 1, e1, pc);
        } else {
        }
      }
  }

  // ==========================================================================
  // R1 (classification brick): innermost-direct owner, NestDepth drop, and the
  // nested-write frame -- the tree-shape facts the depth-k capture recursion
  // consumes.
  // ==========================================================================

  /** R1 #1: the innermost-DIRECT owner of a nested capture `g`. This refines
      `InnermostLookOwnerExists`, which ALREADY ensures the three direct-write
      facts; the only addition is carrying `PIV.CapUnique(r)` in the requires
      for callers that need it downstream. Thin wrapper. */
  lemma InnermostOwnerDirect(r: R.regex, g: nat) returns (owner: nat)
    requires PIV.CapUnique(r) && LTB.LookUnique(r)
    requires g in PIV.CapIdsInLooks(r)
    ensures owner in LTB.LookIds(r)
    ensures g in PIV.CapIds(LookBodyOfRE(r, owner))
    ensures g !in PIV.CapIdsInLooks(LookBodyOfRE(r, owner))
  {
    owner := InnermostLookOwnerExists(r, g);
  }

  /** R1 #2: descending into a look body strictly DROPS the nesting depth --
      the well-founded measure the depth-k capture recursion decreases on.
      Structural induction following `LookBodyOfRE` / `LookIds`. */
  lemma NestDepthLookBodyDrops(r: R.regex, l: nat)
    requires l in LTB.LookIds(r)
    ensures NR.NestDepth(LookBodyOfRE(r, l)) < NR.NestDepth(r)
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      if l in LTB.LookIds(r1) { NestDepthLookBodyDrops(r1, l); }
      else { NestDepthLookBodyDrops(r2, l); }
    case Re_con(r1, r2) =>
      if l in LTB.LookIds(r1) { NestDepthLookBodyDrops(r1, l); }
      else { NestDepthLookBodyDrops(r2, l); }
    case Re_quant(_, _, _, r1) => NestDepthLookBodyDrops(r1, l);
    case Re_capture(_, r1) => NestDepthLookBodyDrops(r1, l);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == l {
      } else {
        NestDepthLookBodyDrops(r1, l);
      }
  }

  /** R1 #3: with `owner` the innermost-direct owner of `g` (as produced by
      `InnermostOwnerDirect`), any OTHER look `l2` whose body ALSO contains `g`
      has `owner` nested inside it -- `l2` is a proper ANCESTOR of `owner` that
      only reaches `g` through the nested `owner` look, so it gates `g` rather
      than writing it. Derived from `LookBodiesCapsDisjointOrNested` (rule out
      the disjoint arm: `g` is in both bodies; rule out the "l2 nested in owner"
      arm: that would bury `g` in a look inside owner's body, contradicting
      `g !in CapIdsInLooks(owner-body)`), leaving "owner nested in l2". */
  lemma NestedGWriteFrame(r: R.regex, g: nat, owner: nat, l2: nat)
    requires PIV.CapUnique(r) && LTB.LookUnique(r)
    requires g in PIV.CapIdsInLooks(r)
    requires owner in LTB.LookIds(r)
    requires g in PIV.CapIds(LookBodyOfRE(r, owner))
    requires g !in PIV.CapIdsInLooks(LookBodyOfRE(r, owner))
    requires l2 in LTB.LookIds(r) && l2 != owner
    requires g in PIV.CapIds(LookBodyOfRE(r, l2))
    ensures owner in LTB.LookIds(LookBodyOfRE(r, l2))
  {
    LookBodiesCapsDisjointOrNested(r, owner, l2);
    if PIV.CapIds(LookBodyOfRE(r, owner)) * PIV.CapIds(LookBodyOfRE(r, l2)) == {} {
      assert g in PIV.CapIds(LookBodyOfRE(r, owner)) * PIV.CapIds(LookBodyOfRE(r, l2));  // false
    } else if l2 in LTB.LookIds(LookBodyOfRE(r, owner))
              && PIV.CapIds(LookBodyOfRE(r, l2)) <= PIV.CapIds(LookBodyOfRE(r, owner)) {
      // l2 nested in owner's body: g would then sit in a nested look -- contradiction
      LookBodyCompose(r, owner, l2);
      LookBodyCapsIn(LookBodyOfRE(r, owner), l2);
      assert g in PIV.CapIdsInLooks(LookBodyOfRE(r, owner));
    } else {
      // owner nested in l2: the conclusion
    }
  }
}
