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
  import PIV = LindenElkPikeInv
  import AR = LindenElkActionsRep

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
}
