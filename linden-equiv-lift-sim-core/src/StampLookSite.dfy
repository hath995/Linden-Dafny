// (G4b-2, 2026-11-18) The look-gate twin of `NST.NestStampTopCapSite`: at a top-level `CheckOracle(lid)` /
// `NegCheckOracle(lid)` site, no STAMPED quantifier's body contains the look. `FrozenOk`'s frame at a gate pass
// needs it (the pass writes the look's groups; a live stamp's frozen groups must be elsewhere). Transcribed from
// `NestStampCapSite{Min,Opt,RE}` with the look gate in place of the capture write.
module LindenElkStampLookSite {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import NR = LindenElkNfaRep
  import AI = ArrayInterp
  import PIV = LindenElkPikeInv
  import NI = LindenElkNestInv
  import LTB = LindenElkLookTables
  import opened LindenElkNestStamp

  lemma StampLookSiteMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat,
                             pc: nat, qcp: seq<int>, lid: nat)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    requires LTB.LookUnique(r1) && PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    requires NestStampMinRE(k, qid, r1, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid as int)) || NR.GetPcRE(code, pc) == Some(RB.NegCheckOracle(lid as int))
    ensures lid in LTB.LookIds(r1)
    ensures StampClearRE(qcp, qid)
    ensures forall A: nat :: A in PIV.QuantIds(r1) && AI.get_idx(qcp, A) >= 0
              ==> lid !in LTB.LookIds(PIV.QidBody(r1, A))
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
      StampLookSiteRE(r1, code, pcb + 1, e1, pc, qcp, lid);
    } else {
      assert {:split_here} true;
      StampLookSiteMin(k - 1, qid, r1, code, e1, pce, pc, qcp, lid);
    }
  }

  lemma StampLookSiteOpt(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                             pcb: nat, pce: nat, pc: nat, qcp: seq<int>, lid: nat)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    requires LTB.LookUnique(r1) && PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    requires NestStampOptRE(k, greedy, qid, r1, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid as int)) || NR.GetPcRE(code, pc) == Some(RB.NegCheckOracle(lid as int))
    ensures lid in LTB.LookIds(r1)
    ensures StampClearRE(qcp, qid)
    ensures forall A: nat :: A in PIV.QuantIds(r1) && AI.get_idx(qcp, A) >= 0
              ==> lid !in LTB.LookIds(PIV.QidBody(r1, A))
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
      StampLookSiteRE(r1, code, pcb + 3, e1, pc, qcp, lid);
    } else {
      assert {:split_here} true;
      StampLookSiteOpt(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc, qcp, lid);
    }
  }

  /** (2026-11-04) Register-generic `NestStampOpenSiteRE`: a capture OPEN or
      CLOSE site is inside `re` and outside the body of every STAMPED
      quantifier of `re` — the hypothesis the readout's Open and Close
      commutations need (`PIV.LiveStampsGm{Open,Close}Commute`). */
  lemma StampLookSiteRE(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat,
                            qcp: seq<int>, lid: nat)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires LTB.LookUnique(re) && PIV.QuantUnique(re)
    requires pcb <= pc < pce
    requires NestStampRE(re, code, pcb, pce, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid as int)) || NR.GetPcRE(code, pc) == Some(RB.NegCheckOracle(lid as int))
    ensures lid in LTB.LookIds(re)
    ensures forall A: nat :: A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
              ==> lid !in LTB.LookIds(PIV.QidBody(re, A))
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
    case Re_lookaround(lid0, la, r1) =>
      assert {:split_here} true;
      assert pc == pcb;
      assert lid0 == lid as int;                     // the gate's own id
      assert lid in LTB.LookIds(re);
      assert lid !in LTB.LookIds(r1);                // LookUnique
      forall A: nat | A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
        ensures lid !in LTB.LookIds(PIV.QidBody(re, A)) {
        assert A in PIV.QuantIds(r1) && PIV.QidBody(re, A) == PIV.QidBody(r1, A);
        NI.QidBodyLookIdsSub(r1, A);
      }
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
        StampLookSiteRE(r1, code, pcb + 1, e1, pc, qcp, lid);
        LookSplitAlt(re, r1, r2, qcp, lid, true);
      } else {
        StampLookSiteRE(r2, code, e1 + 1, pce, pc, qcp, lid);
        LookSplitAlt(re, r1, r2, qcp, lid, false);
      }
    case Re_con(r1, r2) =>
      assert {:split_here} true;   // (2026-09-04) per-arm batch: the un-split body times out at 600 s
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce)
        && (if pc < e1 then NestStampRE(r1, code, pcb, e1, pc, qcp)
            else NestStampRE(r2, code, e1, pce, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb, e1);
      NR.NfaRepIncrRE(r2, code, e1, pce);
      if pc < e1 {
        StampLookSiteRE(r1, code, pcb, e1, pc, qcp, lid);
        LookSplitAlt(re, r1, r2, qcp, lid, true);
      } else {
        StampLookSiteRE(r2, code, e1, pce, pc, qcp, lid);
        LookSplitAlt(re, r1, r2, qcp, lid, false);
      }
    case Re_capture(cid, r1) =>
      assert {:split_here} true;
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1
        && (pcb + 1 <= pc < e1 ==> NestStampRE(r1, code, pcb + 1, e1, pc, qcp));
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      assert PIV.QuantIds(re) == PIV.QuantIds(r1);
      if pc == pcb || pc == e1 {
        assert false;                                // the capture's own open/close
      } else {
        StampLookSiteRE(r1, code, pcb + 1, e1, pc, qcp, lid);
        forall A: nat | A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
          ensures lid !in LTB.LookIds(PIV.QidBody(re, A)) {
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
          StampLookSiteMin(mn, qid, r1, code, pcb, em, pc, qcp, lid);
        } else {
          StampLookSiteOpt(kx, q.greedy, qid, r1, code, em, pce, pc, qcp, lid);
        }
        LookQuantIds(re, nul, qid, q, r1, qcp, lid);
        return;
      }
      if !(q.min == 0 && q.max == None) && nul != R.NonNullable && !q.greedy {
        assert {:split_here} true;
        var mn := q.min as nat;
        var em, e1 := NestStampGenREInv(nul, qid, q, r1, code, pcb, pce, pc, qcp);
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          StampLookSiteMin(mn, qid, r1, code, pcb, em, pc, qcp, lid);
        } else if em + 3 <= pc < e1 {
          StampLookSiteRE(r1, code, em + 3, e1, pc, qcp, lid);
        } else {
          assert false;                              // Fork/stamp/BeginLoop/EndLoop/Jmp
        }
        LookQuantIds(re, nul, qid, q, r1, qcp, lid);
        return;
      }
      if !(q.min == 0 && q.max == None) && nul == R.CINullable {
        assert {:split_here} true;
        var mn1 := (q.min - 1) as nat;
        var em, e1 := NestStampCinREInv(nul, qid, q, r1, code, pcb, pce, pc, qcp);
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          StampLookSiteMin(mn1, qid, r1, code, pcb, em, pc, qcp, lid);
        } else if em + 3 <= pc < e1 {
          StampLookSiteRE(r1, code, em + 3, e1, pc, qcp, lid);
        } else {
          assert false;                              // the loop's own instructions
        }
        LookQuantIds(re, nul, qid, q, r1, qcp, lid);
        return;
      }
      if !(q.min == 0 && q.max == None) && nul == R.CDNullable {
        assert {:split_here} true;
        var mn1 := (q.min - 1) as nat;
        var em, e1 := NestStampCdnREInv(nul, qid, q, r1, code, pcb, pce, pc, qcp);
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          StampLookSiteMin(mn1, qid, r1, code, pcb, em, pc, qcp, lid);
        } else if em + 3 <= pc < e1 {
          StampLookSiteRE(r1, code, em + 3, e1, pc, qcp, lid);
        } else {
          assert false;                              // the loop's own instructions
        }
        LookQuantIds(re, nul, qid, q, r1, qcp, lid);
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
          StampLookSiteMin(mn1, qid, r1, code, pcb, em, pc, qcp, lid);
        } else if em + 1 <= pc < e1 {
          StampLookSiteRE(r1, code, em + 1, e1, pc, qcp, lid);
        } else {
          assert false;                              // the mark / the backward fork
        }
        LookQuantIds(re, nul, qid, q, r1, qcp, lid);
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
        StampLookSiteRE(r1, code, pcb + 3, e1, pc, qcp, lid);
      } else {
        assert false;                                // the loop's own instructions
      }
      LookQuantIds(re, nul, qid, q, r1, qcp, lid);
  }

  /** The binary arms: the gate is in one half; a stamped quantifier of the other half cannot own it
      (`LookUnique`), one in the same half is the recursive conclusion. */
  lemma LookSplitAlt(re: R.regex, r1: R.regex, r2: R.regex, qcp: seq<int>, lid: nat, inLeft: bool)
    requires re == R.Re_alt(r1, r2) || re == R.Re_con(r1, r2)
    requires LTB.LookUnique(re)
    requires inLeft ==> lid in LTB.LookIds(r1)
    requires !inLeft ==> lid in LTB.LookIds(r2)
    requires inLeft ==> forall A: nat :: A in PIV.QuantIds(r1) && AI.get_idx(qcp, A) >= 0
                          ==> lid !in LTB.LookIds(PIV.QidBody(r1, A))
    requires !inLeft ==> forall A: nat :: A in PIV.QuantIds(r2) && AI.get_idx(qcp, A) >= 0
                           ==> lid !in LTB.LookIds(PIV.QidBody(r2, A))
    ensures lid in LTB.LookIds(re)
    ensures forall A: nat :: A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
              ==> lid !in LTB.LookIds(PIV.QidBody(re, A))
  {
    assert LTB.LookIds(re) == LTB.LookIds(r1) + LTB.LookIds(r2);
    assert PIV.QuantIds(re) == PIV.QuantIds(r1) + PIV.QuantIds(r2);
    assert LTB.LookIds(r1) * LTB.LookIds(r2) == {};
    forall A: nat | A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
      ensures lid !in LTB.LookIds(PIV.QidBody(re, A)) {
      if A in PIV.QuantIds(r1) {
        assert PIV.QidBody(re, A) == PIV.QidBody(r1, A);
        NI.QidBodyLookIdsSub(r1, A);
        if !inLeft {
          assert lid !in LTB.LookIds(r1)
            by { if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        }
      } else {
        assert A in PIV.QuantIds(r2);
        assert PIV.QidBody(re, A) == PIV.QidBody(r2, A);
        NI.QidBodyLookIdsSub(r2, A);
        if inLeft {
          assert lid !in LTB.LookIds(r2)
            by { if lid in LTB.LookIds(r2) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        }
      }
    }
  }

  lemma LookQuantIds(re: R.regex, nul: R.nullability, qid: R.quantid, q: R.counted_quantifier,
                     r1: R.regex, qcp: seq<int>, lid: nat)
    requires re == R.Re_quant(nul, qid, q, r1)
    requires LTB.LookUnique(re) && PIV.QuantUnique(re)
    requires lid in LTB.LookIds(r1)
    requires StampClearRE(qcp, qid)
    requires forall A: nat :: A in PIV.QuantIds(r1) && AI.get_idx(qcp, A) >= 0
               ==> lid !in LTB.LookIds(PIV.QidBody(r1, A))
    ensures lid in LTB.LookIds(re)
    ensures forall A: nat :: A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
              ==> lid !in LTB.LookIds(PIV.QidBody(re, A))
  {
    assert LTB.LookIds(re) == LTB.LookIds(r1);
    forall A: nat | A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
      ensures lid !in LTB.LookIds(PIV.QidBody(re, A)) {
      if qid >= 0 && A == qid as nat {
        assert AI.get_idx(qcp, qid) < 0;             // StampClearRE
        assert false;
      } else {
        assert A in PIV.QuantIds(r1);
        assert PIV.QidBody(re, A) == PIV.QidBody(r1, A);
      }
    }
  }

  /** (G4b-2) Machine A's positional stamp invariant at a top-level look gate: no stamped quantifier's body
      holds the look (the twin of `NestStampTopCapSite`). */
  lemma StampTopLookSite(re: R.regex, code: RB.code, endl: nat, pc: nat, qcp: seq<int>, lid: nat)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires LTB.LookUnique(re) && PIV.QuantUnique(re)
    requires pc < endl
    requires NestStampTopRE(re, code, endl, pc, qcp)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid as int)) || NR.GetPcRE(code, pc) == Some(RB.NegCheckOracle(lid as int))
    ensures lid in LTB.LookIds(re)
    ensures forall A: nat :: A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
              ==> lid !in LTB.LookIds(PIV.QidBody(re, A))
  {
    StampLookSiteRE(re, code, 0, endl, pc, qcp, lid);
  }

  /** A look's body groups are among the regex's. */
  lemma CapIdsLookBodySub(r: R.regex, lid: nat)
    requires lid in LTB.LookIds(r)
    ensures PIV.CapIds(NI.LookBodyOfRE(r, lid)) <= PIV.CapIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if lid in LTB.LookIds(r1) { CapIdsLookBodySub(r1, lid); } else { CapIdsLookBodySub(r2, lid); }
    case Re_con(r1, r2) => if lid in LTB.LookIds(r1) { CapIdsLookBodySub(r1, lid); } else { CapIdsLookBodySub(r2, lid); }
    case Re_quant(_, _, _, r1) => CapIdsLookBodySub(r1, lid);
    case Re_capture(_, r1) => CapIdsLookBodySub(r1, lid);
    case Re_lookaround(lid0, _, r1) => if !(lid0 >= 0 && (lid0 as nat) == lid) { CapIdsLookBodySub(r1, lid); }
  }

  /** (G4b-2) A look outside a quantifier's body (the quantifier outside every look) owns groups disjoint
      from the body's. */
  lemma LookBodyQidBodyDisjoint(re: R.regex, lid: nat, q: nat)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires lid in LTB.LookIds(re) && q in PIV.QuantIdsOutsideLooks(re) && q in PIV.QuantIds(re)
    requires lid !in LTB.LookIds(PIV.QidBody(re, q))
    ensures PIV.CapIds(NI.LookBodyOfRE(re, lid)) !! PIV.CapIds(PIV.QidBody(re, q))
    decreases re
  {
    PIV.QuantIdsOutsideLooksSub(re);
    match re
    case Re_alt(r1, r2) =>
      PIV.QuantIdsOutsideLooksSub(r1); PIV.QuantIdsOutsideLooksSub(r2);
      LookBodyQidBodyDisjointBin(re, r1, r2, lid, q);
    case Re_con(r1, r2) =>
      PIV.QuantIdsOutsideLooksSub(r1); PIV.QuantIdsOutsideLooksSub(r2);
      LookBodyQidBodyDisjointBin(re, r1, r2, lid, q);
    case Re_quant(nul, qid, qq, r1) =>
      PIV.QuantIdsOutsideLooksSub(r1);
      if qid >= 0 && (qid as nat) == q {
        assert PIV.QidBody(re, q) == r1;
        assert lid in LTB.LookIds(r1);
        assert false;
      } else {
        assert q in PIV.QuantIdsOutsideLooks(r1) && q in PIV.QuantIds(r1);
        assert PIV.QidBody(re, q) == PIV.QidBody(r1, q);
        assert NI.LookBodyOfRE(re, lid) == NI.LookBodyOfRE(r1, lid);
        LookBodyQidBodyDisjoint(r1, lid, q);
      }
    case Re_capture(_, r1) =>
      assert NI.LookBodyOfRE(re, lid) == NI.LookBodyOfRE(r1, lid);
      LookBodyQidBodyDisjoint(r1, lid, q);
    case Re_lookaround(_, _, _) =>
      assert false;                                  // no quantifier outside looks
  }

  lemma LookBodyQidBodyDisjointBin(re: R.regex, r1: R.regex, r2: R.regex, lid: nat, q: nat)
    requires re == R.Re_alt(r1, r2) || re == R.Re_con(r1, r2)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires lid in LTB.LookIds(re) && q in PIV.QuantIdsOutsideLooks(re) && q in PIV.QuantIds(re)
    requires PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIds(r1) && PIV.QuantIdsOutsideLooks(r2) <= PIV.QuantIds(r2)
    requires lid !in LTB.LookIds(PIV.QidBody(re, q))
    ensures PIV.CapIds(NI.LookBodyOfRE(re, lid)) !! PIV.CapIds(PIV.QidBody(re, q))
    decreases re, 0
  {
    assert PIV.CapIds(r1) * PIV.CapIds(r2) == {};
    var inL := lid in LTB.LookIds(r1);
    var qL := q in PIV.QuantIdsOutsideLooks(r1);
    if inL { assert NI.LookBodyOfRE(re, lid) == NI.LookBodyOfRE(r1, lid); CapIdsLookBodySub(r1, lid); }
    else { assert NI.LookBodyOfRE(re, lid) == NI.LookBodyOfRE(r2, lid); CapIdsLookBodySub(r2, lid); }
    if qL { assert PIV.QidBody(re, q) == PIV.QidBody(r1, q); PIV.CapIdsQidBodySubset(r1, q); }
    else {
      assert q in PIV.QuantIdsOutsideLooks(r2);
      assert q !in PIV.QuantIds(r1) by { if q in PIV.QuantIds(r1) { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); } }
      assert PIV.QidBody(re, q) == PIV.QidBody(r2, q); PIV.CapIdsQidBodySubset(r2, q);
    }
    if inL && qL { assert q in PIV.QuantIds(r1); LookBodyQidBodyDisjoint(r1, lid, q); }
    else if !inL && !qL { assert q in PIV.QuantIds(r2); LookBodyQidBodyDisjoint(r2, lid, q); }
    else if inL {
      forall g | g in PIV.CapIds(NI.LookBodyOfRE(re, lid)) && g in PIV.CapIds(PIV.QidBody(re, q)) ensures false {
        assert g in PIV.CapIds(r1) * PIV.CapIds(r2);
      }
    } else {
      forall g | g in PIV.CapIds(NI.LookBodyOfRE(re, lid)) && g in PIV.CapIds(PIV.QidBody(re, q)) ensures false {
        assert g in PIV.CapIds(r1) * PIV.CapIds(r2);
      }
    }
  }

  /** A quantifier's body inherits capture uniqueness. */
  lemma CapUniqueQidBody(r: R.regex, qid: nat)
    requires PIV.CapUnique(r) && qid in PIV.QuantIds(r)
    ensures PIV.CapUnique(PIV.QidBody(r, qid))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if qid in PIV.QuantIds(r1) { CapUniqueQidBody(r1, qid); } else { CapUniqueQidBody(r2, qid); }
    case Re_con(r1, r2) => if qid in PIV.QuantIds(r1) { CapUniqueQidBody(r1, qid); } else { CapUniqueQidBody(r2, qid); }
    case Re_quant(_, qid0, _, r1) => if !(qid0 >= 0 && (qid0 as nat) == qid) { CapUniqueQidBody(r1, qid); }
    case Re_capture(_, r1) => CapUniqueQidBody(r1, qid);
    case Re_lookaround(_, _, r1) => CapUniqueQidBody(r1, qid);
  }
}
