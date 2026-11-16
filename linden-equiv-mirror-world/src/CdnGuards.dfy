// (G5b) The guard premise `OBV.GuardsOk` of the oracle bridge/decomposition, discharged by `CdnSound` for
// the runs the column chain makes (from W17 probe 3, `endgame/W17-G5b-oracle.md` §3.2):
//   * a forward accept run of a body with its own table (lookahead row, `M.BodyTreeAtCpNested`);
//   * the lookbehind build: `lazy_prefix(remove_capture(body))` forward, with the ORIGINAL body's table;
//   * the lookahead build: `lazy_prefix(reverse(remove_capture(body)))` BACKWARD with the original body's
//     table, read through the mirror as a forward run of `XRev(remove_capture(body))` over the reversed
//     string against the mirrored view with the anchor-swapped table.
// The induction walks the body's nodes, so no `CdnBody`/`XRev` commutation and no list reordering is needed.
/** (G5b) `OBV.GuardsOk` for the column chain's runs, from `CdnSound`. */
module LindenElkCdnGuards {
  import opened Std.Wrappers
  import R = RegElkRegex
  import AI = ArrayInterp
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import LC = Chars
  import ORc = LindenElkOracleReach
  import OBV = LindenElkOracleBridgeV
  import MIR = LindenElkMirror
  import OMV = LindenElkOracleMirrorV
  import CS = LindenElkCdnSound
  import CTT = LindenElkCdnTreeTie
  import RB = Bytecode
  import CP = Compiler
  import NR = LindenElkNfaRep
  import T = LindenElkTranslate
  import AR = LindenElkActionsRep
  import PIV = LindenElkPikeInv
  import PSM = LindenElkPikeSim

  // ---------------------------------------------------------------------------
  // (A) Forward runs: the table of the code's own regex (lookahead accept run;
  //     FXR(body) accept run for a lookbehind).
  // ---------------------------------------------------------------------------

  lemma GuardsOkOfLocal(r: R.regex, cdn: LCdn.cdns, str: string, ov: LOr.OracleView)
    requires forall cp: int :: 0 <= cp <= |str| ==>
      CS.TableOkLocal(r, LCdn.build_cdn_v(cdn, cp, ov, ORc.CtxAt(str, cp), LAnc.Forward), str, ov, cp)
    ensures OBV.GuardsOk(r, cdn, str, ov)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => GuardsOkOfLocal(r1, cdn, str, ov); GuardsOkOfLocal(r2, cdn, str, ov);
    case Re_con(r1, r2) => GuardsOkOfLocal(r1, cdn, str, ov); GuardsOkOfLocal(r2, cdn, str, ov);
    case Re_quant(_, _, _, r1) => GuardsOkOfLocal(r1, cdn, str, ov);
    case Re_capture(_, r1) => GuardsOkOfLocal(r1, cdn, str, ov);
    case _ =>
  }

  lemma GuardsOkForward(body: R.regex, str: string, ov: LOr.OracleView)
    requires CS.CdnWf(body) && CS.QUnique(body)
    ensures OBV.GuardsOk(body, LCdn.compile_cdns(body), str, ov)
  {
    forall cp: int | 0 <= cp <= |str|
      ensures CS.TableOkLocal(body, LCdn.build_cdn_v(LCdn.compile_cdns(body), cp, ov, ORc.CtxAt(str, cp), LAnc.Forward), str, ov, cp)
    {
      CS.CdnSoundAll(body, str, ov, cp, ORc.CtxAt(str, cp), LAnc.Forward);
      CS.TableOkAllLocal(body, LCdn.build_cdn_v(LCdn.compile_cdns(body), cp, ov, ORc.CtxAt(str, cp), LAnc.Forward), str, ov, cp);
    }
    GuardsOkOfLocal(body, LCdn.compile_cdns(body), str, ov);
  }

  // ---------------------------------------------------------------------------
  // (B) The lookBEHIND build: forward over remove_capture(body), table of the
  //     ORIGINAL body (captures kept).
  // ---------------------------------------------------------------------------

  lemma GuardsOkRemoveCapture(r: R.regex, cdn: LCdn.cdns, str: string, ov: LOr.OracleView)
    requires forall cp: int :: 0 <= cp <= |str| ==>
      CS.TableOkLocal(r, LCdn.build_cdn_v(cdn, cp, ov, ORc.CtxAt(str, cp), LAnc.Forward), str, ov, cp)
    ensures OBV.GuardsOk(R.remove_capture(r), cdn, str, ov)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => GuardsOkRemoveCapture(r1, cdn, str, ov); GuardsOkRemoveCapture(r2, cdn, str, ov);
    case Re_con(r1, r2) => GuardsOkRemoveCapture(r1, cdn, str, ov); GuardsOkRemoveCapture(r2, cdn, str, ov);
    case Re_quant(nul, qid, q, r1) =>
      GuardsOkRemoveCapture(r1, cdn, str, ov);
      if CS.EligibleCdnPlus(nul, q) {
        forall cp: int | 0 <= cp <= |str|
          ensures ORc.CdnBit(cdn, str, ov, cp, qid) <==> OBV.MatchesV(R.remove_capture(r1), str, ov, cp, cp)
        {
          OMV.MatchesVRemoveCapture(r1, str, ov, cp, cp);
        }
      }
    case Re_capture(_, r1) => GuardsOkRemoveCapture(r1, cdn, str, ov);
    case _ =>
  }

  lemma GuardsOkLookbehindBuild(body: R.regex, str: string, ov: LOr.OracleView)
    requires CS.CdnWf(body) && CS.QUnique(body)
    ensures OBV.GuardsOk(R.remove_capture(body), LCdn.compile_cdns(body), str, ov)
  {
    forall cp: int | 0 <= cp <= |str|
      ensures CS.TableOkLocal(body, LCdn.build_cdn_v(LCdn.compile_cdns(body), cp, ov, ORc.CtxAt(str, cp), LAnc.Forward), str, ov, cp)
    {
      CS.CdnSoundAll(body, str, ov, cp, ORc.CtxAt(str, cp), LAnc.Forward);
      CS.TableOkAllLocal(body, LCdn.build_cdn_v(LCdn.compile_cdns(body), cp, ov, ORc.CtxAt(str, cp), LAnc.Forward), str, ov, cp);
    }
    GuardsOkRemoveCapture(body, LCdn.compile_cdns(body), str, ov);
  }

  // ---------------------------------------------------------------------------
  // (C) The lookAHEAD build, through the mirror.
  // ---------------------------------------------------------------------------

  /** The backward table at `cp`, as the engine builds it. */
  function TabB(cs: LCdn.cdns, str: string, ov: LOr.OracleView, cp: int): LCdn.cdn_table {
    LCdn.build_cdn_v(cs, cp, ov, AI.cp_context(cp, str, LAnc.Backward), LAnc.Backward)
  }

  /** One position: the mirrored forward bit IS the backward bit. */
  lemma MirrorBit(cs: LCdn.cdns, str: string, ov: LOr.OracleView, m: int, qid: int)
    requires |ov| == |str| + 1 && 0 <= m <= |str|
    ensures ORc.CdnBit(MIR.SwapAnchorsCdns(cs), LC.Reverse(str), MIR.MirrorView(ov, |str|), m, qid)
        <==> LCdn.cdn_get(TabB(cs, str, ov, |str| - m), qid)
  {
    var n := |str|;
    var cp := n - m;
    MIR.ReverseLen(str);
    MIR.CpContextMirror(str, cp);                 // cp_context(cp, str, Bwd) == cp_context(m, rstr, Fwd)
    assert MIR.Mirror(cp, n) == m;
    MIR.BuildCdnMirror(cs, cp, ov, n, AI.cp_context(cp, str, LAnc.Backward));
  }

  lemma GuardsOkMirrorRec(r: R.regex, cs: LCdn.cdns, str: string, ov: LOr.OracleView)
    requires |ov| == |str| + 1
    requires forall cp: int :: 0 <= cp <= |str| ==> CS.TableOkLocal(r, TabB(cs, str, ov, cp), str, ov, cp)
    ensures |LC.Reverse(str)| == |str|
    ensures OBV.GuardsOk(OMV.XRev(R.remove_capture(r)), MIR.SwapAnchorsCdns(cs), LC.Reverse(str),
                     MIR.MirrorView(ov, |str|))
    decreases r
  {
    MIR.ReverseLen(str);
    var n := |str|;
    var rstr := LC.Reverse(str);
    var mv := MIR.MirrorView(ov, n);
    var cs' := MIR.SwapAnchorsCdns(cs);
    match r
    case Re_alt(r1, r2) =>
      GuardsOkMirrorRec(r1, cs, str, ov); GuardsOkMirrorRec(r2, cs, str, ov);
      assert OMV.XRev(R.remove_capture(r))
          == R.Re_alt(OMV.XRev(R.remove_capture(r1)), OMV.XRev(R.remove_capture(r2)));
    case Re_con(r1, r2) =>
      GuardsOkMirrorRec(r1, cs, str, ov); GuardsOkMirrorRec(r2, cs, str, ov);
      assert OMV.XRev(R.remove_capture(r))
          == R.Re_con(OMV.XRev(R.remove_capture(r2)), OMV.XRev(R.remove_capture(r1)));
    case Re_quant(nul, qid, q, r1) =>
      GuardsOkMirrorRec(r1, cs, str, ov);
      var x1 := OMV.XRev(R.remove_capture(r1));
      assert OMV.XRev(R.remove_capture(r)) == R.Re_quant(nul, qid, q, x1);
      if CS.EligibleCdnPlus(nul, q) {
        forall m: int | 0 <= m <= |rstr|
          ensures ORc.CdnBit(cs', rstr, mv, m, qid) <==> OBV.MatchesV(x1, rstr, mv, m, m)
        {
          var cp := n - m;
          MirrorBit(cs, str, ov, m, qid);
          // TableOkLocal at the node: the backward bit is the body's empty span at cp
          assert CS.TableOkLocal(r, TabB(cs, str, ov, cp), str, ov, cp);
          assert LCdn.cdn_get(TabB(cs, str, ov, cp), qid) <==> OBV.MatchesV(r1, str, ov, cp, cp);
          OMV.MatchesVRemoveCapture(r1, str, ov, cp, cp);
          OMV.MatchesVMirror(R.remove_capture(r1), str, ov, cp, cp);
          assert n - cp == m;
        }
      }
    case Re_capture(_, r1) =>
      GuardsOkMirrorRec(r1, cs, str, ov);
    case _ =>
  }

  /** THE lookahead-build guard: the reversed, capture-stripped build code, run
      forward over the reversed string against the mirrored view, with the
      mirrored ORIGINAL-body table, has every CDN guard right. */
  lemma GuardsOkLookaheadBuild(body: R.regex, str: string, ov: LOr.OracleView)
    requires CS.CdnWf(body) && CS.QUnique(body)
    requires |ov| == |str| + 1
    ensures |LC.Reverse(str)| == |str|
    ensures OBV.GuardsOk(OMV.XRev(R.remove_capture(body)), MIR.SwapAnchorsCdns(LCdn.compile_cdns(body)),
                     LC.Reverse(str), MIR.MirrorView(ov, |str|))
  {
    var cs := LCdn.compile_cdns(body);
    forall cp: int | 0 <= cp <= |str|
      ensures CS.TableOkLocal(body, TabB(cs, str, ov, cp), str, ov, cp)
    {
      CS.CdnSoundAll(body, str, ov, cp, AI.cp_context(cp, str, LAnc.Backward), LAnc.Backward);
      CS.TableOkAllLocal(body, TabB(cs, str, ov, cp), str, ov, cp);
    }
    GuardsOkMirrorRec(body, cs, str, ov);
  }

  // ---------------------------------------------------------------------------
  // (D) The run premise of a ROW's body code (N1): the table the engine builds from `compile_cdns(body)` at
  //     every position is right about every `CheckNullable` of `compile_to_bytecode(body)`. The row twin of
  //     main-cin-lk's `GuardsOkRunTop`; it needs no oracle premise (`CTT.FirstEmptyPathRMatchesV` reads
  //     the same view as the table).
  // ---------------------------------------------------------------------------

  // ---------------------------------------------------------------------------
  // 1. A guard of the code names an eligible CDN plus of the regex.
  // ---------------------------------------------------------------------------

  lemma GuardIdsRE(re: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.NestedFragmentCdnRE(re) && PIV.QuantUnique(re)
    requires NR.NfaRepRE(re, code, start, endl)
    requires start <= pc < endl
    ensures forall q: int :: NR.GetPcRE(code, pc) == Some(RB.CheckNullable(q)) ==> q in CS.CdnQIds(re)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
                     && NR.NfaRepRE(r1, code, start + 1, e1)
                     && NR.GetPcRE(code, e1) == Some(RB.Jmp(endl))
                     && NR.NfaRepRE(r2, code, e1 + 1, endl);
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, endl);
      if pc == start {
      } else if pc < e1 {
        GuardIdsRE(r1, code, start + 1, e1, pc);
      } else if pc == e1 {
      } else {
        GuardIdsRE(r2, code, e1 + 1, endl, pc);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, endl);
      NR.NfaRepIncrRE(r1, code, start, e1);
      NR.NfaRepIncrRE(r2, code, e1, endl);
      if pc < e1 {
        GuardIdsRE(r1, code, start, e1, pc);
      } else {
        GuardIdsRE(r2, code, e1, endl, pc);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
                     && NR.NfaRepRE(r1, code, start + 1, e1)
                     && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
                     && endl == e1 + 1;
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      if pc == start {
      } else if pc < e1 {
        GuardIdsRE(r1, code, start + 1, e1, pc);
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
          GuardIdsRE(r1, code, start + 3, e1, pc);
        } else {
        }
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if pc < em {
          GuardIdsMinRE(q.min as nat, qid, r1, code, start, em, pc);
        } else {
          GuardIdsOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, pc);
        }
      } else if nul != R.NonNullable && !q.greedy {
        // §2.5a GENERIC: min forced copies, then the star loop
        var em, e1 := NR.NfaRepREGenInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          GuardIdsMinRE(q.min as nat, qid, r1, code, start, em, pc);
        } else if pc <= em + 2 {
        } else if pc < e1 {
          GuardIdsRE(r1, code, em + 3, e1, pc);
        } else {
        }
      } else if nul == R.CDNullable {
        // (G5a) CDN-GREEDY: the CIN layout with the guard at e1 + 2 (no write, no gate) and the
        // true stamp at e1 + 3
        var em, e1 := NR.NfaRepRECdnInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          GuardIdsMinRE((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc <= em + 2 {
        } else if pc < e1 {
          GuardIdsRE(r1, code, em + 3, e1, pc);
        } else {
        }
      } else if nul != R.NonNullable {
        // §2.5b CIN-GREEDY: min-1 forced copies, then the stamped end-fork loop
        var em, e1 := NR.NfaRepRECinInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          GuardIdsMinRE((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc <= em + 2 {
        } else if pc < e1 {
          GuardIdsRE(r1, code, em + 3, e1, pc);
        } else {
        }
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          GuardIdsMinRE((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc == em {
        } else if pc < e1 {
          GuardIdsRE(r1, code, em + 1, e1, pc);
        } else {
        }
      }
  }

  lemma GuardIdsMinRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.NestedFragmentCdnRE(r1) && PIV.QuantUnique(r1)
    requires NR.NfaRepMinRE(k, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures forall q: int :: NR.GetPcRE(code, pc) == Some(RB.CheckNullable(q)) ==> q in CS.CdnQIds(r1)
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
      GuardIdsRE(r1, code, start + 1, e1, pc);
    } else {
      GuardIdsMinRE(k - 1, qid, r1, code, e1, endl, pc);
    }
  }

  lemma GuardIdsOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.NestedFragmentCdnRE(r1) && PIV.QuantUnique(r1)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures forall q: int :: NR.GetPcRE(code, pc) == Some(RB.CheckNullable(q)) ==> q in CS.CdnQIds(r1)
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
      GuardIdsRE(r1, code, start + 3, e1, pc);
    } else if pc == e1 {
    } else {
      GuardIdsOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl, pc);
    }
  }

  // ---------------------------------------------------------------------------
  // 2. cdn-sound's vocabulary in the tower's.
  // ---------------------------------------------------------------------------

  lemma QIdsAreQuantIds(r: R.regex)
    requires PIV.QuantUnique(r)
    ensures forall q: int :: q in CS.QIds(r) ==> q >= 0 && (q as nat) in PIV.QuantIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => QIdsAreQuantIds(r1); QIdsAreQuantIds(r2);
    case Re_con(r1, r2) => QIdsAreQuantIds(r1); QIdsAreQuantIds(r2);
    case Re_quant(_, _, _, r1) => QIdsAreQuantIds(r1);
    case Re_capture(_, r1) => QIdsAreQuantIds(r1);
    case Re_lookaround(_, _, r1) => QIdsAreQuantIds(r1);
    case _ =>
  }

  lemma QUniqueOfQuantUnique(r: R.regex)
    requires PIV.QuantUnique(r)
    ensures CS.QUnique(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      QUniqueOfQuantUnique(r1); QUniqueOfQuantUnique(r2); QIdsAreQuantIds(r1); QIdsAreQuantIds(r2);
      forall q: int | q in CS.QIds(r1) && q in CS.QIds(r2) ensures false {
        assert (q as nat) in PIV.QuantIds(r1) * PIV.QuantIds(r2);
      }
    case Re_con(r1, r2) =>
      QUniqueOfQuantUnique(r1); QUniqueOfQuantUnique(r2); QIdsAreQuantIds(r1); QIdsAreQuantIds(r2);
      forall q: int | q in CS.QIds(r1) && q in CS.QIds(r2) ensures false {
        assert (q as nat) in PIV.QuantIds(r1) * PIV.QuantIds(r2);
      }
    case Re_quant(_, qid, _, r1) => QUniqueOfQuantUnique(r1); QIdsAreQuantIds(r1);
    case Re_capture(_, r1) => QUniqueOfQuantUnique(r1);
    case Re_lookaround(_, _, r1) => QUniqueOfQuantUnique(r1);
    case _ =>
  }

  /** The body cdn-sound assigns to a CDN plus id is the tower's `QidBody`, well-formed, with its looks in
      the table. */
  lemma CdnBodyFacts(r: R.regex, qm: AR.QMap, q: int)
    requires T.TransWf(r) && PIV.QuantUnique(r) && AR.LmapOk(r, qm)
    requires q in CS.CdnQIds(r)
    ensures q >= 0 && (q as nat) in PIV.QuantIds(r)
    ensures CS.CdnBody(r, q) == PIV.QidBody(r, q as nat)
    ensures T.TransWf(CS.CdnBody(r, q)) && AR.LmapOk(CS.CdnBody(r, q), qm)
    decreases r
  {
    CS.CdnQIdsSub(r);
    QIdsAreQuantIds(r);
    match r
    case Re_alt(r1, r2) =>
      if q in CS.CdnQIds(r1) {
        CdnBodyFacts(r1, qm, q);
      } else {
        CdnBodyFacts(r2, qm, q);
        assert (q as nat) !in PIV.QuantIds(r1) by {
          if (q as nat) in PIV.QuantIds(r1) { assert (q as nat) in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
      }
    case Re_con(r1, r2) =>
      if q in CS.CdnQIds(r1) {
        CdnBodyFacts(r1, qm, q);
      } else {
        CdnBodyFacts(r2, qm, q);
        assert (q as nat) !in PIV.QuantIds(r1) by {
          if (q as nat) in PIV.QuantIds(r1) { assert (q as nat) in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
      }
    case Re_quant(nul, q0, qq, r1) =>
      if !(CS.EligibleCdnPlus(nul, qq) && q0 == q) {
        CdnBodyFacts(r1, qm, q);
        assert q0 != q;   // q is an id of the body, and the node's id is not (QuantUnique)
      }
    case Re_capture(_, r1) => CdnBodyFacts(r1, qm, q);
    case Re_lookaround(_, _, r1) => CdnBodyFacts(r1, qm, q);
  }

  lemma GuardsOkRunRow(qm: AR.QMap, body: R.regex, code: RB.code, endl: nat, str: string, ov: LOr.OracleView)
    requires T.TransWf(body) && NR.NestedFragmentCdnRE(body) && PIV.QuantUnique(body)
    requires AR.QmapOk(body, qm) && AR.LmapOk(body, qm) && qm.ov == ov
    requires NR.NfaRepRE(body, code, 0, endl) && |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept)
    ensures PSM.GuardsOkRun(qm, code, LCdn.compile_cdns(body), ov, str)
  {
    var cdns := LCdn.compile_cdns(body);
    QUniqueOfQuantUnique(body);
    CS.TransWfCdnWf(body);
    forall cp: int ensures PSM.GuardsOkAt(qm, code, PSM.CdnAt(cdns, ov, str, cp), str, cp) {
      var table := PSM.CdnAt(cdns, ov, str, cp);
      if 0 <= cp <= |str| {
        var cpn: nat := cp as nat;
        var inp := PIV.InpOfCp(str, cpn);
        PSM.InpOfCpIsInputAt(str, cpn);
        forall pc: nat | NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.CheckNullable?
          ensures PSM.GuardOkBit(qm, table, NR.GetPcRE(code, pc).value.cnq, inp)
        {
          var qid := NR.GetPcRE(code, pc).value.cnq;
          assert NR.GetPcRE(code, pc) == Some(RB.CheckNullable(qid));
          assert pc < endl;   // pc < |code| == endl + 1, and code[endl] is Accept
          GuardIdsRE(body, code, 0, endl, pc);
          assert qid in CS.CdnQIds(body);
          CdnBodyFacts(body, qm, qid);
          var cb := CS.CdnBody(body, qid);
          PIV.QmapOkBodyAtQid(body, qm, qid as nat);
          assert qid in qm.bodies && qm.bodies[qid] == cb;
          assert table == LCdn.build_cdn_v(cdns, cpn, ov, AI.cp_context(cpn, str, LAnc.Forward), LAnc.Forward);
          CS.CheckNullableMeaning(body, str, ov, cpn, LAnc.Forward, qid);
          CTT.FirstEmptyPathRMatchesV(qm, cb, str, cpn);
        }
      }
      PSM.GuardsOkAtIntro(qm, code, table, str, cp);
    }
  }
}
