// G5, part 2 (W5): the CDN guard in SPEC terms, with no MatchesL.
//
//   table bit  <==>  MatchesV(body, cp, cp)                    (LindenElkCdnSound.CdnSound)
//              <==>  TR.FirstEmptyPathR(qm, body, inp).Some?   (FirstEmptyPathRMatchesV, here)
//              <==>  NP.FirstEmptyPathL(rer, Translate(body), inp).Some?
//                                                              (NPT.FirstEmptyPathRL, existing:
//                                                               needs LmapOk + OracleOkAt only)
//
// `FirstEmptyPathR` is the payload of TreeRepRE's `tr_stamp` rule, so the
// CheckNullable guard is exactly "tr_stamp's precondition holds". OracleOkAt is
// kind-blind (it reads each look's own walk direction), so this route needs
// neither G1(a) nor MatchesVTransfer.
//
// Checked together with CdnSound.dfy against linden-equiv-oracle-entry's deps + .doo.
module LindenElkCdnTreeTie {
  import opened Std.Wrappers
  import R = RegElkRegex
  import C = Cdn
  import LOr = Oracle
  import LAnc = Anchors
  import AI = ArrayInterp
  import ORc = LindenElkOracleReach
  import OBV = LindenElkOracleBridgeV
  import T = LindenElkTranslate
  import LC = Chars
  import LW = WarblreRegExpRecord
  import AR = LindenElkActionsRep
  import TR = LindenElkTreeRep
  import LL = LindenElkLookLeaves
  import NP = LindenElkNulledPlus
  import NPT = LindenElkNulledPlusTie
  import CS = LindenElkCdnSound

  lemma InputAtCtx(str: string, cp: nat)
    requires cp <= |str|
    ensures TR.CpOf(T.InputAt(str, cp)) == cp
    ensures TR.CtxOf(T.InputAt(str, cp)) == ORc.CtxAt(str, cp)
  {
    var inp := T.InputAt(str, cp);
    T.ReverseProps(str[..cp]);
    assert |inp.pref| == cp;
    if cp > 0 { assert inp.pref[0] == str[..cp][cp - 1] == str[cp - 1]; }
    if cp < |str| { assert inp.next[0] == str[cp]; }
  }

  lemma FirstEmptyPathRMatchesV(qm: AR.QMap, re: R.regex, str: string, cp: nat)
    requires T.TransWf(re)
    requires cp <= |str|
    ensures TR.FirstEmptyPathR(qm, re, T.InputAt(str, cp)).Some?
        <==> OBV.MatchesV(re, str, qm.ov, cp, cp)
    decreases re
  {
    CS.TransWfCdnWf(re);
    InputAtCtx(str, cp);
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(a) =>
    case Re_alt(r1, r2) =>
      FirstEmptyPathRMatchesV(qm, r1, str, cp);
      FirstEmptyPathRMatchesV(qm, r2, str, cp);
    case Re_con(r1, r2) =>
      FirstEmptyPathRMatchesV(qm, r1, str, cp);
      FirstEmptyPathRMatchesV(qm, r2, str, cp);
      CS.ConEmptyIff(r1, r2, str, qm.ov, cp);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 {
        var k: nat := 0;
        assert q.min <= k && (q.max.Some? ==> k <= q.max.value)
            && OBV.MatchesIterV(r1, k, str, qm.ov, cp, cp);
      } else {
        FirstEmptyPathRMatchesV(qm, r1, str, cp);
        CS.QuantEmptyIff(nul, qid, q, r1, str, qm.ov, cp);
      }
    case Re_capture(_, r1) =>
      FirstEmptyPathRMatchesV(qm, r1, str, cp);
    case Re_lookaround(lid, lk, r1) =>
  }

  /** TransWf descends to a CDN plus body. */
  lemma TransWfCdnBody(re: R.regex, qid: int)
    requires T.TransWf(re) && qid in CS.CdnQIds(re)
    ensures T.TransWf(CS.CdnBody(re, qid))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => if qid in CS.CdnQIds(r1) { TransWfCdnBody(r1, qid); } else { TransWfCdnBody(r2, qid); }
    case Re_con(r1, r2) => if qid in CS.CdnQIds(r1) { TransWfCdnBody(r1, qid); } else { TransWfCdnBody(r2, qid); }
    case Re_quant(nul, q0, q, r1) =>
      if !(CS.EligibleCdnPlus(nul, q) && q0 == qid) { TransWfCdnBody(r1, qid); }
    case Re_capture(_, r1) => TransWfCdnBody(r1, qid);
    case Re_lookaround(_, _, r1) => TransWfCdnBody(r1, qid);
  }

  /** THE G5 guard meaning, in spec terms, for a scan in EITHER direction:
      the engine's `CheckNullable(qid)` passes at `cp` iff the plus body's
      Linden first empty path exists there — exactly the `tr_stamp` payload. */
  lemma CdnGuardSpec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, str: string, cp: nat,
                     dir: LAnc.direction, qid: int)
    requires !rer.multiline
    requires T.TransWf(re) && CS.QUnique(re)
    requires qid in CS.CdnQIds(re)
    requires cp <= |str|
    requires T.TransWf(CS.CdnBody(re, qid)) ==> AR.LmapOk(CS.CdnBody(re, qid), qm)
    requires LL.OracleOkAt(rer, qm, T.InputAt(str, cp))
    ensures T.TransWf(CS.CdnBody(re, qid))
    ensures C.cdn_get(C.build_cdn_v(C.compile_cdns(re), cp, qm.ov, AI.cp_context(cp, str, dir), dir), qid)
        <==> TR.FirstEmptyPathR(qm, CS.CdnBody(re, qid), T.InputAt(str, cp)).Some?
    ensures C.cdn_get(C.build_cdn_v(C.compile_cdns(re), cp, qm.ov, AI.cp_context(cp, str, dir), dir), qid)
        <==> NP.FirstEmptyPathL(rer, T.Translate(CS.CdnBody(re, qid)), T.InputAt(str, cp)).Some?
  {
    CS.TransWfCdnWf(re);
    TransWfCdnBody(re, qid);
    var body := CS.CdnBody(re, qid);
    CS.CheckNullableMeaning(re, str, qm.ov, cp, dir, qid);
    FirstEmptyPathRMatchesV(qm, body, str, cp);
    NPT.FirstEmptyPathRL(rer, qm, body, T.InputAt(str, cp));
  }
}
