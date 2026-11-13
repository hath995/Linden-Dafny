// (G3b) The backward row's register lemmas, from the W13 probe: the direction-generic final-registers
// lemma and the true-stamp inventory of the lookbehind capture code `compile(reverse_regex(body))`.
module LindenElkBackRowAt {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import NR = LindenElkNfaRep
  import PIV = LindenElkPikeInv
  import NRR = LindenElkNulledReconRegs
  import FV = LindenElkFinalVm
  import FRD = LindenElkFinalReadout
  import CM = LindenElkClockMono

  lemma FFindMatchRegsFinalAny(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView,
                               dir: LAnc.direction, cdn: LCdn.cdns, Q: set<int>)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires FV.TrueStampsIn(c, Q)
    requires dir.Forward? ==> s.context.nextchar == AI.get_char(str, s.cp)
    requires dir.Backward? ==> s.context.nextchar == AI.get_char(str, s.cp - 1)
    requires 0 <= s.cp <= |str| && s.clock >= 0
    requires FV.VmRegsFinalOk(s, |str|, Q)
    ensures var r := AI.FFindMatch(c, str, s, ov, dir, cdn).0;
      r.Some? ==> FV.RegsFinalOk(r.value, |str|, Q)
    decreases if dir.Forward? then |str| - s.cp else s.cp
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, dir));
    assert FV.VmRegsFinalOk(s0, |str|, Q);
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, dir);
    FV.FAdvanceEpsilonRegsFinal(c, s0, ov, dir, |str|, Q);
    CM.FAdvanceEpsilonClockGrows(c, s0, ov, dir);
    assert FV.VmRegsFinalOk(s1, |str|, Q);
    if |s1.blocked| == 0 { return; }
    match s1.context.nextchar {
      case None =>
      case Some(_) =>
        var s2 := AI.FConsume(s1);
        FV.FConsumeRegsFinal(s1, |str|, Q);
        CM.FConsumeClockSame(s1);
        var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                      cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
        var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
        var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
        if dir.Forward? {
          assert s.cp < |str|;
          assert s4.cp == s.cp + 1;
        } else {
          assert s.cp > 0;
          assert s4.cp == s.cp - 1;
        }
        assert FV.VmRegsFinalOk(s4, |str|, Q);
        FFindMatchRegsFinalAny(c, str, s4, ov1, dir, cdn, Q);
    }
  }
  lemma RevIds(r: R.regex)
    ensures PIV.QuantIds(R.reverse_regex(r)) == PIV.QuantIds(r)
    decreases r
  {
    match r
    case Re_alt(a, b) => RevIds(a); RevIds(b);
    case Re_con(a, b) => RevIds(a); RevIds(b);
    case Re_quant(_, _, _, a) => RevIds(a);
    case Re_capture(_, a) => RevIds(a);
    case Re_lookaround(_, _, a) => RevIds(a);
    case _ =>
  }
  lemma RevQuantUnique(r: R.regex)
    requires PIV.QuantUnique(r)
    ensures PIV.QuantUnique(R.reverse_regex(r))
    decreases r
  {
    match r
    case Re_alt(a, b) => RevIds(a); RevIds(b); RevQuantUnique(a); RevQuantUnique(b);
    case Re_con(a, b) => RevIds(a); RevIds(b); RevQuantUnique(a); RevQuantUnique(b);
    case Re_quant(_, _, _, a) => RevIds(a); RevQuantUnique(a);
    case Re_capture(_, a) => RevQuantUnique(a);
    case Re_lookaround(_, _, a) => RevQuantUnique(a);
    case _ =>
  }
  lemma RevCinPlus(r: R.regex, q: nat)
    requires PIV.QuantUnique(r) && q in PIV.QuantIds(r)
    ensures q in PIV.QuantIds(R.reverse_regex(r))
    ensures NRR.QidCinPlus(R.reverse_regex(r), q) == NRR.QidCinPlus(r, q)
    decreases r
  {
    RevIds(r);
    match r
    case Re_alt(a, b) =>
      RevIds(a); RevIds(b);
      if q in PIV.QuantIds(a) { RevCinPlus(a, q); } else { RevCinPlus(b, q); }
    case Re_con(a, b) =>
      RevIds(a); RevIds(b);
      assert PIV.QuantIds(a) * PIV.QuantIds(b) == {};
      if q in PIV.QuantIds(a) {
        assert q !in PIV.QuantIds(b) by { assert q !in PIV.QuantIds(a) * PIV.QuantIds(b); }
        RevCinPlus(a, q);
      } else {
        RevCinPlus(b, q);
      }
    case Re_quant(_, qid0, _, a) =>
      if qid0 >= 0 && (qid0 as nat) == q {} else { RevCinPlus(a, q); }
    case Re_capture(_, a) => RevCinPlus(a, q);
    case Re_lookaround(_, _, a) => RevCinPlus(a, q);
    case _ =>
  }
  lemma RevCinQids(r: R.regex)
    requires PIV.QuantUnique(r)
    ensures FRD.CinQids(R.reverse_regex(r)) == FRD.CinQids(r)
  {
    RevIds(r);
    forall x | x in FRD.CinQids(R.reverse_regex(r)) ensures x in FRD.CinQids(r) {
      var q: nat :| q in PIV.QuantIds(R.reverse_regex(r)) && NRR.QidCinPlus(R.reverse_regex(r), q) && q as int == x;
      RevCinPlus(r, q);
    }
    forall x | x in FRD.CinQids(r) ensures x in FRD.CinQids(R.reverse_regex(r)) {
      var q: nat :| q in PIV.QuantIds(r) && NRR.QidCinPlus(r, q) && q as int == x;
      RevCinPlus(r, q);
    }
  }
  /** Real world: compile(reverse_regex(body)), the lookbehind capture code. */
  lemma RevTrueStampsCin(body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.QuantUnique(body)
    ensures FV.TrueStampsIn(CP.compile_to_bytecode(R.reverse_regex(body)), FRD.CinQids(body))
  {
    var rb := R.reverse_regex(body);
    NR.ReverseNestedFragmentRE(body);
    NR.CompileToBytecodeRepNested(rb);
    var next := CP.compile(rb, 0, CP.Progress).1;
    RevQuantUnique(body);
    RevCinQids(body);
    FRD.NestedNoCdnPlus(rb);   // (G5a) TrueStampsInCin's premise
    FRD.TrueStampsInCin(rb, CP.compile_to_bytecode(rb), next as nat);
  }}
