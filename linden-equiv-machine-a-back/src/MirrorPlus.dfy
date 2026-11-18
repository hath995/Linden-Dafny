// G3b probe (2026-11-12): the mirrored plus table and the gate's FXR invariance.
module LindenElkMirrorPlus {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import NR = LindenElkNfaRep
  import PIV = LindenElkPikeInv
  import FST = LindenElkFlipStatics
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import RF = LindenElkReconFrame
  import W = LindenElkBackRowResidue
  import T = LindenElkTranslate
  import FG = LindenElkFlipGate
  import CMr = LindenElkCdnMirror   // (G4b-1b) NullableFXR

  lemma FlattenNonEmpty(t: CP.treelist, tail: seq<RB.instruction>)
    requires |tail| >= 1
    ensures |CP.tl_flatten(t, tail)| >= 1
    decreases t
  {
    match t
    case Leaf(l) =>
    case Concat(a, b) => FlattenNonEmpty(b, tail); FlattenNonEmpty(a, CP.tl_flatten(b, tail));
  }
  lemma ReconNonEmpty(r: R.regex)
    ensures |CP.compile_reconstruct_nulled(r)| >= 1
  {
    FlattenNonEmpty(CP.compile(r, 0, CP.ReconstructNulled).0, [RB.Accept]);
  }

  /** One entry of the flipped world's plus table. */
  ghost function MirrorPlusAt(host: R.regex, plus: seq<RB.code>, q: nat): RB.code
    requires q < |plus|
  {
    if q in PIV.QuantIds(FST.FXR(host)) && NRR.QidCinPlus(FST.FXR(host), q)
    then CP.compile_reconstruct_nulled(PIV.QidBody(FST.FXR(host), q)) else plus[q]
  }
  /** The plus table of the flipped world: correct for `FXR(host)` on its quantifiers, the real
      table elsewhere. */
  ghost function MirrorPlus(host: R.regex, plus: seq<RB.code>): seq<RB.code> {
    seq(|plus|, q requires 0 <= q < |plus| => MirrorPlusAt(host, plus, q))
  }

  lemma PlusTableOkMirror(host: R.regex, plus: seq<RB.code>)
    requires PIV.QuantUnique(host) && NRR.PlusTableOk(host, plus)
    ensures NRR.PlusTableOk(FST.FXR(host), MirrorPlus(host, plus))
  {
    var hF := FST.FXR(host);
    var pF := MirrorPlus(host, plus);
    W.IdsFXR(host);
    forall q: nat | q in PIV.QuantIds(hF)
      ensures AI.get_code_v(pF, q as int)
           == (if NRR.QidCinPlus(hF, q) then CP.compile_reconstruct_nulled(PIV.QidBody(hF, q)) else [])
    {
      W.PathsFXR(host, [], [], -1, q);
      var e := AI.get_code_v(plus, q as int);
      assert e == (if NRR.QidCinPlus(host, q) then CP.compile_reconstruct_nulled(PIV.QidBody(host, q)) else []);
      ReconNonEmpty(PIV.QidBody(host, q));
      hide *;
      reveal AI.get_code_v, MirrorPlus, MirrorPlusAt;
      if NRR.QidCinPlus(hF, q) {
        assert |e| >= 1;
        assert 0 <= (q as int) < |plus|;
        assert pF[q] == MirrorPlusAt(host, plus, q);
      } else {
        if 0 <= (q as int) < |plus| { assert pF[q] == MirrorPlusAt(host, plus, q); }
      }
    }
  }

  lemma LookFreeFXR(r: R.regex)
    requires NR.LookFreeRE(r)
    ensures NR.LookFreeRE(FST.FXR(r))
    decreases r
  {
    match r
    case Re_alt(a, b) => W.FXRAlt(a, b); LookFreeFXR(a); LookFreeFXR(b);
    case Re_con(a, b) => W.FXRCon(a, b); LookFreeFXR(a); LookFreeFXR(b);
    case Re_quant(nul, qid, q, a) => W.FXRQuant(nul, qid, q, a); LookFreeFXR(a);
    case Re_capture(c, a) => W.FXRCap(c, a); LookFreeFXR(a);
    case Re_lookaround(_, _, _) =>
    case Re_anchor(x) => W.FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }

  lemma NoCdnPlusFXR(r: R.regex)
    requires NRC.NoCdnPlusRE(r)
    ensures NRC.NoCdnPlusRE(FST.FXR(r))
    decreases r
  {
    match r
    case Re_alt(a, b) => W.FXRAlt(a, b); NoCdnPlusFXR(a); NoCdnPlusFXR(b);
    case Re_con(a, b) => W.FXRCon(a, b); NoCdnPlusFXR(a); NoCdnPlusFXR(b);
    case Re_quant(nul, qid, q, a) => W.FXRQuant(nul, qid, q, a); NoCdnPlusFXR(a);
    case Re_capture(c, a) => W.FXRCap(c, a); NoCdnPlusFXR(a);
    case Re_lookaround(l, la, a) => W.FXRLook(l, la, a); NoCdnPlusFXR(a);
    case Re_anchor(x) => W.FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }

  lemma CinBodiesLookFreeFXR(r: R.regex)
    requires RF.CinBodiesLookFreeRE(r)
    ensures RF.CinBodiesLookFreeRE(FST.FXR(r))
    decreases r
  {
    match r
    case Re_alt(a, b) => W.FXRAlt(a, b); CinBodiesLookFreeFXR(a); CinBodiesLookFreeFXR(b);
    case Re_con(a, b) => W.FXRCon(a, b); CinBodiesLookFreeFXR(a); CinBodiesLookFreeFXR(b);
    case Re_quant(nul, qid, q, a) =>
      W.FXRQuant(nul, qid, q, a); CinBodiesLookFreeFXR(a);
      if q.min != 0 && q.max == None && nul == R.CINullable && q.greedy { LookFreeFXR(a); }
    case Re_capture(c, a) => W.FXRCap(c, a); CinBodiesLookFreeFXR(a);
    case Re_lookaround(l, la, a) => W.FXRLook(l, la, a); CinBodiesLookFreeFXR(a);
    case Re_anchor(x) => W.FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }

  // ===========================================================================
  // (G5b-2, N4) The flipped plus table on the stamp pluses: a CDN plus is stamped too.
  // ===========================================================================

  ghost function MirrorPlusAtS(host: R.regex, plus: seq<RB.code>, q: nat): RB.code
    requires q < |plus|
  {
    if q in PIV.QuantIds(FST.FXR(host)) && NRR.QidStampPlus(FST.FXR(host), q)
    then CP.compile_reconstruct_nulled(PIV.QidBody(FST.FXR(host), q)) else plus[q]
  }
  /** `MirrorPlus` keyed on `QidStampPlus`. */
  ghost function MirrorPlusS(host: R.regex, plus: seq<RB.code>): seq<RB.code> {
    seq(|plus|, q requires 0 <= q < |plus| => MirrorPlusAtS(host, plus, q))
  }

  lemma PlusTableOkSMirror(host: R.regex, plus: seq<RB.code>)
    requires PIV.QuantUnique(host) && NRR.PlusTableOkS(host, plus)
    ensures NRR.PlusTableOkS(FST.FXR(host), MirrorPlusS(host, plus))
  {
    var hF := FST.FXR(host);
    var pF := MirrorPlusS(host, plus);
    W.IdsFXR(host);
    forall q: nat | q in PIV.QuantIds(hF)
      ensures AI.get_code_v(pF, q as int)
           == (if NRR.QidStampPlus(hF, q) then CP.compile_reconstruct_nulled(PIV.QidBody(hF, q)) else [])
    {
      W.PathsFXR(host, [], [], -1, q);
      var e := AI.get_code_v(plus, q as int);
      assert e == (if NRR.QidStampPlus(host, q) then CP.compile_reconstruct_nulled(PIV.QidBody(host, q)) else []);
      ReconNonEmpty(PIV.QidBody(host, q));
      hide *;
      reveal AI.get_code_v, MirrorPlusS, MirrorPlusAtS;
      if NRR.QidStampPlus(hF, q) {
        assert |e| >= 1;
        assert 0 <= (q as int) < |plus|;
        assert pF[q] == MirrorPlusAtS(host, plus, q);
      } else {
        if 0 <= (q as int) < |plus| { assert pF[q] == MirrorPlusAtS(host, plus, q); }
      }
    }
  }

  /** (G5b-2) `CinBodiesLookFreeFXR` on the stamp bodies. */
  lemma StampBodiesLookFreeFXR(r: R.regex)
    requires RF.StampBodiesLookFreeRE(r)
    ensures RF.StampBodiesLookFreeRE(FST.FXR(r))
    decreases r
  {
    match r
    case Re_alt(a, b) => W.FXRAlt(a, b); StampBodiesLookFreeFXR(a); StampBodiesLookFreeFXR(b);
    case Re_con(a, b) => W.FXRCon(a, b); StampBodiesLookFreeFXR(a); StampBodiesLookFreeFXR(b);
    case Re_quant(nul, qid, q, a) =>
      W.FXRQuant(nul, qid, q, a); StampBodiesLookFreeFXR(a);
      if q.min != 0 && q.max == None && nul != R.NonNullable && q.greedy { LookFreeFXR(a); }
    case Re_capture(c, a) => W.FXRCap(c, a); StampBodiesLookFreeFXR(a);
    case Re_lookaround(l, la, a) => W.FXRLook(l, la, a); StampBodiesLookFreeFXR(a);
    case Re_anchor(x) => W.FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }

  /** (G4b-1b) The empty-path look scope is FXR-invariant (`R.nullable` is, `CMr.NullableFXR`). */
  lemma EPCFFXR(r: R.regex)
    requires RF.EmptyPathLooksCapFree(r)
    ensures RF.EmptyPathLooksCapFree(FST.FXR(r))
    decreases r
  {
    match r
    case Re_alt(a, b) => W.FXRAlt(a, b); EPCFFXR(a); EPCFFXR(b);
    case Re_con(a, b) =>
      W.FXRCon(a, b); CMr.NullableFXR(a); CMr.NullableFXR(b);
      if RF.MayNull(a) { EPCFFXR(b); }
      if RF.MayNull(b) { EPCFFXR(a); }
    case Re_quant(nul, qid, q, a) => W.FXRQuant(nul, qid, q, a); if q.min != 0 { EPCFFXR(a); }
    case Re_capture(c, a) => W.FXRCap(c, a); EPCFFXR(a);
    case Re_lookaround(l, la, a) => W.FXRLook(l, la, a); W.IdsFXR(a);
    case Re_anchor(x) => W.FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }

  /** (G5b-3, G4b-1b) `StampBodiesLookFreeFXR` on the stamp scope. */
  lemma StampLooksCapFreeFXR(r: R.regex)
    requires RF.StampLooksCapFreeRE(r) && T.TransWf(r)
    ensures RF.StampLooksCapFreeRE(FST.FXR(r))
    decreases r
  {
    match r
    case Re_alt(a, b) => W.FXRAlt(a, b); StampLooksCapFreeFXR(a); StampLooksCapFreeFXR(b);
    case Re_con(a, b) => W.FXRCon(a, b); StampLooksCapFreeFXR(a); StampLooksCapFreeFXR(b);
    case Re_quant(nul, qid, q, a) =>
      W.FXRQuant(nul, qid, q, a); StampLooksCapFreeFXR(a);
      if RF.StampNode(nul, q) { EPCFFXR(a); }
    case Re_capture(c, a) => W.FXRCap(c, a); StampLooksCapFreeFXR(a);
    case Re_lookaround(l, la, a) => W.FXRLook(l, la, a); StampLooksCapFreeFXR(a);
    case Re_anchor(x) => W.FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }
}
