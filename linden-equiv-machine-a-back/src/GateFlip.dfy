// (G3b) The uniform plus gate (`M.LookBodiesPlusGateRE`: every look body, of either kind, in the CIN
// fragment) is flip-invariant, and the CIN fragment of the whole regex implies it (by the peer session).
module LindenElkGateFlip {
  import R = RegElkRegex
  import M = LindenElkMain
  import NRC = LindenElkNulledRecon
  import RF = LindenElkReconFrame
  import NR = LindenElkNfaRep
  import FRD = LindenElkFinalReadout
  import FST = LindenElkFlipStatics
  import TB = LindenElkMirrorPlus
  import W = LindenElkBackRowResidue

  /** It is flip-invariant. */
  lemma GateFXR(r: R.regex)
    requires M.LookBodiesPlusGateRE(r)
    ensures M.LookBodiesPlusGateRE(FST.FXR(r))
    decreases r
  {
    match r
    case Re_alt(a, b) => W.FXRAlt(a, b); GateFXR(a); GateFXR(b);
    case Re_con(a, b) => W.FXRCon(a, b); GateFXR(a); GateFXR(b);
    case Re_quant(nul, qid, q, a) => W.FXRQuant(nul, qid, q, a); GateFXR(a);
    case Re_capture(c, a) => W.FXRCap(c, a); GateFXR(a);
    case Re_lookaround(l, la, a) =>
      W.FXRLook(l, la, a); GateFXR(a); TB.CinBodiesLookFreeFXR(a);
      if NRC.PositiveLk(la) { TB.NoCdnPlusFXR(a); }   // (G5b) the gate keeps only positive bodies CDN-free
    case Re_anchor(x) => W.FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }
  /** The top level: the CIN fragment of the whole regex gives the gate (`Supported` needs no gate conjunct). */
  lemma GateFromCin(re: R.regex)
    requires NRC.NoCdnPlusRE(re) && RF.CinBodiesLookFreeRE(re)
    ensures M.LookBodiesPlusGateRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => GateFromCin(r1); GateFromCin(r2);
    case Re_con(r1, r2) => GateFromCin(r1); GateFromCin(r2);
    case Re_quant(_, _, _, r1) => GateFromCin(r1);
    case Re_capture(_, r1) => GateFromCin(r1);
    case Re_lookaround(_, _, r1) => GateFromCin(r1);
    case _ =>
  }

  /** (G5a-1 step 4) A look-free regex passes the look-bodies gate vacuously. */
  lemma LookFreeGate(re: R.regex)
    requires NR.LookFreeRE(re)
    ensures M.LookBodiesPlusGateRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookFreeGate(r1); LookFreeGate(r2);
    case Re_con(r1, r2) => LookFreeGate(r1); LookFreeGate(r2);
    case Re_quant(_, _, _, r1) => LookFreeGate(r1);
    case Re_capture(_, r1) => LookFreeGate(r1);
    case _ =>
  }

}
