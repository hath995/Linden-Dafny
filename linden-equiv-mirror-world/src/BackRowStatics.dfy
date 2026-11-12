// W13: the statics machine A needs at FXR(body) WITH a nulled plus in body.
// `FK.FlipXRevStaticOkNested` minus its one `NoNulledPlusRE` premise, ensuring
// the gate-free package `PSM.StaticCoreNestedRE` (PikeSimRE.dfy:6145) that
// `PSM.FindMatchSimRENested` (:4754) already takes. Same proof, minus one
// premise and the `FST.NoNulledPlusFXR` call.
module LindenElkBackRowStatics {
  import opened Std.Wrappers
  import NUL = LindenElkNullable
  import R = RegElkRegex
  import LCdn = Cdn
  import CP = Compiler
  import LOr = Oracle
  import NR = LindenElkNfaRep
  import T = LindenElkTranslate
  import PIV = LindenElkPikeInv
  import AR = LindenElkActionsRep
  import PSM = LindenElkPikeSim
  import LTB = LindenElkLookTables
  import OE = LindenElkOracleEntry
  import M = LindenElkMain
  import FST = LindenElkFlipStatics

  lemma FlipXRevStaticCoreNested(body: R.regex, someView: LOr.OracleView,
                                 ncap: int, nlook: int, nquant: int)
      returns (qm'': AR.QMap, endl': nat)
    requires T.TransWf(body) && NR.NestedFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    ensures PSM.StaticCoreNestedRE(qm'', FST.FXR(body), CP.compile_to_bytecode(FST.FXR(body)), endl')
    ensures PSM.SizesOkRE(FST.FXR(body), ncap, nlook, nquant)
    ensures qm''.ov == someView && qm''.looks == FST.FlipLooksMap(OE.LmOf(body))
    ensures qm''.bodies == M.BodiesOfRE(FST.FXR(body))
  {
    var re' := FST.FXR(body);
    FST.FXRStructural(body);
    qm'' := AR.QMap(M.QmOfRE(re'), FST.FlipLooksMap(OE.LmOf(body)), someView, M.BodiesOfRE(re'));
    M.QmOfREEntries(re');
    M.BodiesOfREEntries(re');
    M.QmapOkFromEntries(re', qm'');
    var qmB := AR.QMap(map[], OE.LmOf(body), someView, map[]);
    OE.LmapOkOfLmOf(body, qmB);
    FST.LmapOkFlipXRev(body, qmB, qm'');
    endl' := FST.FXRCompileFacts(body);
  }

  /** Anti-vacuity: the premises admit a nulled plus, `(?:())+` (no NoNulledPlusRE). */
  lemma NulledPlusAdmitted()
    ensures var b := R.Re_quant(R.CINullable, 0, R.CountedQuant(1, None, true), R.Re_capture(1, R.Re_empty));
            NR.NestedFragmentRE(b) && !NR.NoNulledPlusRE(b)
  {
    var b := R.Re_quant(R.CINullable, 0, R.CountedQuant(1, None, true), R.Re_capture(1, R.Re_empty));
    assert R.nullable(R.Re_capture(1, R.Re_empty)) == R.CINullable;
    assert !NUL.NoNulledPlusRE_(b);
  }

  /** Anti-vacuity for `LindenElkBackRowPremises.RowPremisesLB`: W1's `RowOk` asks for empty
      cdn lists on both sides, and `compile_cdns` collects only CDN-nullable
      pluses, so a nulled-plus body passes; it also has every structural fact
      the transports use. */
  lemma NulledPlusRowOkCdns()
    ensures var b := R.Re_quant(R.CINullable, 0, R.CountedQuant(1, None, true), R.Re_capture(1, R.Re_empty));
            LCdn.compile_cdns(b) == [] && LCdn.compile_cdns(FST.FXR(b)) == []
            && T.TransWf(b) && PIV.CapUnique(b) && PIV.QuantUnique(b)
            && NR.NestedFragmentRE(b) && !NR.NoNulledPlusRE(b)
  {
    var b := R.Re_quant(R.CINullable, 0, R.CountedQuant(1, None, true), R.Re_capture(1, R.Re_empty));
    assert FST.FXR(b) == b;
    NulledPlusAdmitted();
  }
}
