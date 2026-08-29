import sys
CALL="""LookNestBackTFromBodyReplay(rer, qmB, laA, host, bodycode, endlH, 0, crv, str, cpA, ov,
                                  cdnA, crv.f_plus_bc, ncap, nlook, nquant);"""
def patch(p):
    s=open(p).read(); i=s.index('ForwardFindRecFwdDeep('); j=s.index('\n  lemma', i); body=s[i:j]
    old1="""    LookNestBackTFromBodyReplay(rer, qmB, laA, host, bodycode, endlH, 0, crv, str, cpA, ov,
                                cdnA, crv.f_plus_bc, ncap, nlook, nquant);
    var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(host))], inpA, LG.Empty, WP.Forward);
    var rfP := AI.FFindMatchPlus(bodycode, host, crv.f_plus_bc, str, ov, LAnc.Forward, cpA,
                                 AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                 0, cdnA).0;
"""
    new1="""    var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(host))], inpA, LG.Empty, WP.Forward);
    var rfP := AI.FFindMatchPlus(bodycode, host, crv.f_plus_bc, str, ov, LAnc.Forward, cpA,
                                 AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                 0, cdnA).0;
    // (2026-08-29 proof-engineering) the forward carrier's three quantified predicates are kept OUT of
    // the context: each use below re-invokes the carrier inside an `assert … by {}` exposing only the
    // instance it needs. Here: the None-iff + the clock invariants of the fresh run.
    assert (rfP.Some? <==> LT.FirstLeaf(t, inpA).Some?)
        && (rfP.Some? ==> CM.LookClkSetWithCp(rfP.value.look_regs) && CM.LookCpSetWithClk(rfP.value.look_regs)
                          && CM.LookCpsLE(rfP.value.look_regs, |str|)) by {
      %s
    }
""" % CALL
    assert body.count(old1)==1; body=body.replace(old1,new1)
    old2="""    // (a) the FORWARD carrier at A1 (leaf-witness g): crossed + dominant on rf_A
    assert LookNestOkTTop(host, Sh, gmtH, rfA);
    assert g in Sh && g in gmtH && g in PIV.CapIds(NI.LookBodyOfRE(host, A1));
    assert NI.LookPathPresent(host, rfA.capture_regs.a_clk, rfA.quant_regs.a_clk, -1, A1)
           && AI.get_idx(rfA.look_regs.a_clk, A1 as int) >= 0
           && AI.get_idx(rfA.look_regs.a_clk, A1 as int)
              >= NI.MxAtLidLk(host, rfA.quant_regs.a_clk, -1, A1);
"""
    new2="""    // (a) the FORWARD carrier at A1 (leaf-witness g): crossed + dominant on rf_A — the
    //     `LookNestOkTTop` instance at A1, with the quantified carrier scoped to this block
    assert g in Sh && g in gmtH && g in PIV.CapIds(NI.LookBodyOfRE(host, A1));
    assert NI.LookPathPresent(host, rfA.capture_regs.a_clk, rfA.quant_regs.a_clk, -1, A1)
           && AI.get_idx(rfA.look_regs.a_clk, A1 as int) >= 0
           && AI.get_idx(rfA.look_regs.a_clk, A1 as int)
              >= NI.MxAtLidLk(host, rfA.quant_regs.a_clk, -1, A1) by {
      %s
      assert LookNestOkTTop(host, Sh, gmtH, rfA);
    }
""" % CALL
    assert body.count(old2)==1; body=body.replace(old2,new2)
    old3="""    assert LookNestBackTTopDeep(rer, host, crv, str, ov, Sh, gmtH, rfA, ncap, nlook, nquant);
    assert g in lsub1rf.value && gmtH[g] == lsub1rf.value[g] by {
      assert g in gmtH;
    }
"""
    new3="""    assert g in lsub1rf.value && gmtH[g] == lsub1rf.value[g] by {   // the deep carrier's instance at A1, scoped
      %s
      assert LookNestBackTTopDeep(rer, host, crv, str, ov, Sh, gmtH, rfA, ncap, nlook, nquant);
      assert g in gmtH;
    }
""" % CALL
    assert body.count(old3)==1; body=body.replace(old3,new3)
    assert body.count('LookNestBackTFromBodyReplay(')==3
    open(p,'w').write(s[:i]+body+s[j:]); print(p.split('/')[-1], 'FwdDeep patched')
for p in sys.argv[1:]: patch(p)
