#!/usr/bin/env bash
# regenerate L3aEndpointAssembly from the pre-opaque source: facts, pins, sub-splits, 2 blocks, 2 forall wraps, section splits
set -e; S=$E3_SCRATCH; cd /home/aaron/code/Linden-Dafny
F=linden-equiv-lift-sim-oracle/src/LiftSimOracle.dfy; cp $S/LiftSimOracle.pre-opaque.dfy $F; sed -i 's/lemma {:isolate_assertions} L3aEndpointAssembly(/lemma L3aEndpointAssembly(/' $F
python3 - <<'EOF'
p='linden-equiv-lift-sim-oracle/src/LiftSimOracle.dfy'; L=open(p).read().split('\n')
BUNDLE='''forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
             exists la: R.lookaround, body: R.regex ::
               LTB.LookEntryOk(crv, l, la, body)
               && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
               && PIV.CapUnique(body) && PIV.QuantUnique(body)
               && PIV.CaptureRegs(body) <= Sreg
               && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(ast))
               && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body))'''
c=next(k for k in range(2644,len(L)) if L[k].strip().startswith('M.FLookLoopValueLift(crv, str, 1, maxlook'))
pins='''    // (E3) pins: FLookLoopValueLift's preconditions, one assert each
    assert ncap >= 0 && nlook >= 0 && nquant >= 0;
    assert NR.LookBehindFragmentRE(ast) && PIV.QuantUnique(ast);
    assert (forall k :: AI.get_idx(qtF.a_cp, k) < 0) && (forall k :: AI.get_idx(qtF.a_clk, k) >= -1);
    assert |qtF.a_cp| == nquant && |qtF.a_clk| == nquant;
    assert |thread.capture_regs.a_cp| == ncap && |thread.capture_regs.a_clk| == ncap && PIV.CapRegWf(thread.capture_regs);
    assert |lk.a_cp| == nlook && |lk.a_clk| == nlook;
    assert %s;
    assert forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==> CM.RegsAgreeInside(thread.capture_regs, AReg.init_regs(ncap), PIV.CaptureRegs(M.VBody(crv, l)));
    assert forall l1: int, l2: int :: 1 <= l1 <= maxlook && 1 <= l2 <= maxlook && l1 != l2 && AReg.get_cp(lk, l1).Some? && AReg.get_cp(lk, l2).Some? ==> PIV.CaptureRegs(M.VBody(crv, l1)) * PIV.CaptureRegs(M.VBody(crv, l2)) == {};
    assert forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==> M.cp_ctx_ok(crv, str, lk, l);
    assert {:split_here} true;   // (E3) lifts sub-batch: pins | lifts''' % BUNDLE
L[c:c]=pins.split('\n')
fa=next(k for k in range(c,len(L)) if L[k].strip().startswith('assert forall c: nat :: c in PIV.CapIdsOutsideLooks(re)')); L.insert(fa, '    assert {:split_here} true;   // (E3) lifts sub-batch: lifts | frame asserts')
m=next(k for k in range(2644, len(L)) if '---- run the lifts' in L[k])
facts='''    // (E3) exported facts for the lifts/FORWARD/REVERSE sections (lemma posts + call-site preconditions)
    assert NR.LookBehindFragmentRE(ast) && PIV.QuantUnique(ast);
    assert PIV.CapIds(re) == PIV.CapIdsOutsideLooks(re) + PIV.CapIdsInLooks(re);
    assert PIV.CapIdsOutsideLooks(re) * PIV.CapIdsInLooks(re) == {};
    assert PIV.QuantIdsOutsideLooks(re) * PIV.QuantIdsInLooks(re) == {};
    assert forall l: int :: 0 <= l < nlook && AReg.get_cp(lk, l).Some? ==> 1 <= l <= maxlook && (l as nat) in LTB.LookIds(re);
    assert forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==> M.cp_ctx_ok(crv, str, lk, l);
    assert %s;
    // (E3) the two-lid capture-register disjointness (FLookLoopValueLift's precondition), proved once here
    forall l1: int, l2: int |
      1 <= l1 <= maxlook && 1 <= l2 <= maxlook && l1 != l2
      && AReg.get_cp(lk, l1).Some? && AReg.get_cp(lk, l2).Some?
      ensures PIV.CaptureRegs(M.VBody(crv, l1)) * PIV.CaptureRegs(M.VBody(crv, l2)) == {}
    {
      assert (l1 as nat) in LTB.LookIds(re) && (l2 as nat) in LTB.LookIds(re);
      OE.LmOfDom(re);
      assert l1 in OE.LmOf(re) && l2 in OE.LmOf(re);
      var la1, b1, la2, b2 := M.LmOfBodiesDisjoint(re, crv, l1, l2);
      assert b1 == M.VBody(crv, l1) && b2 == M.VBody(crv, l2);
      PIV.CaptureRegsDisjoint(b1, b2);
    }''' % BUNDLE
L[m:m]=facts.split('\n')
for k in sorted([2707,2734,2765,2783,2819,2850], reverse=True):
    assert L[k-1].startswith('    assert') or L[k-1].startswith('    forall'), (k, L[k-1][:60]); L.insert(k-1, '    assert {:split_here} true;   // (E3) section-1 sub-batch')
open(p,'w').write('\n'.join(L)); print('L3a source prepped')
EOF
$S/venv/bin/python $S/e3opaque.py $F L3aEndpointAssembly '---- run the lifts' --export-forall --apply | tail -1
$S/venv/bin/python $S/e3opaque.py $F L3aEndpointAssembly '---- FORWARD' --from '---- run the lifts' --export-forall --apply | tail -1
python3 - <<'EOF'
p='linden-equiv-lift-sim-oracle/src/LiftSimOracle.dfy'; L=open(p).read().split('\n')
def wrap(hdr, ens):
    i=next(k for k,l in enumerate(L) if l.startswith(hdr)); j=next(k for k in range(i+1,len(L)) if L[k]=='    }')
    body=['  '+l if l else l for l in L[i:j+1]]; L[i:j+1]=['    opaque']+['      '+e for e in ens]+['    {']+body+['    }']
wrap('    forall g: LG.GroupId | g in S && g in leafgm', ['ensures forall g: LG.GroupId :: g in S && g in leafgm ==>','          g in PIV.GmOfLive(re, res0, lk, res2)','          && leafgm[g] == PIV.NormRange(PIV.GmOfLive(re, res0, lk, res2)[g])'])
wrap('    forall g: LG.GroupId | g in S && g in PIV.GmOfLive(re, res0, lk, res2)', ['ensures forall g: LG.GroupId :: g in S && g in PIV.GmOfLive(re, res0, lk, res2) ==> g in leafgm'])
open(p,'w').write('\n'.join(L)); print('wrapped 2 foralls')
EOF
python3 $S/splits.py $F 2640 3520 4
cd linden-equiv-lift-sim-oracle; LIBS=$(for d in deps/*.doo; do printf -- '--library=%s ' $d; done); timeout 900 dafny resolve --standard-libraries $LIBS src/LiftSimOracle.dfy 2>&1 | grep -v '^$' | tail -1 | cut -c1-120
