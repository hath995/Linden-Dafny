#!/usr/bin/env bash
set -e; S=$E3_SCRATCH; cd /home/aaron/code/Linden-Dafny
D=linden-equiv-lift-sim-forward/src/LiftSimForward.dfy; cp $S/LiftSimForward.pre-opaque.dfy $D
$S/venv/bin/python $S/e3opaque.py $D ForwardFindRecLBDeep '==== DEEP: descend' --export-forall --defs-first --apply | tail -1
$S/venv/bin/python $S/e3opaque.py $D ForwardFindRecLBDeep '(c) LEVEL-LINK' --from '==== DEEP: descend' --export-forall --export-all --apply | tail -1
$S/venv/bin/python $S/e3opaque.py $D ForwardFindRecLBDeep '(f) the value chain' --from '(c) LEVEL-LINK' --export-forall --defs-first --apply | tail -1
python3 $S/splits.py $D 121 800 4
python3 - <<'EOF'
p='linden-equiv-lift-sim-forward/src/LiftSimForward.dfy'; L=open(p).read().split('\n')
pins='''      // (E3) pins: the LB carrier's preconditions, one assert each
      assert laA.Lookbehind?;
      assert T.TransWf(host); assert NR.NestedFragmentRE(host); assert NR.NegLooksLookFreeRE(host);
      assert FST.LBOnlyLooksRE(host);
      assert PIV.CapUnique(host) && PIV.QuantUnique(host) && LTB.LookUnique(host);
      assert PSM.SizesOkRE(host, ncap, nlook, nquant);
      assert !rer.ignoreCase && !rer.multiline;
      assert cpA <= |str| && |ov| == |str| + 1;
      assert bodycodeB == CP.compile_to_bytecode(R.reverse_regex(host));
      assert qmB.ov == ov; assert AR.LmapOk(host, qmB); assert OE.OracleColsOk(rer, qmB, str);
      assert LTB.LookTablesOk(host, crv) && |crv.f_look_types| == |crv.f_look_ast|;
      assert forall l: nat :: l in LTB.LookIds(host) ==> l < nlook;'''
i=next(k for k,l in enumerate(L) if k>380 and l.strip().startswith('// (a) the FORWARD carrier at A1')); L[i:i]=pins.split('\n')
j=next(k for k,l in enumerate(L) if k>i and l.strip().startswith('// (b) the')); L.insert(j, '      assert {:split_here} true;   // (E3) block-2 sub-batch: (a) | (b)')
# one sub-batch per heavy obligation inside block 2
heads=['assert M.MatchedPosLA(crv, rfA.look_regs, A1 as int) by {', 'assert ctxB.nextchar == AI.get_char(str, cpA);', 'M.NoWriteOracleBodyCodeNested(R.reverse_regex(host));', 'CM.FFindMatchLookOracleTrueB(bodycodeB, str, initsB, ov, LAnc.Backward, cdnA);', 'assert LT.FirstLeaf(t1, inp1).Some? by {', 'assert lsub1rf.Some? && lsub1rf.value == LT.FirstLeaf(t1, inp1).value.1 by {', 'assert g in lsub1rf.value && gmtH[g] == lsub1rf.value[g] by {']
idx=[k for k,l in enumerate(L) if k>i and any(l.strip().startswith(h) for h in heads)]
for k in sorted(idx, reverse=True): L.insert(k, '      assert {:split_here} true;   // (E3) block-2 sub-batch (heavy obligation)')
open(p,'w').write('\n'.join(L)); print('pins + sub-splits', 1+len(idx))
EOF
cd linden-equiv-lift-sim-forward; LIBS=$(for d in deps/*.doo; do printf -- '--library=%s ' $d; done); timeout 600 dafny resolve --standard-libraries $LIBS src/LiftSimForward.dfy 2>&1 | grep -v '^$' | tail -1 | cut -c1-120
