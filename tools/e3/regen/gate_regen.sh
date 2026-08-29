#!/usr/bin/env bash
set -e; S=$E3_SCRATCH; cd /home/aaron/code/Linden-Dafny
G=linden-equiv-lift-sim-gate/src/LiftSimGate.dfy; cp $S/LiftSimGate.pre-opaque.dfy $G; sed -i '2246s/lemma {:isolate_assertions} LiftPreserveGatePassLk(/lemma LiftPreserveGatePassLk(/' $G
python3 - <<'EOF'
p='linden-equiv-lift-sim-gate/src/LiftSimGate.dfy'; L=open(p).read().split('\n')
i=next(k for k in range(2490,2510) if L[k].strip()=='LkResultAgreeOutside(rer, lk, r1, inp, tlk, gm);'); L.insert(i+1, '    assert LL.GmAgreeOutside(gm2, gm, set g | g in L.DefGroups(r1));   // (E3) exported: the agree-outside post (gm only grows)')
i=next(k for k in range(2480,2512) if L[k].strip()=='var LB := NI.LookBodyOfRE(re, l as nat);'); L.insert(i, '    assert l >= 0 && (l as nat) in LTB.LookIds(re);   // (E3) exported: LookBodyOfRE(re, l) is well-formed in the residual')
i=next(k for k in range(2480,2514) if L[k].strip()=='assert r1 == T.Translate(LB);'); L.insert(i, '    assert T.TransWf(LB);   // (E3) exported: Translate(LB) is well-formed in the residual')
i=next(k for k in range(2360,2375) if L[k].startswith('    if la.Lookahead? {')); L.insert(i,'    // ---- (E3) the gate case split ----'); open(p,'w').write('\n'.join(L)); print('gate source prepped')
EOF
$S/venv/bin/python $S/e3opaque.py $G LiftPreserveGatePassLk '---- (E3) the gate case split' --export-forall --export-all --types 'gm:LG.GroupMap;gm2:LG.GroupMap;ta:seq<(LT.Tree, LG.GroupMap)>' --apply | tail -1
$S/venv/bin/python $S/e3opaque.py $G LiftPreserveGatePassLk '---- (E4) converse' --from '---- (E3) the look-path carrier' --export-forall --export-all --apply | tail -1
sed -i 's/ensures (bst == PTS(inp, ta, best, tbl, seen))/ensures (bst == PT.PTS(inp, ta, best, tbl, seen))/' $G; python3 $S/splits.py $G 2246 2900 4
cd linden-equiv-lift-sim-gate; LIBS=$(for d in deps/*.doo; do printf -- '--library=%s ' $d; done); timeout 600 dafny resolve --standard-libraries $LIBS src/LiftSimGate.dfy 2>&1 | grep -v '^$' | tail -1 | cut -c1-120
