#!/usr/bin/env python3
"""e2split.py FILE.dfy OUTDIR [--apply] — split module LindenElkLiftSim into level-band modules.
Reads FILE.ts.json (from e2ts.py). Bands: contiguous dependency-level ranges (a DAG by construction)."""
import json, sys, os, collections, re
F=sys.argv[1]; OUT=sys.argv[2]; d=json.load(open(F+'.ts.json')); L=open(F).read().split('\n')
BANDS=[('Core',0,1,4),('Oracle',2,3,4),('Chain',4,9,4),('Gate',10,14,4),('Carriers',15,16,4),('Deep',17,17,4),('Forward',18,18,2),('Main',19,99,4)]
known={'ForwardFindRecLBDeep':1140,'ForwardFindRecFwdDeep':1140,'ForwardFindRecLBBase':600,'ForwardFindRecFwdBase':600,'ForwardFindRecLB':300,'ForwardFindRec':300,'DeepFindRecLB':480,'DeepFindRecFwdDeep':500,'DeepFindRecFwdBase':200,'DeepFindRec':300,'LiftPreserveGatePassLkRec':260,'MainTheoremL5':300,'MainTheoremL4DeepConclude':300,'ReverseCDeepFull':300,'ForwardMemberOne':400,'LookNestBackTFromBodyReplayLB':900,'LookNestBackTFromBodyReplay':300,'LookNestOkTFromBodyReplay':200,'ActionsTreeRepLkFRec':1300,'OracleOkRowsL5':400,'L3aEndpointAssemblyNestedFull2':200,'FreshWfGIndep':200,'ProduceOwnerForall':300,'MainTheoremL3':600}
items=sorted(d['items'], key=lambda x:x['line'])
# recompute levels: longest path over the SCC condensation (Kahn), robust
refs={it['name']:set(it['refs']) for it in items}; comp={it['name']:it['scc'] for it in items}
cnodes=collections.defaultdict(set); cedges=collections.defaultdict(set)
for it in items: cnodes[it['scc']].add(it['name'])
for a,bs in refs.items():
    for b in bs:
        if comp[a]!=comp[b]: cedges[comp[b]].add(comp[a])   # b (dep) -> a (dependent)
indeg=collections.Counter()
for b,dsts in cedges.items():
    for a in dsts: indeg[a]+=1
clevel={c:0 for c in cnodes}; q=[c for c in cnodes if indeg[c]==0]; seen=0
while q:
    c=q.pop(); seen+=1
    for a in cedges[c]:
        clevel[a]=max(clevel[a],clevel[c]+1); indeg[a]-=1
        if indeg[a]==0: q.append(a)
assert seen==len(cnodes), 'cycle in condensation?!'
for it in items: it['level']=clevel[it['scc']]
hist=collections.Counter(it['level'] for it in items); print('levels recomputed:', dict(sorted(hist.items())))
def band_of(lv):
    for i,(n,a,b,c) in enumerate(BANDS):
        if a<=lv<=b: return i
    raise SystemExit('no band for level %d'%lv)
for it in items: it['band']=band_of(it['level']); it['cost']=known.get(it['name'], 0.2*(it['end']-it['line']+1) if it['kind']=='method_decl' else 1)
# sanity: every ref must be in the same or a lower band
byname={it['name']:it for it in items}
bad=[(it['name'],r) for it in items for r in it['refs'] if byname[r]['band']>it['band']]
assert not bad, bad[:5]
mod=d['module']; modline=d['header_end_line']   # 0-based index of the `module` line
header=L[:modline]
print('%-9s %5s %5s %8s  %s' % ('band','decls','lemma','est.min','biggest'))
for i,(n,a,b,c) in enumerate(BANDS):
    xs=[it for it in items if it['band']==i]
    big=sorted(xs,key=lambda x:-x['cost'])[:3]
    print('%-9s %5d %5d %8.1f  %s' % (n, len(xs), sum(1 for x in xs if x['kind']=='method_decl'), sum(x['cost'] for x in xs)/60, ', '.join('%s(%dm)'%(x['name'],x['cost']//60) for x in big if x['cost']>=120)))
if '--apply' not in sys.argv: sys.exit(0)
os.makedirs(OUT,exist_ok=True)
for i,(n,a,b,c) in enumerate(BANDS):
    xs=[it for it in items if it['band']==i]
    out=[h for h in header if not re.match(r'^\s*include\s+"', h)]
    out.append('module %s%s {' % (mod, n))
    out += ['  '+im.strip() if not im.startswith('  ') else im for im in d['imports']]
    for j in range(i): out.append('  import opened %s%s' % (mod, BANDS[j][0]))
    out.append('')
    for it in xs: out += L[it['line']-1:it['end']] + ['']
    out.append('}')
    open(os.path.join(OUT,'LiftSim%d%s.dfy'%(i,n)),'w').write('\n'.join(out)+'\n')
json.dump({it['name']:BANDS[it['band']][0] for it in items}, open(os.path.join(OUT,'bands.json'),'w'))
print('wrote', len(BANDS), 'files to', OUT)
