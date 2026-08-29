#!/usr/bin/env python3
"""e2ts.py FILE.dfy — tree-sitter analysis of one Dafny module: declarations with exact spans (doc comment attached),
same-module references (member accesses excluded), SCCs, dependency levels. Writes FILE.ts.json."""
import sys, json, collections
import tree_sitter_dafny as tsd
from tree_sitter import Language, Parser
src=open(sys.argv[1],'rb').read()
tree=Parser(Language(tsd.language())).parse(src)
root=tree.root_node
mod=[c for c in root.children if c.type=='module_definition']
assert len(mod)==1, [c.type for c in root.children]
body=[c for c in mod[0].children if c.type=='module_body'][0]
DECL={'method_decl','function_decl','datatype_decl','constant_field_decl','synonym_type_decl','newtype_decl','class_decl','trait_decl','field_decl','iterator_decl'}
text=lambda n: src[n.start_byte:n.end_byte].decode()
items=[]; pending=[]   # pending comments to attach to the next decl
imports=[]; others=[]
for c in body.children:
    if c.type in ('line_comment','block_comment','decl_modifier'): pending.append(c); continue
    if c.type=='module_import': imports.append(c); pending=[]; continue
    if c.type in DECL:
        nm=c.child_by_field_name('name')
        kw=None
        for ch in c.children:
            if ch.type in ('decl_modifier','attribute'): continue
            if not ch.is_named: kw=text(ch); break
            if ch.type not in ('decl_modifier','attribute'): break
        # gather identifiers referenced inside, excluding member accesses (`.x`) and the decl's own name
        refs=set(); stack=[c]
        while stack:
            n=stack.pop()
            if n.type=='identifier':
                ps=n.prev_sibling
                if not (ps is not None and not ps.is_named and text(ps)=='.'): refs.add(text(n))
            stack.extend(n.children)
        start=pending[0].start_point[0] if pending else c.start_point[0]
        mods=[text(x) for x in pending if x.type=='decl_modifier']
        items.append({'kind':c.type,'kw':kw,'mods':mods,'name':text(nm) if nm else '?','line':start+1,'dstart':c.start_point[0]+1,'end':c.end_point[0]+1,'refs':sorted(refs)})
        pending=[]
    elif c.is_named:
        others.append((c.type, c.start_point[0]+1)); pending=[]
names={it['name'] for it in items}
for it in items: it['refs']=[r for r in it['refs'] if r in names and r!=it['name']]
print('decls', len(items), 'imports', len(imports), 'other body nodes', collections.Counter(t for t,_ in others))
print('kinds', collections.Counter((it['kind'],it['kw']) for it in items).most_common(8))
# levels over SCCs
refs={it['name']:set(it['refs']) for it in items}
sys.setrecursionlimit(100000); idx={};low={};st=[];on=set();comp={};c=[0];k=[0]
def strong(v):
    idx[v]=low[v]=c[0];c[0]+=1;st.append(v);on.add(v)
    for w in refs[v]:
        if w not in idx: strong(w);low[v]=min(low[v],low[w])
        elif w in on: low[v]=min(low[v],idx[w])
    if low[v]==idx[v]:
        while True:
            w=st.pop();on.discard(w);comp[w]=k[0]
            if w==v: break
        k[0]+=1
for it in items:
    if it['name'] not in idx: strong(it['name'])
level={}
def lv(n):
    if n in level: return level[n]
    level[n]=0; m=0
    for w in refs[n]:
        if comp[w]!=comp[n]: m=max(m,lv(w)+1)
    level[n]=m; return m
for it in items: lv(it['name'])
byc=collections.defaultdict(list)
for n in level: byc[comp[n]].append(n)
for ns in byc.values():
    m=max(level[n] for n in ns)
    for n in ns: level[n]=m
for it in items: it['level']=level[it['name']]; it['scc']=comp[it['name']]
sccs=[ns for ns in byc.values() if len(ns)>1]
print('max level', max(level.values()), 'nontrivial SCCs', [sorted(s) for s in sccs])
hist=collections.Counter(it['level'] for it in items); print('level histogram', dict(sorted(hist.items())))
json.dump({'items':items,'imports':[text(i) for i in imports],'module':text(mod[0].child_by_field_name('name')), 'header_end_line': mod[0].start_point[0]}, open(sys.argv[1]+'.ts.json','w'))
