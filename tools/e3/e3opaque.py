#!/usr/bin/env python3
"""e3opaque.py FILE LEMMA MARKER [--apply] — wrap the statements of LEMMA that precede the line containing MARKER in an
`opaque ensures … { … }` block: all locals declared in the preamble are pre-declared (types inferred), `var x := E`
becomes `x := E` with `x == E` exported, `var a, b :| C` becomes `a, b :| C` with C exported, and every preamble
`assert P` (`by`-bodies dropped) whose identifiers intersect the downstream-used names is exported."""
import sys, re
import tree_sitter_dafny as tsd
from tree_sitter import Language, Parser
F, NAME, MARKER = sys.argv[1], sys.argv[2], sys.argv[3]
FROM = sys.argv[sys.argv.index('--from')+1] if '--from' in sys.argv else None
src=open(F,'rb').read(); tree=Parser(Language(tsd.language())).parse(src); text=lambda n: src[n.start_byte:n.end_byte].decode()
L=src.decode().split('\n')
import glob as _g
LEMMAS=set()
for _f in _g.glob('/home/aaron/code/Linden-Dafny-l4/linden-equiv/src/Equiv/*.dfy'):
    LEMMAS |= set(re.findall(r'^\s*(?:ghost )?(?:least )?lemma(?:\s*\{[^}]*\})*\s+([A-Za-z_]\w*)', open(_f).read(), re.M))
def walk(n):
    yield n
    for c in n.children: yield from walk(c)
d=[n for n in walk(tree.root_node) if n.type=='method_decl' and n.child_by_field_name('name') and text(n.child_by_field_name('name'))==NAME][0]
body=[c for c in d.children if c.type=='block_statement'][-1]
mline=[i for i in range(d.start_point[0], d.end_point[0]) if MARKER in L[i]][0]   # 0-based
fline=[i for i in range(d.start_point[0], d.end_point[0]) if FROM and FROM in L[i]][0] if FROM else -1
# the INNERMOST block containing the marker line(s): lets the tool work inside if/else/match arms
lo=fline if fline>=0 else mline
blk=max([n for n in walk(body) if n.type=='block_statement' and n.start_point[0] <= lo and n.end_point[0] >= mline], key=lambda n: n.start_byte)
stmts=[c for c in blk.children if c.is_named and c.type.endswith('statement') or (c.is_named and c.type.endswith('block'))]
if fline<0: fline=blk.start_point[0]-1 if blk is not body else -1
pre=[s for s in stmts if s.end_point[0] < mline and s.start_point[0] > fline]; post=[s for s in stmts if s.start_point[0] >= mline]
pre_start=pre[0].start_point[0]; pre_end=pre[-1].end_point[0]
IND=' '*pre[0].start_point[1]
# names declared in the preamble
TYPES={}
if '--types' in sys.argv:
    for kv in sys.argv[sys.argv.index('--types')+1].split(';'): k,v=kv.split(':',1); TYPES[k.strip()]=v.strip()
NOEXP=re.compile(sys.argv[sys.argv.index('--no-export')+1]) if '--no-export' in sys.argv else None
OUTS=[]
_r=re.search(r'returns\s*\((.*?)\)', text(d), re.S)
if _r: OUTS=[x.split(':')[0].strip() for x in _r.group(1).split(',') if x.strip()]
def parse_lhs(lhs):
    m=re.match(r'^([A-Za-z_][\w.]*|)\((.*)\)$', lhs.strip(), re.S)
    if m: return [x.strip() for x in m.group(2).split(',')], m.group(1)
    names=[]
    for x in lhs.split(','):
        x=x.strip(); mm=re.match(r'^([A-Za-z_]\w*)\s*:\s*(.+)$', x, re.S)
        if mm: names.append(mm.group(1)); TYPES.setdefault(mm.group(1), mm.group(2).strip())
        else: names.append(x)
    return names, None
decl=[]; ens=[]; outset=[]; DECLF=set()
downstream=set(text(x) for s in post for x in walk(s) if x.type=='identifier')
for s in pre:
    t=text(s)
    if s.type=='assert_statement' and '{:' in t.split('assert',1)[1][:12]: pass   # attributed asserts ({:split_here} ...) are not facts
    elif s.type=='assert_statement':
        t=re.sub(r'\s+by\s*\{.*\}\s*$', '', t, flags=re.S).strip(); t=re.sub(r'^assert\s+','',t).rstrip(';').strip()
        ids=set(re.findall(r'\b[A-Za-z_]\w*\b', t))
        if (ids & downstream or '--export-all' in sys.argv) and ('--export-forall' in sys.argv or 'forall' not in t.split('::')[0][:8]): ens.append(t)
    elif s.type=='forall_statement' and '--export-forall' in sys.argv:
        # a forall STATEMENT's conclusion is a fact: forall <binders> :: <range> ==> <ensures>
        blk=[c for c in s.children if c.type=='block_statement']
        head=src[s.start_byte:blk[0].start_byte].decode() if blk else t
        m=re.match(r'^forall\s+(.*?)\s*(?:\|\s*(.*?))?\s*ensures\s+(.*?)\s*$', head, re.S)
        if m:
            binders, rng, concl = m.group(1).strip(), (m.group(2) or '').strip(), m.group(3).strip()
            fact = 'forall %s :: %s' % (binders, ('(%s) ==> (%s)' % (rng, concl)) if rng else concl)
            ids=set(re.findall(r'\b[A-Za-z_]\w*\b', fact))
            if ids & downstream or '--export-all' in sys.argv: ens.append(fact)
    elif s.type=='var_decl_statement':
        m=re.match(r'^var\s+(.*?)\s*(:=|:\|)\s*(.*)$', t, re.S)
        if not m: raise SystemExit('unparsed var: '+t[:80])
        lhs, op, rhs = m.group(1).strip(), m.group(2), m.group(3).strip().rstrip(';')
        names,ctor=parse_lhs(lhs)
        decl += names
        if op==':=' and ctor is not None: (lambda f: (ens.append(f), DECLF.add(f)))('%s == %s(%s)' % (rhs, ctor, ', '.join(names)))
        elif op==':=' and len(names)==1 and len(rhs)<900 and not any(re.search(r'\b%s\s*\(' % re.escape(lm), rhs) for lm in LEMMAS) and not (NOEXP and NOEXP.search(rhs)): (lambda f: (ens.append(f), DECLF.add(f)))('%s == %s' % (names[0], rhs))
        elif op==':|': (lambda f: (ens.append(f), DECLF.add(f)))(rhs)
    else:
        m=re.match(r'^([A-Za-z_]\w*)\s*:=\s*(.*);\s*$', t, re.S)
        if m and m.group(1) in OUTS:
            outset.append(m.group(1)); rhs=m.group(2).strip()
            if len(rhs)<900 and not any(re.search(r'\b%s\s*\(' % re.escape(lm), rhs) for lm in LEMMAS) and not (NOEXP and NOEXP.search(rhs)): (lambda f: (ens.append(f), DECLF.add(f)))('%s == %s' % (m.group(1), rhs))
used_decl=[n for n in decl if n in downstream]
# order for well-formedness: Some?-facts first, then the other asserted facts, then the definitional equalities
# SOURCE ORDER: the block body was well-formed in this order, so its exported facts are too (Some?-only facts first is the one safe hoist)
some=[e for e in ens if '.Some?' in e and '.value' not in e]   # hoist Some?-only facts (incl. call receivers); everything else stays in source order
ens=some+[e for e in ens if e not in some]
if '--defs-first' in sys.argv:   # the older ordering: definitional facts of locals first, then the asserted facts (empirically better for LBDeep)
    ens=[e for e in ens if e in some]+[e for e in ens if e not in some and e in DECLF]+[e for e in ens if e not in some and e not in DECLF]
_have=set(e.strip() for e in ens); _auto=[]
NOSOME=set(sys.argv[sys.argv.index('--no-some')+1].split(',')) if '--no-some' in sys.argv else set()
for e in list(ens):
    for nm in re.findall(r'\b([A-Za-z_]\w*)\.value\b', e):
        f='%s.Some?' % nm
        if nm in NOSOME: continue
        if f not in _have and not any(re.match(r'^%s\.Some\?' % re.escape(nm), x.strip()) for x in ens): _have.add(f); _auto.append(f)
ens=_auto+ens
print('preamble: lines %d-%d, %d statements, %d locals (%d used downstream), %d exported facts' % (pre_start+1, pre_end+1, len(pre), len(decl), len(used_decl), len(ens)))
# emit
out=L[:pre_start]
out.append(IND+'// (2026-08-29 E3) the preamble is an OPAQUE block: only the facts below reach the arm\'s VC.')
out += [IND+('var %s: %s := *;' % (n, TYPES[n]) if n in TYPES else 'var %s := *;' % n) for n in decl]
out += [IND+'%s := *;' % n for n in dict.fromkeys(outset)]   # `:= *` makes the local definitely assigned: no defass obligations in the block's ensures
out.append(IND+'opaque')
out += [IND+'  ensures %s' % ('(' + e.replace('\n','\n'+IND+'    ') + ')') for e in ens]
out.append(IND+'{')
# rewrite ONLY the top-level var declarations of the preamble (nested ones inside by-blocks stay as they are)
segbytes=bytearray(src[:0]); 
segsrc=src
edits=[]
for st in pre:
    if st.type=='var_decl_statement':
        t=text(st); m=re.match(r'^var\s+(.*?)\s*(:=|:\|)', t, re.S)
        lhs=m.group(1); names,ctor=parse_lhs(lhs)
        if ctor is not None: newt='var %s(%s) %s %s := %s;' % (ctor, ', '.join(n+"'" for n in names), t[m.end(2)-len(m.group(2)):].rstrip(), ', '.join(names), ', '.join(n+"'" for n in names))
        else: newt=', '.join(names)+' '+t[m.end(2)-len(m.group(2)):]
        edits.append((st.start_byte, st.end_byte, newt))
seg_b=src[body_line_start(pre_start):body_line_end(pre_end)] if False else None
# apply edits on the byte string of the preamble region
region_start=len('\n'.join(L[:pre_start]).encode())+ (1 if pre_start>0 else 0)
region_end=len('\n'.join(L[:pre_end+1]).encode())
reg=src[region_start:region_end]
for a,b,newt in sorted(edits, reverse=True):
    reg=reg[:a-region_start]+newt.encode()+reg[b-region_start:]
segtxt=reg.decode()
out += ['  '+l for l in segtxt.split('\n')]
out.append(IND+'}')
out += L[pre_end+1:]
if '--apply' in sys.argv: open(F,'w').write('\n'.join(out)); print('applied to', F)
else: print('\n'.join(out[pre_start:pre_start+len(decl)+len(ens)+6])[:3000])
