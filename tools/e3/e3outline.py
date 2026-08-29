#!/usr/bin/env python3
"""e3outline.py FILE.dfy LEMMA — statement-tree outline of one lemma (tree-sitter): nested blocks with line spans,
statement counts, calls (with callee ensures sizes looked up across src/Equiv)."""
import sys, re, glob, collections
import tree_sitter_dafny as tsd
from tree_sitter import Language, Parser
F, NAME = sys.argv[1], sys.argv[2]
src=open(F,'rb').read(); tree=Parser(Language(tsd.language())).parse(src); text=lambda n: src[n.start_byte:n.end_byte].decode()
# ensures sizes of every lemma across the equiv sources (line counts of the ensures section)
ens={}
for f in glob.glob('/home/aaron/code/Linden-Dafny-l4/linden-equiv/src/Equiv/*.dfy'):
    t=open(f).read()
    for m in re.finditer(r'^\s*(?:ghost )?(?:least )?lemma(?:\s*\{[^}]*\})*\s+([A-Za-z_]\w*)\s*\(.*?\n(.*?)\n  \{', t, re.S|re.M):
        hdr=m.group(2); on=False; n=0
        for l in hdr.split('\n'):
            if re.match(r'^\s*ensures\b', l): on=True
            elif re.match(r'^\s*(requires|decreases|modifies)\b', l): on=False
            if on and l.strip() and not l.strip().startswith('//'): n+=1
        ens[m.group(1)]=(n, len(re.findall(r'\b(forall|exists)\b', hdr)))
def find_decl(n):
    if n.type=='method_decl' and n.child_by_field_name('name') is not None and text(n.child_by_field_name('name'))==NAME: return n
    for c in n.children:
        r=find_decl(c)
        if r: return r
d=find_decl(tree.root_node); assert d, 'not found'
body=[c for c in d.children if c.type=='block_statement' or c.type.endswith('block')][-1]
calls_in=lambda n: sorted({text(x.child_by_field_name('name') if x.child_by_field_name('name') else x.children[0]) for x in walk(n) if x.type in ('call_statement','method_call','call_expression')})
def walk(n):
    yield n
    for c in n.children: yield from walk(c)
def outline(n, depth, maxdepth):
    for c in n.children:
        if not c.is_named: continue
        lines=c.end_point[0]-c.start_point[0]+1
        first=text(c).split('\n')[0].strip()
        kids=[x for x in c.children if x.is_named]
        if c.type in ('match_statement','if_statement','block_statement','case','while_statement','forall_statement','assert_statement','calc_statement','opaque_block') or lines>=25:
            ident=[x for x in walk(c) if x.type=='identifier']
            callees=sorted({text(x) for x in ident if text(x) in ens and text(x)!=NAME})
            print('%s%-18s L%5d-%-5d %4d lines  %s%s' % ('  '*depth, c.type, c.start_point[0]+1, c.end_point[0]+1, lines, first[:60], ('  calls: '+', '.join('%s[%d/%d]'%(k,*ens[k]) for k in callees[:6])) if callees and c.type in ('case','if_statement','block_statement','assert_statement') and depth<=maxdepth else ''))
            if depth<maxdepth and c.type not in ('assert_statement',): outline(c, depth+1, maxdepth)
print('%s: lines %d-%d (%d)' % (NAME, d.start_point[0]+1, d.end_point[0]+1, d.end_point[0]-d.start_point[0]+1))
print("body node:", body.type); outline(body, 0, 7)
