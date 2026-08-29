#!/usr/bin/env python3
"""e3scan.py LEMMA... — for each target lemma in the monolith, list bare statement-level lemma calls whose callee's
ensures is big or quantified (scoping candidates)."""
import json, re, sys, collections
W='/home/aaron/code/Linden-Dafny-l4/linden-equiv/src/Equiv/LiftSim.dfy'
L=open(W).read().split('\n'); d=json.load(open(W+'.ts.json')); items={it['name']:it for it in d['items']}
def ensures_of(name):
    it=items.get(name)
    if not it: return None
    body='\n'.join(L[it['dstart']-1:it['end']]); i=body.find('\n  {'); hdr=body[:i] if i>0 else body
    ens=[l for l in hdr.split('\n') if re.match(r'^\s*ensures\b', l)]
    # count ensures lines incl. continuation lines
    n=0; on=False
    for l in hdr.split('\n'):
        if re.match(r'^\s*ensures\b', l): on=True
        elif re.match(r'^\s*(requires|decreases|modifies)\b', l): on=False
        if on and l.strip() and not l.strip().startswith('//'): n+=1
    q=len(re.findall(r'\b(forall|exists)\b', hdr)); car=len(re.findall(r'LookNest\w+|GateStatic\w+|OracleColsOk|LookTablesOk', hdr))
    return n, q, car
for target in sys.argv[1:]:
    it=items[target]; print('== %s (lines %d-%d, %d lines)' % (target, it['dstart'], it['end'], it['end']-it['dstart']+1))
    for ln in range(it['dstart'], it['end']+1):
        m=re.match(r'^(\s+)([A-Za-z_][\w.]*)\(', L[ln-1])
        if not m: continue
        callee=m.group(2).split('.')[-1]
        if callee not in items or items[callee]['kind']!='method_decl': continue
        # bare = the statement is not inside an `assert ... by {` on the same/previous line (heuristic: look back 3 lines for ' by {')
        ctx='\n'.join(L[max(0,ln-4):ln-1]); scoped=' by {' in ctx and '}' not in L[ln-2]
        e=ensures_of(callee)
        if e and (e[0]>=6 or e[1]>=1 or e[2]>=1):
            print('  %s%6d  %-38s ens=%2d lines, quant=%d, carrier=%d' % ('(by)' if scoped else '    ', ln, callee, *e))
