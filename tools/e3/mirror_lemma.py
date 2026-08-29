#!/usr/bin/env python3
"""mirror_lemma.py SRC.dfy DST.dfy LEMMA [LEMMA ...] [--apply]
Replace each named lemma's full span (doc comment + attributes + signature + body) in DST with the
span from SRC. Spans come from tree-sitter-dafny (`method_decl` nodes), so this survives line drift
between the lem-split band files and the monolith. Prints old/new line counts; writes only with --apply."""
import sys, re
import tree_sitter_dafny as tsd
from tree_sitter import Language, Parser

def spans(path):
    src = open(path, 'rb').read()
    tree = Parser(Language(tsd.language())).parse(src)
    out = {}
    def walk(n):
        if n.type == 'method_decl':
            nm = n.child_by_field_name('name')
            if nm is not None:
                a, b = n.start_byte, n.end_byte
                # include a directly preceding doc comment (/** ... */ or // lines) glued to the decl
                head = src.rfind(b'\n', 0, a) + 1
                out[src[nm.start_byte:nm.end_byte].decode()] = (head, b)
        for c in n.children: walk(c)
    walk(tree.root_node)
    return src, out

args = [a for a in sys.argv[1:] if not a.startswith('--')]
S, D, names = args[0], args[1], args[2:]
ssrc, sspan = spans(S); dsrc, dspan = spans(D)
edits = []
for n in names:
    if n not in sspan: raise SystemExit('not in SRC: ' + n)
    if n not in dspan: raise SystemExit('not in DST: ' + n)
    sa, sb = sspan[n]; da, db = dspan[n]
    edits.append((da, db, ssrc[sa:sb]))
    print('%s: DST %d lines -> SRC %d lines' % (n, dsrc[da:db].count(b'\n'), ssrc[sa:sb].count(b'\n')))
out = dsrc
for da, db, txt in sorted(edits, reverse=True):
    out = out[:da] + txt + out[db:]
if '--apply' in sys.argv:
    open(D, 'wb').write(out); print('written', D)
else:
    print('(dry run; add --apply)')
