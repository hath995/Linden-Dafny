#!/usr/bin/env python3
"""regen_dfyconfig.py [--apply] — rewrite every workspace member's tracked dfyconfig.toml from its
materialized deps/ (lem stages the closure there during `lem pack`; the namespaced .doo names are
`linden.<name>.doo`). Format matches what lem wrote originally: a header + [options] library = [...]."""
import os, sys, glob
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
HEAD = ("# Created by lem: the restored dependency closure. No `includes` key —\n"
        "# Dafny defaults to **/*.dfy, covering src, tests, and materialized deps.\n\n[options]\n")
n = 0
for m in sorted(glob.glob(os.path.join(ROOT, '*', 'lemmata.toml'))):
    d = os.path.dirname(m)
    doos = sorted(os.path.basename(p) for p in glob.glob(os.path.join(d, 'deps', '*.doo')))
    txt = HEAD + 'library = [%s]\n' % ', '.join('"deps/%s"' % f for f in doos)
    cur = open(os.path.join(d, 'dfyconfig.toml')).read() if os.path.exists(os.path.join(d, 'dfyconfig.toml')) else None
    if cur != txt:
        n += 1
        print('%-40s %d deps%s' % (os.path.basename(d), len(doos), '' if doos else '  (no deps/ yet)'))
        if '--apply' in sys.argv: open(os.path.join(d, 'dfyconfig.toml'), 'w').write(txt)
print('%d member(s) %s' % (n, 'rewritten' if '--apply' in sys.argv else 'would change (dry run)'))
