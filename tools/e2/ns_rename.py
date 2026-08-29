#!/usr/bin/env python3
"""ns_rename.py [--apply] — move every workspace member into the `linden` namespace (lem namespace feature):
[package] namespace = "linden", name = <old name minus the 'linden-' prefix> (regex-engine -> linden.regex-engine),
and every internal dependency key rewritten to the quoted canonical name "linden.<name>". Directory names unchanged."""
import re, sys, glob, os
R='/home/aaron/code/Linden-Dafny'
members=sorted(d for d in glob.glob(R+'/*/lemmata.toml'))
old2new={}
for m in members:
    s=open(m).read(); n=re.search(r'^name = "([a-z0-9-]+)"', s, re.M).group(1)
    new=n[len('linden-'):] if n.startswith('linden-') else n
    assert re.match(r'^[a-z][a-z0-9-]*$', new) and len('linden.'+new)<=64, new
    old2new[n]='linden.'+new
print('%d members; e.g.' % len(old2new), dict(list(old2new.items())[:3]))
for m in members:
    s=open(m).read(); n=re.search(r'^name = "([a-z0-9-]+)"', s, re.M).group(1)
    s2=re.sub(r'^name = "%s"'%re.escape(n), 'namespace = "linden"\nname = "%s"'%old2new[n][len('linden.'):], s, count=1, flags=re.M)
    for o,nn in old2new.items():
        s2=re.sub(r'^%s = "'%re.escape(o), '"%s" = "'%nn, s2, flags=re.M)
    if '--apply' in sys.argv: open(m,'w').write(s2)
print('applied' if '--apply' in sys.argv else 'dry run only')
