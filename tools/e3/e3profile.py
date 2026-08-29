#!/usr/bin/env python3
"""e3profile.py LOG.txt [N] — rank the verification scopes of a Dafny `--log-format text` log by cost.
Prints the top N (default 25) scopes: resource count, wall time, outcome, #batches, name; then totals.
Use on a whole-module run (e.g. --filter-symbol=LindenElkLiftSim) to pick the lemmas worth the E3 loop."""
import re, sys
txt = open(sys.argv[1]).read(); N = int(sys.argv[2]) if len(sys.argv) > 2 else 25
rows = []
for sec in txt.split('\nResults for ')[1:]:
    head, _, body = sec.partition('\n')
    name = head.strip()
    if '(well-formedness)' in name: continue
    oc = re.search(r'Overall outcome: (\S+)', body); ot = re.search(r'Overall time: (\S+)', body); orc = re.search(r'Overall resource count: (\d+)', body)
    nb = body.count('Assertion batch ')
    t = ot.group(1) if ot else '?'
    h, m, s = t.split(':') if t.count(':') == 2 else ('0', '0', '0')
    secs = int(h) * 3600 + int(m) * 60 + float(s)
    rows.append((int(orc.group(1)) if orc else 0, secs, oc.group(1) if oc else '?', nb, name.replace(' (correctness)', '')))
rows.sort(reverse=True)
print('%14s %8s %-10s %4s  %s' % ('resources', 'seconds', 'outcome', 'bat', 'scope'))
for r, s, o, nb, n in rows[:N]: print('%14d %8.1f %-10s %4d  %s' % (r, s, o, nb, n))
tot = sum(r[1] for r in rows); bad = [r for r in rows if r[2] != 'Correct']
print('\n%d scopes, %.0f s solver time total; %d not Correct: %s' % (len(rows), tot, len(bad), ', '.join(n for *_, n in bad[:10])))
