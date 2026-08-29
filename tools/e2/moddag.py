import re, glob, os, collections
files = sorted(glob.glob('src/Equiv/*.dfy'))
mod_file = {}; file_mods = collections.defaultdict(list); imports = collections.defaultdict(set); includes = collections.defaultdict(set)
for f in files:
    t = open(f).read()
    for m in re.finditer(r'^\s*module\s+(?:\{[^}]*\}\s*)?([A-Za-z_][\w]*)', t, re.M):
        mod_file[m.group(1)] = f; file_mods[f].append(m.group(1))
    for m in re.finditer(r'^\s*import\s+(?:opened\s+)?(?:[A-Za-z_]\w*\s*=\s*)?([A-Za-z_][\w.]*)', t, re.M):
        imports[f].add(m.group(1).split('.')[0])
    for m in re.finditer(r'^\s*include\s+"([^"]+)"', t, re.M):
        includes[f].add(m.group(1))
local = set(mod_file)
ext = collections.Counter()
edges = collections.defaultdict(set)
for f in files:
    for m in imports[f]:
        if m in local:
            if mod_file[m] != f: edges[f].add(mod_file[m])
        else: ext[m] += 1
multi = {f: ms for f, ms in file_mods.items() if len(ms) > 1}
print('files', len(files), 'modules', len(mod_file), 'files with >1 module:', {os.path.basename(f): ms for f, ms in multi.items()})
print('external modules imported (name: #files):', dict(ext))
print('files with include statements:', sum(1 for f in files if includes[f]), 'total includes', sum(len(v) for v in includes.values()))
# topo order + fan-in/out
indeg = {f: len(edges[f]) for f in files}
order = []; done = set()
while len(order) < len(files):
    ready = sorted(f for f in files if f not in done and edges[f] <= done)
    if not ready: print('CYCLE among', [f for f in files if f not in done]); break
    order += ready; done |= set(ready)
rev = collections.defaultdict(set)
for f in files:
    for d in edges[f]: rev[d].add(f)
print('\nTOPO ORDER (deps -> dependents): name: #deps/#dependents')
for f in order: print('  %-24s %2d/%2d' % (os.path.basename(f)[:-4], len(edges[f]), len(rev[f])))
open('/tmp/claude-1000/-home-aaron-code-Linden-Dafny/4b2a334e-25cd-4ec4-91cd-749084e887a7/scratchpad/moddag.tsv','w').write('\n'.join('%s\t%s' % (os.path.basename(f)[:-4], ','.join(sorted(os.path.basename(d)[:-4] for d in edges[f]))) for f in order))
