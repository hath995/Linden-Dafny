import json, re
S='/tmp/claude-1000/-home-aaron-code-Linden-Dafny/4b2a334e-25cd-4ec4-91cd-749084e887a7/scratchpad'; R='/home/aaron/code/Linden-Dafny'
bands=json.load(open(S+'/split/bands.json'))
p=R+'/linden-equiv/src/Equiv/ApiMatch.dfy'; s=open(p).read()
used=sorted({m for m in re.findall(r'LSIM\.([A-Za-z0-9_]+)', s)}); need=sorted({bands[u] for u in used})
alias={b:('LSIM' if b=='Main' else 'LSIM'+b.upper()[:3]) for b in need}
imp='\n'.join('  import %s = LindenElkLiftSim%s' % (alias[b], b) for b in need)
s2,n=re.subn(r'^\s*import LSIM = LindenElkLiftSim\s*$', imp, s, flags=re.M); assert n==1, n
for u in used: s2=re.sub(r'\bLSIM\.'+u+r'\b', alias[bands[u]]+'.'+u, s2)
open(p,'w').write(s2); print('ApiMatch:', {u:bands[u] for u in used}, 'imports:', alias)
p=R+'/linden-equiv/lemmata.toml'; s=open(p).read()
s2=s.replace('linden-equiv-lift-sim = "^1.0.0"\n', ''.join('linden-equiv-lift-sim-%s = "^1.0.0"\n'%b.lower() for b in need)); assert s2!=s
open(p,'w').write(s2); print('parent deps:', [b.lower() for b in need])
