#!/usr/bin/env python3
"""gen_pkgs.py [--apply] — split linden-equiv/src/Equiv into one lem package per file under linden-equiv/pkgs/<name>/.
Dry run prints the plan. --apply: creates dirs, MOVES the .dfy (include lines stripped), writes lemmata.toml
(+ dfyconfig.toml via `lem restore` later), and widens lem-workspace.toml's members."""
import re, glob, os, sys, collections, subprocess, shutil
ROOT='/home/aaron/code/Linden-Dafny'; EQ=ROOT+'/linden-equiv'; S=os.path.dirname(os.path.abspath(__file__))
ext = {}
for line in open(S+'/extmods.tsv'):
    p, m = line.rstrip('\n').split('\t'); ext.setdefault(m, p)
SHIMS={'LindenImports','RegElkImports'}   # include-only convenience files: no proofs, no dependents — not packages
files = sorted(f for f in glob.glob(EQ+'/src/Equiv/*.dfy') if os.path.basename(f)[:-4] not in SHIMS)
mod_file={}; imports=collections.defaultdict(set)
for f in files:
    t=open(f).read()
    for m in re.finditer(r'^\s*module\s+(?:\{[^}]*\}\s*)?([A-Za-z_]\w*)', t, re.M): mod_file[m.group(1)]=f
    for m in re.finditer(r'^\s*import\s+(?:opened\s+)?(?:[A-Za-z_]\w*\s*=\s*)?([A-Za-z_][\w.]*)', t, re.M): imports[f].add(m.group(1).split('.')[0])
kebab=lambda f: 'linden-equiv-'+re.sub(r'(?<=[a-z0-9])(?=[A-Z])','-',os.path.basename(f)[:-4]).lower()
BIG={'LiftSim':4,'MainTheorem':4,'ActionsTreeRepRE':4,'FlipGate':4,'FlipKeystone':4,'LookBehindKeystone':4,'NfaRepRE':4}
plan=[]
for f in files:
    base=os.path.basename(f)[:-4]; name=kebab(f)
    internal=sorted({kebab(mod_file[m]) for m in imports[f] if m in mod_file and mod_file[m]!=f})
    external=sorted({ext[m] for m in imports[f] if m in ext})
    missing=sorted(m for m in imports[f] if m not in mod_file and m not in ext and m!='Std')
    plan.append((base,name,internal,external,missing,BIG.get(base)))
for base,name,internal,external,missing,cores in plan:
    print('%-22s -> %-34s int=%d ext=%s%s%s' % (base,name,len(internal),','.join(e.replace('linden-','').replace('regex-engine','rx') for e in external), '  cores=%d'%cores if cores else '', '  MISSING='+','.join(missing) if missing else ''))
if '--apply' not in sys.argv: sys.exit(0)
LEM='/home/aaron/code/Lemmata/deploy/cli/.out/lem-0.1.20-linux-x64/lem'
API={'ApiMatch','ApiReasoning'}          # stay in the parent `linden-equiv` package
strip=lambda t: re.sub(r'^\s*include\s+"[^"]+"\s*\n','',t,flags=re.M)
api_int=set(); api_ext=set()
for base,name,internal,external,missing,cores in plan:
    src=EQ+'/src/Equiv/'+base+'.dfy'
    if base in API:
        open(src,'w').write(strip(open(src).read())); api_int|=set(internal); api_ext|=set(external); continue
    d=EQ+'/pkgs/'+name; os.makedirs(d,exist_ok=True)
    r=subprocess.run([LEM,'init',name],cwd=d,input='>= 4.11.0\nlinden-equiv layer: %s (machine-checked RegElk/Linden equivalence)\n\n\nMIT\n\n'%base,capture_output=True,text=True)
    if r.returncode!=0: print('lem init FAILED for',name,r.stdout[-300:],r.stderr[-300:]); sys.exit(1)
    os.makedirs(d+'/src',exist_ok=True)
    open(d+'/src/'+base+'.dfy','w').write(strip(open(src).read())); os.remove(src)
    m=open(d+'/lemmata.toml').read()
    opts='[options]\nstandard-libraries = true\nverification-time-limit = "900"' + ('\ncores = "%d"'%cores if cores else '') + '\n'
    assert '[options]\n' in m and m.rstrip().endswith('[dependencies]'), m
    m=m.replace('[options]\n',opts,1).rstrip()+'\n'+'\n'.join('%s = "^1.0.0"'%q for q in external+internal)+'\n'
    open(d+'/lemmata.toml','w').write(m)
# the parent package keeps ApiMatch/ApiReasoning and depends on what they import
m=open(EQ+'/lemmata.toml').read()
i=m.index('[dependencies]'); m=m[:i]+'[dependencies]\n'+'\n'.join('%s = "^1.0.0"'%q for q in sorted(api_ext|api_int))+'\n'
open(EQ+'/lemmata.toml','w').write(m)
print('applied: %d packages under linden-equiv/pkgs/ + parent keeps ApiMatch/ApiReasoning' % (len(plan)-2))
