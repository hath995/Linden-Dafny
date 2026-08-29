#!/usr/bin/env python3
import json, os, re
S='/tmp/claude-1000/-home-aaron-code-Linden-Dafny/4b2a334e-25cd-4ec4-91cd-749084e887a7/scratchpad'; R='/home/aaron/code/Linden-Dafny'
BANDS=[('Core',4),('Oracle',4),('Chain',4),('Gate',4),('Carriers',4),('Deep',4),('Forward',2),('Main',4)]
import subprocess
old=subprocess.run(['git','show','HEAD:linden-equiv-lift-sim/lemmata.toml'],cwd=R,capture_output=True,text=True).stdout
deps=[l for l in old.split('\n') if re.match(r'^[a-z0-9-]+ = "\^1\.0\.0"$', l)]
assert len(deps) > 40, len(deps)
for i,(n,cores) in enumerate(BANDS):
    pk='linden-equiv-lift-sim-'+n.lower(); d=os.path.join(R,pk)
    lower=['linden-equiv-lift-sim-%s = "^1.0.0"'%BANDS[j][0].lower() for j in range(i)]
    open(d+'/lemmata.toml','w').write('''[package]
name = "%s"
version = "1.0.0"
description = "linden-equiv LiftSim layer %d: %s (machine-checked RegElk/Linden equivalence)"
license = "MIT"

[toolchain]
dafny = ">= 4.11.0"

[source]
to_export = ["src/**/*.dfy"]

[options]
standard-libraries = true
verification-time-limit = "900"
cores = "%d"

[verification]
expected-errors = [
]

[dependencies]
%s
''' % (pk, i, n, cores, '\n'.join(deps+lower)))
print('manifests written for', len(BANDS), 'bands;', len(deps), 'inherited deps')
