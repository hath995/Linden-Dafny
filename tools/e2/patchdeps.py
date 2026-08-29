import zipfile, sys, os, glob, re
S=os.path.dirname(os.path.abspath(__file__))
# usage: patchdeps.py [--out DIR] BOOGIEARG...   (each arg one --boogie value, e.g. '/proc:*well-formedness*' or '/noProc:DeepFindRec*')
args=sys.argv[1:]; outdir='deps-wf'
if args and args[0]=='--out': outdir=args[1]; args=args[2:]
assert args
D=os.path.expanduser('~/dafny-4.11.0-x64-ubuntu-22.04/dafny')
srcs=glob.glob('/home/aaron/code/Linden-Dafny/linden-equiv/deps/*.doo')+[D+'/DafnyStandardLibraries.doo',D+'/DafnyStandardLibraries-cs.doo']
os.makedirs(os.path.join(S,outdir),exist_ok=True)
for src in srcs:
    dst=os.path.join(S,outdir,os.path.basename(src))
    with zipfile.ZipFile(src) as zi, zipfile.ZipFile(dst,'w',zipfile.ZIP_DEFLATED) as zo:
        for item in zi.infolist():
            data=zi.read(item.filename)
            if item.filename=='manifest.toml':
                t=data.decode()
                t=re.sub(r'standard-libraries = \w+','standard-libraries = false',t)
                t=t.replace('[options]\n','[options]\nboogie = [%s]\n'%', '.join('"%s"'%a for a in args))
                data=t.encode()
            zo.writestr(item,data)
print(outdir,'patched with boogie =',args)
