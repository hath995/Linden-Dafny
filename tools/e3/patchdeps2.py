import zipfile, sys, os, glob, re
srcdir, outdir, args = sys.argv[1], sys.argv[2], sys.argv[3:]
D=os.path.expanduser('~/dafny-4.11.0-x64-ubuntu-22.04/dafny')
os.makedirs(outdir, exist_ok=True)
for src in glob.glob(srcdir+'/*.doo')+[D+'/DafnyStandardLibraries.doo', D+'/DafnyStandardLibraries-cs.doo']:
    dst=os.path.join(outdir, os.path.basename(src))
    with zipfile.ZipFile(src) as zi, zipfile.ZipFile(dst,'w',zipfile.ZIP_DEFLATED) as zo:
        for item in zi.infolist():
            data=zi.read(item.filename)
            if item.filename=='manifest.toml':
                t=data.decode(); t=re.sub(r'standard-libraries = \w+','standard-libraries = false',t)
                t=t.replace('[options]\n','[options]\nboogie = [%s]\n'%', '.join('"%s"'%a for a in args)); data=t.encode()
            zo.writestr(item,data)
print('patched', len(glob.glob(outdir+'/*.doo')), 'doo files ->', outdir)
