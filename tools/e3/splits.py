import sys
p, lo, hi, ind = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
L=open(p).read().split('\n'); out=[]; i=0; n=0; sp=' '*ind
while i < len(L):
    out.append(L[i])
    if L[i]==sp+'opaque' and lo < i < hi:
        j=i+1
        while L[j]!=sp+'}': out.append(L[j]); j+=1
        out.append(L[j]); out.append(sp+'assert {:split_here} true;   // (E3) section boundary: its own assertion batch'); n+=1; i=j+1; continue
    i+=1
open(p,'w').write('\n'.join(out)); print(p, 'splits inserted:', n)
