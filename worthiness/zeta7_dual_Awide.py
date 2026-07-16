#!/usr/bin/env python3
"""Wide search for A_n=1,61,52921 as multisum with weight C(n+k,k)^p C(n,k)^q
and coupling = product over a subset-family of C(n + sum_{i in S} k_i, n).
Reference: zeta5 Q_n = double sum, weight p=1,q=2, coupling family {{1,2}}."""
from math import comb
from itertools import product, combinations
TARGET=[1,61,52921]
def wt(n,k,p,q): return comb(n+k,k)**p * comb(n,k)**q

def multisum(n, nidx, p, q, family):
    tot=0
    for ks in product(range(n+1), repeat=nidx):
        term=1
        for k in ks: term*=wt(n,k,p,q)
        for S in family:
            term*=comb(n+sum(ks[i] for i in S), n)
        tot+=term
    return tot

# verify Q_n
def Q(n): return multisum(n,2,1,2,[(0,1)])
print("check Q_n:",[Q(n) for n in range(3)],"expect 1,21,2989")

found=[]
for nidx in (2,3):
    idxs=tuple(range(nidx))
    subs=[S for r in range(1,nidx+1) for S in combinations(idxs,r)]
    for p in range(0,4):
        for q in range(0,4):
            for fsize in range(0, min(4,len(subs))+1):
                for family in combinations(subs, fsize):
                    try:
                        vals=[multisum(n,nidx,p,q,family) for n in range(3)]
                    except Exception: continue
                    if vals==TARGET:
                        print(f"*** MATCH nidx={nidx} p={p} q={q} family={family}")
                        found.append((nidx,p,q,family))
                    elif vals[0]==1 and vals[1]==61:
                        print(f"  p61 nidx={nidx} p={p} q={q} family={family} -> {vals}")
print("found:",found)
