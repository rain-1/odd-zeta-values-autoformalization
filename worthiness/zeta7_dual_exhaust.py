#!/usr/bin/env python3
"""Exhaustive triple-sum coupling search for A_n=1,61,52921.
Summand = prod_i w(k_i) * prod_{S in family} C(n + sum_{i in S} k_i, n),
w(k)=C(n+k,n)C(n,k)^2, family = any subset of the 7 nonempty subsets of {1,2,3}."""
from math import comb
from itertools import product, combinations

TARGET = [1, 61, 52921]
def w(n,k): return comb(n+k,n)*comb(n,k)**2

subsets = [S for r in range(1,4) for S in combinations((0,1,2), r)]  # 7 subsets

def sumval(n, family):
    t=0
    for ks in product(range(n+1), repeat=3):
        term = w(n,ks[0])*w(n,ks[1])*w(n,ks[2])
        for S in family:
            s=sum(ks[i] for i in S)
            term *= comb(n+s, n)
        t+=term
    return t

hits=[]
# iterate over all families (subsets of the 7 subsets), but keep size<=4 to bound coupling degree
from itertools import combinations as C7
for fsize in range(0,5):
    for family in C7(subsets, fsize):
        vals=[sumval(n,family) for n in range(3)]
        if vals==TARGET:
            hits.append(family); print("*** MATCH family:", family, vals)
        elif vals[0]==1 and vals[1]==61:
            print("  partial61:", family, vals)

print("total hits:", len(hits))

# Also try with weight power on w varied and single total coupling
print("\n--- vary weight exponents, coupling = C(n+k1+k2+k3,n)^e ---")
def sv2(n, a, b, cc, e):
    t=0
    for ks in product(range(n+1),repeat=3):
        term=1
        for k in ks:
            term*=comb(n+k,n)**a*comb(n,k)**b*comb(n+k,k)**cc
        term*=comb(n+sum(ks),n)**e
        t+=term
    return t
for a in range(0,3):
 for b in range(0,4):
  for cc in range(0,2):
   for e in range(0,4):
     vals=[sv2(n,a,b,cc,e) for n in range(3)]
     if vals==TARGET:
        print("*** MATCH w-exp a,b,c,e=",a,b,cc,e,vals)
     elif vals==[1,61]+[vals[2]] and vals[1]==61:
        print("  p61 a,b,c,e=",a,b,cc,e,vals)
