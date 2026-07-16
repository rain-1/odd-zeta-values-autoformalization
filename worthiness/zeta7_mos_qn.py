"""Fast computation of q_n = A_sigma(n) = [x1^n..x8^n] prod_i W_i^n
via bucket elimination over variables (interval-structured windows).
q_n = (n!)^8 * sum over token-matrices a_{ij} (j in W_i), row sums n, col sums n,
       of prod 1/a_{ij}!  .  We process variables (columns) 1..8, tracking partial
row-sums s_i of ACTIVE windows; finished windows must have s_i=n."""
from math import factorial
from fractions import Fraction
from functools import lru_cache
W=[{2,3},{2,3,4,5},{3,4,5},{3,4,5,6,7},{5,6,7},{7,8},set(range(1,9)),{1,2,3}]
rng=[(min(w),max(w)) for w in W]
def qn(n):
    invf=[Fraction(1,factorial(k)) for k in range(n+1)]
    # state: tuple over windows of partial row-sum s_i (0..n); use full 8-tuple, inactive stay 0/n
    from collections import defaultdict
    state=defaultdict(Fraction); state[(0,)*8]=Fraction(1)
    for j in range(1,9):
        wins=[i for i in range(8) if rng[i][0]<=j<=rng[i][1]]  # windows containing x_j
        finishing=[i for i in range(8) if rng[i][1]==j]
        ns=defaultdict(Fraction)
        # distribute n tokens for column j among 'wins'
        def dists(total,parts):
            if parts==1: yield (total,); return
            for a in range(total+1):
                for r in dists(total-a,parts-1): yield (a,)+r
        distlist=list(dists(n,len(wins)))
        for st,c in state.items():
            for dd in distlist:
                ns_st=list(st); ok=True; cc=c
                for i,a in zip(wins,dd):
                    v=st[i]+a
                    if v>n: ok=False; break
                    ns_st[i]=v; cc=cc*invf[a]
                if not ok: continue
                # check finishing windows reached n
                good=True
                for i in finishing:
                    if ns_st[i]!=n: good=False; break
                if not good: continue
                ns[tuple(ns_st)]+=cc
        state=ns
    total=state.get((n,)*8,Fraction(0))
    return total*Fraction(factorial(n))**8
import time,sys
t0=time.time(); out=[]
Nmax=int(sys.argv[1]) if len(sys.argv)>1 else 9
for n in range(Nmax+1):
    v=qn(n); assert v.denominator==1; out.append(int(v))
    print(f"q_{n} = {int(v)}   [{time.time()-t0:.1f}s]",flush=True)
