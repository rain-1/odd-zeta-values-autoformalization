"""zeta7_residue_ckpt_gen.py -- exact shell-sum checkpoints for I_n (rigorous lower bounds).

Usage: python3 zeta7_residue_ckpt_gen.py N NMAX     (default N=3, NMAX=40)

Writes worthiness/zeta7_residue_ckpt/I{n}_shells.json:
  {"n":3, "Nmax":40, "shells":[["num","den"],...]}   shell[K]=exact sum over max index==K.
Cumulative S_N = sum_{K<=N} shell[K] is an EXACT rational, a rigorous lower bound for I_n
(all terms positive), climbing to I_n.  Chunked by shell so the file can be extended.
"""
import sys, os, json
from fractions import Fraction as F
from math import comb, factorial
from functools import lru_cache

HERE = os.path.dirname(os.path.abspath(__file__))
CK = os.path.join(HERE, "zeta7_residue_ckpt"); os.makedirs(CK, exist_ok=True)

@lru_cache(None)
def Bab(a,b): return F(factorial(a-1)*factorial(b-1), factorial(a+b-1))
def blocks(n):
    @lru_cache(None)
    def G2(p): return sum(F((-1)**k)*comb(p,k)*Bab(n+1+k,n+1)**2 for k in range(p+1))
    @lru_cache(None)
    def H2(q,r): return sum(F((-1)**j)*comb(q,j)*Bab(n+j+1,n+1)*Bab(n+j+1,n+r+1) for j in range(q+1))
    return G2,H2

def shells(n, Nmax):
    G2,H2=blocks(n); Cn=[comb(n+x,x) for x in range(Nmax+1)]
    sh=[F(0)]*(Nmax+1)
    for a in range(Nmax+1):
        for b in range(Nmax+1):
            Cab=Cn[a]*Cn[b]; g=G2(a+b); B1=Bab(n+a+b+1,n+1); mab=max(a,b)
            for c in range(Nmax+1):
                mabc=max(mab,c)
                for d in range(Nmax+1):
                    t=Cab*Cn[c]*Cn[d]*g*H2(b+c,d)*B1*Bab(2*n+2+a+b+c+d,n+1)*Bab(n+b+c+d+1,n+1)
                    sh[max(mabc,d)]+=t
    return sh

if __name__=="__main__":
    n=int(sys.argv[1]) if len(sys.argv)>1 else 3
    Nmax=int(sys.argv[2]) if len(sys.argv)>2 else 40
    sh=shells(n,Nmax)
    out={"n":n,"Nmax":Nmax,"shells":[[str(x.numerator),str(x.denominator)] for x in sh]}
    fn=os.path.join(CK, f"I{n}_shells.json")
    json.dump(out, open(fn,"w"))
    # report cumulative lower bounds
    tot=F(0)
    for K in range(Nmax+1):
        tot+=sh[K]
        if K in (10,20,30,Nmax):
            print(f"  n={n} S_{K} = {float(tot):.12e}  (exact rational, {len(str(tot.numerator))}/{len(str(tot.denominator))} digits)")
    print("wrote", fn)
