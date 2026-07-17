"""Accelerated (float64, numpy) partial sums of the all-positive 4-fold series.
G2/H2 precomputed EXACTLY (Fraction) then cast to float to avoid the internal
alternating-sum cancellation. Outer 4-fold sum is all-positive -> float64 safe.
Partial sums S_N over [0,N]^4 are (numerically) rigorous lower bounds for I_n.
"""
from fractions import Fraction as F
from math import comb, factorial
import numpy as np, sys, time

def Bab(a,b): return F(factorial(a-1)*factorial(b-1), factorial(a+b-1))

def precompute(n,Nmax):
    from functools import lru_cache
    @lru_cache(None)
    def B(a,b): return Bab(a,b)
    # beta arrays
    Bs  =[float(B(n+s+1,n+1))       for s in range(2*Nmax+1)]        # B(n+s+1,n+1)
    Bsig=[float(B(2*n+2+sig,n+1))   for sig in range(4*Nmax+1+2*n+2)] # B(2n+2+sig,n+1)
    Bu  =[float(B(n+u+1,n+1))       for u in range(3*Nmax+1)]        # B(n+u+1,n+1)
    Cn  =[float(comb(n+x,x))        for x in range(Nmax+1)]
    # G2[p]
    G2=[]
    for p in range(2*Nmax+1):
        v=sum(F((-1)**k)*comb(p,k)*B(n+1+k,n+1)**2 for k in range(p+1))
        G2.append(float(v))
    # H2[q][r], q in 0..2Nmax, r in 0..Nmax
    H2=[[0.0]*(Nmax+1) for _ in range(2*Nmax+1)]
    for q in range(2*Nmax+1):
        # precompute Bj=B(n+j+1,n+1) and per-r Bjr=B(n+j+1,n+r+1)
        for r in range(Nmax+1):
            v=sum(F((-1)**j)*comb(q,j)*B(n+j+1,n+1)*B(n+j+1,n+r+1) for j in range(q+1))
            H2[q][r]=float(v)
    return np.array(Bs),np.array(Bsig),np.array(Bu),np.array(Cn),np.array(G2),H2

def run(n,Nmax,report):
    t0=time.time()
    Bs,Bsig,Bu,Cn,G2,H2=precompute(n,Nmax)
    H2=[np.array(row) for row in H2]
    d=np.arange(Nmax+1)
    Cnd=Cn                                   # Cn[d]
    shell=np.zeros(Nmax+1)
    for a in range(Nmax+1):
        Ca=Cn[a]
        for b in range(Nmax+1):
            Cab=Ca*Cn[b]; g=G2[a+b]; bs=Bs[a+b]; pref_ab=Cab*g*bs
            mab=a if a>b else b
            for c in range(Nmax+1):
                pref=pref_ab*Cn[c]
                H2row=H2[b+c]                # length Nmax+1, indexed by d (r=d)
                sig0=a+b+c                   # + d ; Bsig[sig]=B(2n+2+sig,n+1)
                u0=b+c                       # + d  -> Bu index n+u+1 handled by array Bu[u]
                # inner over d (vector):
                inner=pref*Cnd*H2row*Bsig[sig0+d]*Bu[u0+d]
                mabc=mab if mab>c else c
                # d<=mabc -> shell[mabc]; d>mabc -> shell[d]
                shell[mabc]+=inner[:mabc+1].sum()
                if mabc<Nmax:
                    shell[mabc+1:]+=inner[mabc+1:]
    tot=np.cumsum(shell)
    print(f"# n={n} Nmax={Nmax} elapsed={time.time()-t0:.1f}s")
    for N in report:
        if N<=Nmax:
            print(f"n={n} N={N:4d} S_N={tot[N]:.15e}")
    return tot

if __name__=="__main__":
    n=int(sys.argv[1]); Nmax=int(sys.argv[2])
    report=[int(x) for x in sys.argv[3].split(",")] if len(sys.argv)>3 else list(range(0,Nmax+1,max(1,Nmax//10)))+[Nmax]
    run(n,Nmax,report)
