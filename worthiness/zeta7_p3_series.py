"""P3 verification: all-positive 4-fold series for I_n, exact Fraction partial sums.
Reuses the DERIVED+VERIFIED representation from zeta7_barnes_num1.py.
Partial sums S_N over the box [0,N]^4 are rigorous LOWER bounds for I_n
(every term is a positive rational; the integrand is >=0).

I_n = sum_{a,b,c,d>=0} C(n+a,a)C(n+b,b)C(n+c,c)C(n+d,d)
      * G2(a+b) * H2(b+c,d)
      * B(n+a+b+1,n+1) * B(2n+2+a+b+c+d,n+1) * B(n+b+c+d+1,n+1)
"""
from fractions import Fraction as F
from math import comb, factorial
import sys

def Bab(a,b):  # Euler Beta B(a,b) exact for positive integers
    return F(factorial(a-1)*factorial(b-1), factorial(a+b-1))

def make(n):
    from functools import lru_cache
    @lru_cache(None)
    def B(a,b): return Bab(a,b)
    @lru_cache(None)
    def G2(p):
        return sum(F((-1)**k)*comb(p,k)*B(n+1+k,n+1)**2 for k in range(p+1))
    @lru_cache(None)
    def H2(q,r):
        return sum(F((-1)**j)*comb(q,j)*B(n+j+1,n+1)*B(n+j+1,n+r+1) for j in range(q+1))
    return B,G2,H2

def Isum_cumulative(n,Nmax,report):
    """Return dict N-> exact partial sum over [0,N]^4, for N in `report`.
    Single pass over [0,Nmax]^4, bucketing each term by K=max(a,b,c,d)."""
    B,G2,H2=make(n)
    Cn=[comb(n+x,x) for x in range(Nmax+1)]
    shell=[F(0) for _ in range(Nmax+1)]
    for a in range(Nmax+1):
        for b in range(Nmax+1):
            Cab=Cn[a]*Cn[b]; g=G2(a+b); Bab1=B(n+a+b+1,n+1)
            mab=a if a>b else b
            for c in range(Nmax+1):
                mabc=mab if mab>c else c
                for d in range(Nmax+1):
                    term=Cab*Cn[c]*Cn[d]*g*H2(b+c,d)*Bab1*B(2*n+2+a+b+c+d,n+1)*B(n+b+c+d+1,n+1)
                    K=mabc if mabc>d else d
                    shell[K]+=term
    out={}; tot=F(0); rs=set(report)
    for K in range(Nmax+1):
        tot+=shell[K]
        if K in rs: out[K]=tot
    return out

if __name__=="__main__":
    n=int(sys.argv[1]); Nmax=int(sys.argv[2])
    report=[int(x) for x in sys.argv[3].split(",")] if len(sys.argv)>3 else [Nmax]
    res=Isum_cumulative(n,Nmax,report)
    for N in sorted(res):
        v=res[N]
        print(f"n={n} N={N:3d} S_N={float(v):.15e}  exact_num_den_digits={len(str(v.numerator))},{len(str(v.denominator))}")
