from fractions import Fraction as F
from math import comb, factorial
import mpmath as mp
mp.mp.dps=120
def Bab(a,b): return F(factorial(a-1)*factorial(b-1), factorial(a+b-1))
def make(n):
    from functools import lru_cache
    @lru_cache(None)
    def B(a,b): return Bab(a,b)
    @lru_cache(None)
    def G2(p): return sum(F((-1)**k)*comb(p,k)*B(n+1+k,n+1)**2 for k in range(p+1))
    @lru_cache(None)
    def H2(q,r): return sum(F((-1)**j)*comb(q,j)*B(n+j+1,n+1)*B(n+j+1,n+r+1) for j in range(q+1))
    return B,G2,H2
def partial_sums(n,Nmax):
    B,G2,H2=make(n)
    # accumulate by shell m=max(a,b,c,d); store cumulative S(N) as mpf
    from collections import defaultdict
    shell=defaultdict(lambda: mp.mpf(0))
    for a in range(Nmax+1):
        Ca=comb(n+a,a)
        for b in range(Nmax+1):
            Cab=Ca*comb(n+b,b); g=(lambda f: mp.mpf(f.numerator)/mp.mpf(f.denominator))(G2(a+b)); Bab1=(lambda f: mp.mpf(f.numerator)/mp.mpf(f.denominator))(B(n+a+b+1,n+1))
            for c in range(Nmax+1):
                Cabc=Cab*comb(n+c,c)
                for d in range(Nmax+1):
                    m=max(a,b,c,d)
                    term=Cabc*comb(n+d,d)*g*(lambda f: mp.mpf(f.numerator)/mp.mpf(f.denominator))(H2(b+c,d))*Bab1*(lambda f: mp.mpf(f.numerator)/mp.mpf(f.denominator))(B(2*n+2+a+b+c+d,n+1))*(lambda f: mp.mpf(f.numerator)/mp.mpf(f.denominator))(B(n+b+c+d+1,n+1))
                    shell[m]+=term
    S=[]; acc=mp.mpf(0)
    for m in range(Nmax+1):
        acc+=shell[m]; S.append(acc)
    return S
def wynn(seq):
    # Wynn epsilon; return best estimate
    n=len(seq); e=[[mp.mpf(0)]*(n+1) for _ in range(n+1)]
    for i in range(n): e[i][0]=seq[i]
    best=seq[-1]
    for k in range(1,n):
        for i in range(n-k):
            d=e[i+1][k-1]-e[i][k-1]
            e[i][k]=e[i+1][k-2] + (1/d if d!=0 else mp.mpf('1e99'))
        if (n-k)>0 and k%2==0: best=e[0][k]
    return e
n=1
z2,z3,z5,z7=mp.zeta(2),mp.zeta(3),mp.zeta(5),mp.zeta(7)
exact=(61*mp.mpf(75)/4*z7-900*z5-220)-(549*z5-600*z3+152)*z2
S=partial_sums(n,45)
print("n=1 exact=",mp.nstr(exact,25))
print("raw S(45)=",mp.nstr(S[-1],25)," err=",mp.nstr(exact-S[-1],3))
e=wynn(S)
# report diagonal even-order estimates
for k in range(2,44,2):
    if 0 < len(e[0]) and k < len(e[0]) and e[0][k]!=0:
        err=exact-e[0][k]
        if abs(err)>0: print(f"  wynn k={k:2d} est_err={mp.nstr(err,3)}")
