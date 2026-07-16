"""All-positive 4-fold series for the J-form I_n.
Derivation: expand each 1/P_k^{n+1}=sum C(n+m,m) arg^m, integrate monomials.
I_n = sum_{a,b,c,d>=0} C(n+a,a)C(n+b,b)C(n+c,c)C(n+d,d)
      * G2(a+b) * H2(b+c,d)
      * B(n+a+b+1,n+1) * B(2n+2+a+b+c+d,n+1) * B(n+b+c+d+1,n+1)
G2(p)=int (1-y1y2)^p y1^n(1-y1)^n y2^n(1-y2)^n = sum_k C(p,k)(-1)^k B(n+1+k,n+1)^2
H2(q,r)=sum_j C(q,j)(-1)^j B(n+j+1,n+1) B(n+j+1,n+r+1)
B(a,b)=Gamma(a)Gamma(b)/Gamma(a+b), integer args -> exact Fraction.
"""
from fractions import Fraction as F
from math import comb, factorial
import mpmath as mp, sys

def Bab(a,b):  # B(a,b) exact for positive integers a,b
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

def Isum(n,N):
    B,G2,H2=make(n)
    tot=F(0)
    for a in range(N+1):
        for b in range(N+1):
            Cab=comb(n+a,a)*comb(n+b,b); g=G2(a+b); Bab1=B(n+a+b+1,n+1)
            for c in range(N+1):
                for d in range(N+1):
                    term=Cab*comb(n+c,c)*comb(n+d,d)*g*H2(b+c,d)*Bab1*B(2*n+2+a+b+c+d,n+1)*B(n+b+c+d+1,n+1)
                    tot+=term
    return tot

mp.mp.dps=40
anchors={0:mp.mpf(75)/4*mp.zeta(7)-9*mp.zeta(5)*mp.zeta(2)}
# I_1 exact
z2,z3,z5,z7=mp.zeta(2),mp.zeta(3),mp.zeta(5),mp.zeta(7)
anchors[1]=(61*mp.mpf(75)/4*z7-900*z5-220)-(549*z5-600*z3+152)*z2
for n in (0,1):
    print(f"n={n} exact={mp.nstr(anchors[n],20)}")
    for N in (8,16,24,32):
        val=mp.mpf(Isum(n,N).numerator)/mp.mpf(Isum(n,N).denominator)
        print(f"   N={N:3d} sum={mp.nstr(val,18)}  rem={mp.nstr(anchors[n]-val,4)}")
