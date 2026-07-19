"""zeta7_residue_hiprec.py -- high-precision evaluation of I_n via the reduced
harmonic/blocked series, using mpmath nsum acceleration to beat the algebraic wall.

Usage:
    python3 zeta7_residue_hiprec.py test0    # n=0: nested-nsum precision test vs exact
    python3 zeta7_residue_hiprec.py test     N DPS   # generic quick single-index probe

Idea: the raw 4-fold box sum converges like N^{-p} (p~1.2-2.3) -> PSLQ wall.
mpmath's nsum applies Richardson/Shanks/Euler-Maclaurin PER DIMENSION, so a nested
nsum can reach many digits from modest index depth IF the tail is a clean power law.
Inner blocks G2,H2 are exact rationals (cast to mpf at working precision).
"""
import sys
from fractions import Fraction as F
from math import comb, factorial
from functools import lru_cache
import mpmath as mp

@lru_cache(None)
def Bab(a, b):
    return F(factorial(a - 1) * factorial(b - 1), factorial(a + b - 1))

def make_blocks(n):
    @lru_cache(None)
    def G2(p):
        return sum(F((-1)**k) * comb(p, k) * Bab(n + 1 + k, n + 1)**2 for k in range(p + 1))
    @lru_cache(None)
    def H2(q, r):
        return sum(F((-1)**j) * comb(q, j) * Bab(n + j + 1, n + 1) * Bab(n + j + 1, n + r + 1)
                   for j in range(q + 1))
    return G2, H2

def test0(dps=40):
    mp.mp.dps = dps
    n = 0
    G2, H2 = make_blocks(n)
    # cast helpers to mpf
    def g2(p):
        v = G2(int(p)); return mp.mpf(v.numerator)/mp.mpf(v.denominator)
    def h2(q, r):
        v = H2(int(q), int(r)); return mp.mpf(v.numerator)/mp.mpf(v.denominator)
    def bab(a, b):
        v = Bab(int(a), int(b)); return mp.mpf(v.numerator)/mp.mpf(v.denominator)
    # summand at n=0 (all outer binomials =1)
    def T(a, b, c, d):
        a=int(a); b=int(b); c=int(c); d=int(d)
        return (g2(a+b) * h2(b+c, d) * bab(a+b+1,1) * bab(2+a+b+c+d,1) * bab(b+c+d+1,1))
    exact = mp.mpf(75)/4*mp.zeta(7) - 9*mp.zeta(5)*mp.zeta(2)
    print("exact I_0 =", mp.nstr(exact, dps-3))
    for meth in ('r', 'd'):
        try:
            val = mp.nsum(lambda a,b,c,d: T(a,b,c,d), [0,mp.inf],[0,mp.inf],[0,mp.inf],[0,mp.inf], method=meth)
            print(f"  nsum method={meth}: {mp.nstr(val,dps-3)}  err={mp.nstr(exact-val,4)}")
        except Exception as e:
            print(f"  nsum method={meth} FAILED: {e}")

if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "test0"
    if cmd == "test0":
        dps = int(sys.argv[2]) if len(sys.argv) > 2 else 30
        test0(dps)
