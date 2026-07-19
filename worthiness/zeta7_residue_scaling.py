"""zeta7_residue_scaling.py -- measured scaling of the exact residue/series route.

Usage: python3 zeta7_residue_scaling.py

Measures, for n=0,1,2:
 (i)  inner residue-block sizes (#terms in G2(a+b), H2(b+c,d)) -> per-tuple cost;
 (ii) raw box partial sums S_N (exact rational) and the convergence exponent p
      (err ~ C N^-p), to project the N needed for PSLQ-grade (~100-digit) precision.
This quantifies why the numeric/PSLQ shortcut on the residue series is walled, and
what an EXACT symbolic reduction (left-closure -> MZV) must instead accomplish.
"""
from fractions import Fraction as F
from math import comb, factorial, log
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

def shell_sums(n, Nmax):
    """Exact partial sums S_N over [0,N]^4 for N=0..Nmax (single pass, shell-bucketed)."""
    G2, H2 = make_blocks(n)
    Cn = [comb(n + x, x) for x in range(Nmax + 1)]
    shell = [F(0)] * (Nmax + 1)
    for a in range(Nmax + 1):
        for b in range(Nmax + 1):
            Cab = Cn[a] * Cn[b]; g = G2(a + b); Bab1 = Bab(n + a + b + 1, n + 1)
            mab = max(a, b)
            for c in range(Nmax + 1):
                mabc = max(mab, c)
                for d in range(Nmax + 1):
                    term = (Cab * Cn[c] * Cn[d] * g * H2(b + c, d) * Bab1
                            * Bab(2 * n + 2 + a + b + c + d, n + 1)
                            * Bab(n + b + c + d + 1, n + 1))
                    K = max(mabc, d)
                    shell[K] += term
    S = []; tot = F(0)
    for K in range(Nmax + 1):
        tot += shell[K]; S.append(tot)
    return S

if __name__ == "__main__":
    mp.mp.dps = 40
    print("=== inner residue-block sizes ===")
    print("  per outer tuple (a,b,c,d): G2 has (a+b+1) terms, H2 has (b+c+1) terms.")
    print("  box [0,N]^4 residue-sum cost ~ N^4 * O(N) rational ops = O(N^5).")
    print()
    anchors = {}
    z2, z3, z5, z7 = mp.zeta(2), mp.zeta(3), mp.zeta(5), mp.zeta(7)
    anchors[0] = mp.mpf(75)/4*z7 - 9*z5*z2
    anchors[1] = (61*mp.mpf(75)/4*z7 - 900*z5 - 220) - (549*z5 - 600*z3 + 152)*z2
    anchors[2] = (52921*mp.mpf(75)/4*z7 - 261153*3*z5 - mp.mpf(6021219)/32) \
                 - (52921*9*z5 - 261153*2*z3 + mp.mpf(535857)/4)*z2
    for n in (0, 1, 2):
        Nmax = 48
        S = shell_sums(n, Nmax)
        ex = anchors[n]
        print(f"=== n={n}  exact I_n = {mp.nstr(ex,16)} ===")
        pts = [16, 24, 32, 40, 48]
        for N in pts:
            v = mp.mpf(S[N].numerator)/mp.mpf(S[N].denominator)
            print(f"   N={N:3d}  err={mp.nstr(ex-v,6)}")
        # fit exponent from last 3 points: err ~ C N^-p
        errs = [float(ex - mp.mpf(S[N].numerator)/mp.mpf(S[N].denominator)) for N in pts]
        N1,N2,N3 = pts[-3], pts[-2], pts[-1]
        e1,e2,e3 = errs[-3], errs[-2], errs[-1]
        try:
            p = log(e2/e3)/log(float(N3)/N2)
            print(f"   fitted tail exponent p ~ {p:.3f}")
            # N to reach 1e-100: err = e3*(N/N3)^-p = 1e-100
            need = N3 * (e3/1e-100)**(1.0/p)
            print(f"   projected N for 1e-100 (PSLQ): ~1e{log(need)/log(10):.0f}   (terms ~ N^4)")
        except Exception as ex2:
            print("   fit failed", ex2)
        print()
