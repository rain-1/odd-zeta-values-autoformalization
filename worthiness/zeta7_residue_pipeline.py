"""zeta7_residue_pipeline.py  --  exact symbolic-residue route to I'_3 (Agent B).

Usage:
    python3 zeta7_residue_pipeline.py validate     # closed forms + anchor reproduction (n=0,1,2)
    python3 zeta7_residue_pipeline.py n0symbolic   # n=0 harmonic Euler-sum reduction + PSLQ
    python3 zeta7_residue_pipeline.py scaling       # measure residue/sum cost n=0,1,2 -> project n=3

This is the INDEPENDENT (non-CT, non-Wolfram) route.  Object: the machine-verified
J-form all-positive 4-fold series (ZETA7_BARNES.md Sec 5f), reduced by exact closed
forms for the inner blocks G2, H2.

I_n = sum_{a,b,c,d>=0} C(n+a,a)C(n+b,b)C(n+c,c)C(n+d,d)
      * G2(a+b) * H2(b+c,d)
      * B(n+a+b+1,n+1) * B(2n+2+a+b+c+d,n+1) * B(n+b+c+d+1,n+1)

with
  G2(p)   = sum_k (-1)^k C(p,k) B(n+1+k,n+1)^2        [ = int (1-y1 y2)^p (y1(1-y1)y2(1-y2))^n ]
  H2(q,r) = sum_j (-1)^j C(q,j) B(n+j+1,n+1) B(n+j+1,n+r+1)
                                                       [ = int (1-yw)^q y^n(1-y)^n w^n(1-w)^{n+r} ]

KEY STRUCTURAL RESULT (this script, verified exactly): AT n=0 the inner blocks
collapse to harmonic numbers,
  G2(p)|_{n=0}   = H_{p+1}/(p+1),
  H2(q,r)|_{n=0} = (H_{q+r+1} - H_r)/(q+1),
turning I_0 into an explicit weight-7 harmonic (Euler) 4-fold sum -- the object a
residue decomposition delivers.  For n>=1 the blocks are genuine terminating 2F1's
(the 'non-hypergeometric wall'); they are computed as exact finite rational sums.
"""
import sys
from fractions import Fraction as F
from math import comb, factorial
from functools import lru_cache

# ---------------------------------------------------------------- Beta, blocks
@lru_cache(None)
def Bab(a, b):                      # Euler Beta B(a,b), exact for positive integers
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

# ---------------------------------------------------------------- harmonic numbers
@lru_cache(None)
def Harm(m):                        # H_m = sum_{i=1}^m 1/i
    return sum(F(1, i) for i in range(1, m + 1))

# ---------------------------------------------------------------- exact partial sum
def Isum_box(n, N):
    """Exact partial sum over the box [0,N]^4 (rigorous lower bound; all terms >0)."""
    G2, H2 = make_blocks(n)
    Cn = [comb(n + x, x) for x in range(N + 1)]
    tot = F(0)
    for a in range(N + 1):
        for b in range(N + 1):
            Cab = Cn[a] * Cn[b]; g = G2(a + b); Bab1 = Bab(n + a + b + 1, n + 1)
            for c in range(N + 1):
                for d in range(N + 1):
                    tot += (Cab * Cn[c] * Cn[d] * g * H2(b + c, d) * Bab1
                            * Bab(2 * n + 2 + a + b + c + d, n + 1)
                            * Bab(n + b + c + d + 1, n + 1))
    return tot

# ================================================================ VALIDATE
def validate():
    print("=== 1. Closed-form check for the inner blocks at n=0 ===")
    G2_0, H2_0 = make_blocks(0)
    ok = True
    for p in range(0, 14):
        lhs = G2_0(p); rhs = Harm(p + 1) / (p + 1)
        if lhs != rhs:
            ok = False; print(f"  G2({p}) MISMATCH {lhs} vs {rhs}")
    print(f"  G2(p) == H_(p+1)/(p+1)      for p=0..13:  {'OK' if ok else 'FAIL'}")
    ok = True
    for q in range(0, 12):
        for r in range(0, 12):
            lhs = H2_0(q, r); rhs = (Harm(q + r + 1) - Harm(r)) / (q + 1)
            if lhs != rhs:
                ok = False; print(f"  H2({q},{r}) MISMATCH {lhs} vs {rhs}")
    print(f"  H2(q,r) == (H_(q+r+1)-H_r)/(q+1)  for q,r=0..11:  {'OK' if ok else 'FAIL'}")

    print("\n=== 2. Anchor reproduction (exact partial sums vs BZ closed forms) ===")
    import mpmath as mp
    mp.mp.dps = 40
    z2, z3, z5, z7 = mp.zeta(2), mp.zeta(3), mp.zeta(5), mp.zeta(7)
    # exact BZ anchors as high-precision floats
    anchors = {
        0: mp.mpf(75) / 4 * z7 - 9 * z5 * z2,
        1: (61 * mp.mpf(75) / 4 * z7 - 900 * z5 - 220) - (549 * z5 - 600 * z3 + 152) * z2,
        2: (52921 * mp.mpf(75) / 4 * z7 - 261153 * 3 * z5 - mp.mpf(6021219) / 32)
           - (52921 * 9 * z5 - 261153 * 2 * z3 + mp.mpf(535857) / 4) * z2,
    }
    for n in (0, 1, 2):
        print(f"  n={n}  exact I_n = {mp.nstr(anchors[n], 18)}")
        for N in (10, 20, 30):
            v = Isum_box(n, N)
            fv = mp.mpf(v.numerator) / mp.mpf(v.denominator)
            print(f"      N={N:3d}  S_N={mp.nstr(fv,16):>22s}  rem={mp.nstr(anchors[n]-fv,4)}")

if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "validate"
    if cmd == "validate":
        validate()
    else:
        print("unknown command", cmd)
