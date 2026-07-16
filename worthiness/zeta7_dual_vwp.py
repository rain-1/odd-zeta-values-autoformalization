#!/usr/bin/env python3
"""
SERIES identification for the Brown-Zudilin zeta(7) cellular family.

Target (BZ CellZeta.tex, lines 1456-1466), the zeta(2)=0 part I'_n:
    I'_n = A_n*(75/4)zeta(7) - B_n*3 zeta(5) - C_n
    (A_0,A_1,A_2)=(1,61,52921)
    (B_0,B_1,B_2)=(0,300,261153)
    (C_0,C_1,C_2)=(0,220,6021219/32)
I'_n has NO zeta(3); leading is pure zeta(7) at n=0.

Candidate: the paper's own very-well-poised series \tilde F_k (eq:10) with k=9,
which represents Q-linear forms in 1, zeta(3), zeta(5), zeta(7).

    \tilde F_k(b0;b1..bk) = sum_{mu>=0} (b0+2mu+2) *
        Gamma(b0+mu+2) prod_j Gamma(bj+mu+1)
        / ( mu! prod_j Gamma(b0-bj+mu+2) ) * (-1)^{(k+1)mu}

For k=9, (-1)^{10 mu}=+1. As a rational function of mu this is
    (b0+2mu+2) * prod_{i=1}^{b0+1}(mu+i) / prod_j prod_{i=bj+1}^{b0-bj+1}(mu+i)
Shift m=mu+1 (sum m>=1) and factor (b0+2mu+2)=2(m+b0/2):
    pref=2, halfshift=b0/2, C=0,
    num bases  0..b0
    den bases  bj..(b0-bj)   for each j
Fed to engine linear_form_coeffs which returns As[s]=coeff zeta(s), const.
"""
from fractions import Fraction as F
import sys
sys.path.insert(0, '/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from zn_check import linear_form_coeffs

# ---- exact target anchors (within-n, prefactor-independent ratios) ----
A = {0: F(1), 1: F(61), 2: F(52921)}
B = {0: F(0), 1: F(300), 2: F(261153)}
C = {0: F(0), 1: F(220), 2: F(6021219, 32)}
def target_ratios(n):
    # I'_n = A*(75/4) z7 - 3B z5 - C ; coeffs: cz7=(75/4)A, cz5=-3B, cconst=-C
    cz7 = F(75,4)*A[n]; cz5 = -3*B[n]; cconst = -C[n]
    r5 = cz5/cz7          # coeff(z5)/coeff(z7)
    rc = cconst/cz7       # const/coeff(z7)
    return r5, rc

def tildeF(b0, bs):
    k = len(bs)
    assert all(b0 >= 2*bj >= 0 for bj in bs), (b0, bs)
    num = list(range(0, b0+1))            # bases 0..b0
    den = []
    for bj in bs:
        den += list(range(bj, b0-bj+1))   # bases bj..b0-bj
    As, const = linear_form_coeffs(F(2), F(b0,2), num, den, C=0)
    return As, const

def decomp(b0, bs, label=""):
    As, const = tildeF(b0, bs)
    z = {s: As.get(s, F(0)) for s in range(1, 12)}
    z3, z5, z7, z9 = z[3], z[5], z[7], z[9]
    even = {s: z[s] for s in (2,4,6,8,10) if z[s] != 0}
    print(f"  {label}: b0={b0} bs={bs}")
    print(f"     const={const}")
    print(f"     z3={z3} z5={z5} z7={z7} z9={z9}")
    if even:
        print(f"     EVEN NONZERO (should vanish for VWP): {even}")
    other = {s: z[s] for s in range(1,12) if s not in (3,5,7) and z[s]!=0}
    if other:
        print(f"     nonzero outside {{3,5,7}}: {other}")
    # match to target: need z3==0, and ratios z5/z7, const/z7
    if z7 != 0:
        print(f"     r5=z5/z7={z5/z7}   rc=const/z7={const/z7}")
    return const, z3, z5, z7, z9

if __name__ == '__main__':
    print("TARGET within-n ratios (r5=coeffz5/coeffz7, rc=const/coeffz7):")
    for n in (0,1,2):
        r5, rc = target_ratios(n)
        print(f"   n={n}: r5={r5}  rc={rc}   (A={A[n]},B={B[n]},C={C[n]})")
    print()
    print("Test all-equal symmetric tilde F_9, small params:")
    # try b0=2b (min) and b0>2b, all bj=b
    for b in range(0, 4):
        for b0 in range(2*b, 2*b+5):
            try:
                decomp(b0, [b]*9, f"b={b}")
            except AssertionError:
                pass
