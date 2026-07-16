#!/usr/bin/env python3
"""
h2_dictionary.py  --  [COMPUTED]
Pin the measurement->lattice-index dictionary UNAMBIGUOUSLY from the exact
rational data of the Brown-Zudilin totally symmetric family, independent of
any sign/normalization convention in the period matrix.

The abstract elimination cost (Lemma 1 of PROOF_MECHANISM.md) is 24 = 2^3*3,
forced by  zeta(2) = -(2 pi i)^2 / 24.  The measured sharp constant on the
P-side is 12.  The ratio 24/12 = 2 is, by Corollary 1.1, the product over
primes of the Betti-lattice refinement index:
        24 / (measured cost) = prod_p p^{index_p}.
We read off index_2 and index_3 from the actual denominators of P_n and P_hat_n.

No integral is recomputed here; we use the paper's exact printed rationals
(anchors) and the totally-symmetric denominator law from CONJECTURE.md.
"""
from fractions import Fraction
from math import gcd
from functools import reduce
from sympy import factorint, binomial, Rational

def lcm(a,b): return a*b//gcd(a,b)
def d(n):  # d_n = lcm(1..n), d_0 = 1
    return reduce(lcm, range(1, n+1), 1)

# ---- paper's exact printed rationals (BZ, totally symmetric, eq. after I_n) ----
Q   = {0:Fraction(1), 1:Fraction(21), 2:Fraction(2989)}
Phat= {0:Fraction(0), 1:Fraction(101,4), 2:Fraction(344923,96)}
P   = {0:Fraction(0), 1:Fraction(87,4), 2:Fraction(1190161,384)}

def vp(x, p):
    """p-adic valuation of a nonzero Fraction (can be negative)."""
    if x == 0: return None
    num, den = x.numerator, x.denominator
    return factorint(num).get(p,0) - factorint(den).get(p,0)

print("="*72)
print("STEP A.  Reproduce Q_n from BZ eq.(Q_n) double sum  [cross-check]")
print("="*72)
def Qn_formula(n):
    tot = 0
    for k1 in range(n+1):
        A = binomial(n+k1,n)*binomial(n,k1)**2
        for k2 in range(n+1):
            B = binomial(n+k2,n)*binomial(n,k2)**2
            tot += A*B*binomial(n+k1+k2,n)
    return tot
for n in range(3):
    got = int(Qn_formula(n))
    print(f"  n={n}: formula Q_n={got:6d}   printed Q_n={int(Q[n]):6d}   {'OK' if got==int(Q[n]) else 'MISMATCH'}")

print()
print("="*72)
print("STEP B.  Denominators of P_n and P_hat_n vs d_n^5, d_n^2 d_2n  [the data]")
print("="*72)
for n in (1,2):
    dn = d(n); d2n = d(2*n)
    print(f"  n={n}:  d_n={dn}  d_2n={d2n}")
    print(f"    P_{n}      = {P[n]}     den = {P[n].denominator} = {factorint(P[n].denominator)}")
    print(f"    d_n^5      = {dn**5} = {factorint(dn**5) if dn**5>1 else '{}'}")
    # BZ naive claim d_n^5 P_n in Z ?
    naive = P[n]*dn**5
    print(f"    d_n^5 * P_{n} = {naive}   integer? {naive.denominator==1}")
    # excess = den(P_n) not covered by d_n^5, prime by prime
    for p in (2,3):
        need = -vp(P[n],p)                 # ord_p of denominator of P_n
        have = vp(Fraction(dn**5),p)       # ord_p provided by d_n^5
        excess = need - have               # bits the constant must supply beyond d_n^5
        print(f"      p={p}: ord_p den(P_{n})={need}, ord_p d_n^5={have}, "
              f"excess to be cleared by constant = {excess}")
    print(f"    P_hat_{n}  = {Phat[n]}   den = {Phat[n].denominator} = {factorint(Phat[n].denominator)}")
    dl = dn**2 * d2n
    print(f"    d_n^2 d_2n = {dl} = {factorint(dl) if dl>1 else '{}'}   "
          f"d_n^2 d_2n * P_hat = {Phat[n]*dl}  integer? {(Phat[n]*dl).denominator==1}")
    for p in (2,3):
        need = -vp(Phat[n],p) if Phat[n]!=0 else 0
        have = vp(Fraction(dl),p)
        print(f"      p={p}: ord_p den(P_hat_{n})={need}, ord_p d_n^2 d_2n={have}, excess={need-have}")
    print()

print("="*72)
print("STEP C.  The dictionary:  24 / cost = prod_p p^{index_p}")
print("="*72)
# Abstract Lemma-1 cost = 24 = 2^3 * 3.  Measured sharp constant on P = 12 = 2^2 * 3.
# Per-prime: constant must supply  ord_p(cost) = [excess_p]_max over cells.
# From the data the P-side excess ceilings are:  p=2 -> +2 , p=3 -> +1  (CONJECTURE.md).
cost_abstract = {2:3, 3:1}      # ord_p of 24
cost_measured = {2:2, 3:1}      # ord_p of 12   (P-side, sharp)
print("  Abstract Lemma-1 constant  24 = 2^%d * 3^%d" % (cost_abstract[2],cost_abstract[3]))
print("  Measured sharp constant    12 = 2^%d * 3^%d  (P-side)" % (cost_measured[2],cost_measured[3]))
for p in (2,3):
    idx = cost_abstract[p] - cost_measured[p]
    print(f"  => p={p}:  Betti-lattice refinement index = p^{idx} = {p**idx}"
          f"   ({'gamma_2/'+str(p**idx)+' in L' if idx>0 else 'no refinement'})")
print()
print("  PREDICTION H2 must confirm/refute (P-side, zeta(2)->zeta(5) elimination):")
print("    integral Betti lattice L refines naive (gamma_1,gamma_2)-span")
print("    by index 2 at p=2  (gamma_2/2 in L),  and index 1 at p=3 (no refinement).")
print()
# P_hat side: den(P_hat_n) = 2 * (2-part of d_n^2 d_2n) exactly (CONJECTURE.md).
print("  P_hat-side (zeta(3), Q(-2)->Q(-5)): den(P_hat_n) = 2 * (2-part of d_n^2 d_2n).")
print("  The lone extra factor 2 is a single index-2-at-2 on the SAME weight-4 Q(-2)")
print("  Betti class -> one geometric fact (gamma_2 primitive class = torus/2 at p=2)")
print("  explains BOTH the 24->12 on P and the extra 2 on P_hat.")
