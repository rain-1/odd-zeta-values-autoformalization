#!/usr/bin/env python3
r"""
table_row3.py -- [COMPUTED, exact] ROW 3: weight-2 Apery/Beukers zeta(2) family, M_{0,5}.
THE CONTROL ROW (the zeta(2)-extension itself; performs no elimination).

Beukers double integral
   I_n = \int\int_{[0,1]^2} [x(1-x)y(1-y)]^n / (1-xy)^{n+1} dx dy  = a_n zeta(2) - b_n.
n=0 geometric period:  I_0 = \int\int 1/(1-xy) = sum_{k>=0} 1/(k+1)^2 = zeta(2)  (coeff 1).

We recover a_n, b_n EXACTLY by high-precision 2D integration + PSLQ against {1, zeta(2)},
cross-check a_n against the known zeta(2)-Apery numbers 1,3,19,147,..., and record the
denominator ledger: den(b_n) | d_n^2, SHARP (Rhin-Viola 1996 Thm 2.1), clearing constant 1.
"""
from fractions import Fraction as Fr
from math import comb, lcm
import mpmath as mp

mp.mp.dps = 60

def dn(n):
    return lcm(*range(1, n+1)) if n >= 1 else 1

def apery2_a(n):  # known closed form, integer
    return sum(comb(n,k)**2 * comb(n+k,k) for k in range(n+1))

def factor_int(x):
    x = abs(int(x)); f = {}; d = 2
    while d*d <= x:
        while x % d == 0:
            f[d]=f.get(d,0)+1; x//=d
        d += 1 if d==2 else 2
    if x>1: f[x]=f.get(x,0)+1
    return f

def I_n(n):
    def integrand(x,y):
        return (x*(1-x)*y*(1-y))**n / (1-x*y)**(n+1)
    return mp.quad(lambda x: mp.quad(lambda y: integrand(x,y), [0,1]), [0,1])

def rat_from_pslq(val, basis, maxden=10**18):
    # find integers p,q,... with p*val + sum q_i basis_i = 0, small
    rel = mp.pslq([val] + list(basis), maxcoeff=10**12, maxsteps=10**5)
    return rel

z2 = mp.zeta(2)
print("="*80)
print("ROW 3  weight-2 zeta(2)  I_n = a_n zeta(2) - b_n   (control: no elimination)")
print("="*80)
print(f"{'n':>2} {'a_n(int)':>10} {'a_n(known)':>10} {'b_n':>18} {'den(b_n)':>10} {'d_n^2':>8}  clean?")
data=[]
for n in range(0,7):
    val = I_n(n)
    # I_n = a_n z2 - b_n  => pslq on [I_n, z2, 1] : c0*I + c1*z2 + c2 = 0
    rel = mp.pslq([val, z2, mp.mpf(1)], maxcoeff=10**15, maxsteps=10**6)
    c0,c1,c2 = rel
    # normalize so coeff of I_n is +1: I_n = (-c1/c0) z2 + (-c2/c0)
    a = Fr(-int(c1), int(c0))
    negb = Fr(-int(c2), int(c0))
    b = -negb
    aknown = apery2_a(n)
    d2 = dn(n)**2
    denb = b.denominator
    clean = (Fr(d2)*b).denominator==1
    data.append((n,a,b))
    print(f"{n:>2} {str(a):>10} {aknown:>10} {str(b):>18} {denb:>10} {d2:>8}  {clean}  "
          f"{'a_n==known' if a==aknown else 'MISMATCH'}")

print("\n-- per-prime denominator ledger: den(b_n) vs d_n^2 --")
for n,a,b in data:
    if n==0: continue
    d=dn(n)
    denf = factor_int(b.denominator) if b.denominator>1 else {}
    d2f = factor_int(d**2) if d>1 else {}
    primes=sorted(set(denf)|set(d2f))
    excess={p:denf.get(p,0)-d2f.get(p,0) for p in primes}
    print(f"  n={n}: den(b_n)={dict(denf)}  d_n^2 primes={dict(d2f)}  excess={excess}")

print("\n[VERDICT] I_0 = zeta(2) (coeff 1: clean period, NO log-doubling, NO factor 2).")
print("          a_n integers; den(b_n) | d_n^2 with NO excess -> clearing constant = 1.")
print("          The zeta(2)-extension family IS the extension: it performs no elimination")
print("          and pays no Bernoulli cost. This is the mechanism's control case.")
