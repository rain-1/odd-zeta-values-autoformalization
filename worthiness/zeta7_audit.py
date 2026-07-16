"""
zeta7_audit.py  -- denominator audit of the Brown-Zudilin zeta(7) cellular
family on M_{0,10} (the "vanishing in the middle" permutation (10,2,4,1,6,3,8,5,9,7)),
totally symmetric version.

DATA PROVENANCE [VERIFIED, from paper]:
  /tmp/.../bz/2026-01-26_CellZeta.tex, lines ~1443-1467.  Brown-Zudilin print
  the exact linear forms I_n = I'_n + I''_n*zeta(2) for n=0,1,2, where
    I'_n  is a linear form in 1, zeta(5), zeta(7)   (obtained by setting zeta(2)=0)
    I''_n is a linear form in 1, zeta(3), zeta(5).

Their printed forms (verbatim):
  I_0  = (75/4) zeta7                         - 9 zeta5 zeta2
  I_1  = (61*75/4 zeta7 - 300*3 zeta5 - 220)  - (61*9 zeta5 - 300*2 zeta3 + 152) zeta2
  I_2  = (52921*75/4 zeta7 - 261153*3 zeta5 - 6021219/32)
                                              - (52921*9 zeta5 - 261153*2 zeta3 + 535857/4) zeta2

We DERIVE the shared-integer structure (see below) and run the per-prime ledger.
No existing repo files are modified.
"""
import sympy as sp
from sympy import Rational as R, Integer, factorint, ilcm

zeta2, zeta3, zeta5, zeta7 = sp.symbols('zeta2 zeta3 zeta5 zeta7')

# ---- exact data, exactly as BZ print it -------------------------------------
Ip = {   # I'_n : coefficients of (zeta7, zeta5, 1)
    0: (R(75,4)*1,          -3*0,          -0),
    1: (R(75,4)*61,         -3*300,        -220),
    2: (R(75,4)*52921,      -3*261153,     -R(6021219,32)),
}
Ipp = {  # I''_n : coefficients of (zeta5, zeta3, 1)
    0: (-9*1,               2*0,           -0),
    1: (-9*61,              2*300,         -152),
    2: (-9*52921,           2*261153,      -R(535857,4)),
}

# ---- the DERIVED shared-integer skeleton ------------------------------------
# I'_n  = (75/4) q_n zeta7  - 3 s_n zeta5 - P_n
# I''_n =    -9  q_n zeta5  + 2 s_n zeta3 - Phat_n
q    = {0:1,    1:61,    2:52921}
s    = {0:0,    1:300,   2:261153}
P    = {0:R(0), 1:R(220), 2:R(6021219,32)}
Phat = {0:R(0), 1:R(152), 2:R(535857,4)}

print("=== consistency of the DERIVED (q_n, s_n, P_n, Phat_n) skeleton with BZ's printed forms ===")
for n in range(3):
    a7,a5,a1 = Ip[n]
    assert a7 == R(75,4)*q[n], (n,'zeta7')
    assert a5 == -3*s[n],      (n,'zeta5 in I_prime')
    assert a1 == -P[n],        (n,'const in I_prime')
    b5,b3,b1 = Ipp[n]
    assert b5 == -9*q[n],      (n,'zeta5 in I_pp')
    assert b3 == 2*s[n],       (n,'zeta3 in I_pp')
    assert b1 == -Phat[n],     (n,'const in I_pp')
print("  OK: q_n appears as (75/4)q_n in zeta7 and -9 q_n in zeta5;")
print("      s_n appears as -3 s_n in zeta5 and +2 s_n in zeta3.  q,s integers.\n")

# ---- numeric consistency: I_n must be a *small* linear form ------------------
import mpmath as mp
mp.mp.dps = 60
z2,z3,z5,z7 = mp.zeta(2),mp.zeta(3),mp.zeta(5),mp.zeta(7)
def num(expr_tuple, basis):
    return sum(mp.mpf(str(sp.nsimplify(c))) * b if False else mp.mpf(sp.Float(c,50)) * b
               for c,b in zip(expr_tuple, basis))
print("=== numeric check: I_n = I'_n + I''_n zeta(2) should be SMALL (BZ) ===")
for n in range(3):
    a7,a5,a1 = Ip[n]; b5,b3,b1 = Ipp[n]
    Iprime = mp.mpf(sp.Float(a7,50))*z7 + mp.mpf(sp.Float(a5,50))*z5 + mp.mpf(sp.Float(a1,50))
    Ipp_v  = mp.mpf(sp.Float(b5,50))*z5 + mp.mpf(sp.Float(b3,50))*z3 + mp.mpf(sp.Float(b1,50))
    In     = Iprime + Ipp_v*z2
    print(f"  n={n}:  I'_n={mp.nstr(Iprime,8):>12}   I''_n={mp.nstr(Ipp_v,8):>12}"
          f"   I_n={mp.nstr(In,6):>12}   (|coef|~{abs(float(a7)):.3g})")
print()

# ---- the per-prime denominator ledger ---------------------------------------
def dn(n):  # lcm(1..n)
    v = 1
    for k in range(1, n+1):
        v = v*k//sp.igcd(v, k)
    return int(v)

def vprint(name, val):
    val = sp.nsimplify(val)
    num_, den_ = sp.fraction(sp.Rational(val))
    fd = factorint(den_)
    return f"{name}={val}  den={den_}={dict(fd) if fd else 1}"

print("=== ζ(7)-form I'_n coefficient denominators, vs d_n^7 ===")
for n in range(3):
    d = dn(n)
    a7,a5,a1 = Ip[n]
    den_all = ilcm(sp.fraction(sp.Rational(a7))[1],
                   sp.fraction(sp.Rational(a5))[1],
                   sp.fraction(sp.Rational(a1))[1])
    print(f"  n={n}  d_n={d}  d_n^7={d**7}={dict(factorint(d**7)) if d>1 else 1}")
    print("     ", vprint("[zeta7]", a7))
    print("     ", vprint("[zeta5]", a5))
    print("     ", vprint("[const]", a1))
    # clearing factor K so that K * d_n^7 * I'_n has integer coeffs
    need = den_all
    from math import gcd
    K = need // gcd(int(need), d**7)
    print(f"      common den of I'_n = {den_all}={dict(factorint(den_all)) if den_all>1 else 1};"
          f"  d_n^7 supplies {gcd(int(need),d**7)};  EXTRA clearing factor K={K}"
          f"={dict(factorint(K)) if K>1 else 1}")
print()

print("=== ζ(5) side of the ζ(2)-companion I''_n, vs d_n^5 ===")
for n in range(3):
    d = dn(n)
    b5,b3,b1 = Ipp[n]
    den_all = ilcm(sp.fraction(sp.Rational(b5))[1],
                   sp.fraction(sp.Rational(b3))[1],
                   sp.fraction(sp.Rational(b1))[1])
    from math import gcd
    K = int(den_all) // gcd(int(den_all), d**5)
    print(f"  n={n}  d_n^5={d**5}   common den(I''_n)={den_all}={dict(factorint(den_all)) if den_all>1 else 1}"
          f"   EXTRA K={K}={dict(factorint(K)) if K>1 else 1}")
    print("     ", vprint("[const P_n]", P[n]), "   ||  ", vprint("[const Phat_n]", Phat[n]))
print()

print("=== the constant terms alone (analog of BZ M_{0,8}: d_n^5 P_n ∈ Z ?) ===")
for n in range(3):
    d = dn(n)
    from math import gcd
    for nm, val, w in [("P_n (wt7 side)", P[n], 7), ("Phat_n (wt5 side)", Phat[n], 5)]:
        den = sp.fraction(sp.Rational(val))[1]
        K = int(den)//gcd(int(den), d**w)
        print(f"  n={n}  {nm}: den={den}={dict(factorint(den)) if den>1 else 1}"
              f"   vs d_n^{w}={d**w};  d_n^{w}*val extra factor K={K}={dict(factorint(K)) if K>1 else 1}")
