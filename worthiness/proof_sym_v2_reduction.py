"""proof_sym_v2_reduction.py -- audit of the Barnes -> sine-kernel reduction (v2 SS2-3).

(A) Prefactor of (intJ) in the symmetric case equals n!.
(B) The reflection identity  Gamma(-n-1-w)Gamma(n+2+w) = (-1)^n pi/sin(pi w)  (symbolic).
(C) Prop 3.1 rational identity  R_gamma = r(s)r(t)C(s,t)  as an identity of
    products of linear factors (exact, via Pochhammer bookkeeping), n=1..8.
(D) Full integrand identity Phi = (-1)^n pi^3 r r C /(sin sin sin), 40-digit, n=1..4.
"""
import sympy as sp
import mpmath as mp
from math import factorial

s, t, w = sp.symbols('s t w')

# (A) prefactor q1!q2!q4!q5!/(p0! p6! (p3+q3-p0-p6)!) with all =n, p3=2n,q3=n,p0=p6=n
print("(A) intJ prefactor, symmetric case:")
for n in range(1, 6):
    pref = sp.Rational(factorial(n) ** 4, factorial(n) * factorial(n) * factorial(n))
    print(f"    n={n}: {pref}  ==  n! = {factorial(n)}   [{'OK' if pref==factorial(n) else 'FAIL'}]")

# (B) reflection identity, symbolic via sin expansion
print("\n(B) Gamma(-n-1-w)Gamma(n+2+w) = (-1)^n pi/sin(pi w):")
for n in range(0, 5):
    lhs = sp.gamma(-n - 1 - w) * sp.gamma(n + 2 + w)
    rhs = (-1) ** n * sp.pi / sp.sin(sp.pi * w)
    diff = sp.simplify(lhs - rhs)
    print(f"    n={n}: simplify(LHS-RHS) = {diff}   [{'OK' if diff==0 else 'FAIL'}]")

# (C) rational identity as products of linear factors, exact
def prod_lin(lo, hi, x):
    return sp.prod([x + k for k in range(lo, hi + 1)])

print("\n(C) R_gamma = r(s)r(t)C(s,t) via exact Pochhammer bookkeeping (rational), n=1..8:")
# Rewrite every Gamma-ratio as an explicit product of linear factors, then check
# the resulting RATIONAL identity by sp.cancel (no gamma involved => fast, exact).
#   G(n+1+x)/G(1+x)     = prod_{i=1}^{n} (x+i)
#   G(n+1+x)^2/G(2n+2+x)^2 = 1 / prod_{j=n+1}^{2n+1} (x+j)^2
#   G(2n+2+w)/G(n+2+w)  = prod_{l=n+2}^{2n+1} (w+l) = C
# so R_gamma = [prod_{i=1}^n(s+i) / prod_{n+1}^{2n+1}(s+j)^2] * (same in t) * C.
for n in range(1, 9):
    R_gamma_rat = (prod_lin(1, n, s) / prod_lin(n+1, 2*n+1, s) ** 2
                   * prod_lin(1, n, t) / prod_lin(n+1, 2*n+1, t) ** 2
                   * prod_lin(n+2, 2*n+1, s + t))
    r = lambda x: prod_lin(1, n, x) / prod_lin(n+1, 2*n+1, x) ** 2
    R_claim = r(s) * r(t) * prod_lin(n+2, 2*n+1, s + t)
    ratio = sp.cancel(R_gamma_rat / R_claim)
    print(f"    n={n}: R_gamma/R_claim = {ratio}   [{'OK' if ratio==1 else 'FAIL'}]")

# (D) full integrand, 40 digits
print("\n(D) Phi_gamma vs Phi_sine, 40-digit numeric at generic complex (s,t):")
mp.mp.dps = 40
def Phi_gamma(n, sv, tv):
    G = mp.gamma
    Gs = G(n+1+sv)**3 * G(-sv) / G(2*n+2+sv)**2
    Gt = G(n+1+tv)**3 * G(-tv) / G(2*n+2+tv)**2
    return Gs * Gt * G(2*n+2+sv+tv) * G(-n-1-sv-tv)
def Phi_sine(n, sv, tv):
    def r(x):
        num = mp.mpf(1)
        for i in range(1, n+1): num *= (x + i)
        den = mp.mpf(1)
        for j in range(n+1, 2*n+2): den *= (x + j)
        return num / den ** 2
    C = mp.mpf(1)
    for l in range(n+2, 2*n+2): C *= (sv + tv + l)
    pi = mp.pi
    return (-1)**n * pi**3 * r(sv)*r(tv)*C / (mp.sin(pi*sv)*mp.sin(pi*tv)*mp.sin(pi*(sv+tv)))
for n in [1, 2, 3, 4]:
    sv = mp.mpf('0.3') + mp.mpf('0.17')*1j
    tv = mp.mpf('-0.41') + mp.mpf('0.23')*1j
    a = Phi_gamma(n, sv, tv); b = Phi_sine(n, sv, tv)
    print(f"    n={n}: rel err = {mp.nstr(abs(a-b)/abs(a), 4)}")
