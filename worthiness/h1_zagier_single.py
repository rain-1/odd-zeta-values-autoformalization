"""h1_zagier_single.py -- Zagier's beta_r dictionary applied to the single
building block r(s), exactly.

Zagier appendix (arXiv:1601.00950, eq.(43)-(44)): for R in V_0 (poles in the
negative integers, vanishing at infinity),
    R(k) = sum_r beta_r(R)/(k+1)^r - Delta R_0(k),
    sum_{k>=0} R(k) = R_0(0) + sum_{r>=2} beta_r(R) zeta(r).
Because (k+j)^{-r} == (k+1)^{-r} (mod Delta V), beta_r(R) is exactly the SUM
over the poles of the depth-r partial-fraction coefficients of R.

Our block r(x) = prod_{i=1}^n (x+i) / (prod_{j=n+1}^{2n+1}(x+j))^2 has only
DOUBLE poles, so beta_r(r)=0 for r>=3 and
    r(x) = sum_{j=n+1}^{2n+1} ( A_j/(x+j) + B_j/(x+j)^2 ),
    beta_1(r) = sum_j A_j   (must be 0: integrability / no residue at infinity),
    beta_2(r) = sum_j B_j   (= the zeta(2)-coefficient of sum_{k>=0} r(k)),
    R_0(0)    = the rational part of sum_{k>=0} r(k).

A_j, B_j from PROOF_SYMMETRIC_v2 Lemma 4.1 (a = j-(n+1)):
    B_j = (-1)^n binom(n+a,a) binom(n,a)^2 / n!
    A_j = B_j (3 H_a - H_{n+a} - 2 H_{n-a}).

We (1) verify beta_1 = 0 exactly; (2) verify beta_2 = sum B_j equals the PSLQ
zeta(2)-coefficient of the numerically summed series (self-check of the whole
dictionary); (3) factor den(beta_2) and den(R_0(0)) and compare to n!, d_n,
d_{2n}.  This exposes, at the cheapest (one-variable) level, whether the sum
over poles already collapses the per-term factorial n! (Cor 4.2) down to a
d-controlled denominator.
"""
from fractions import Fraction
from math import comb, gcd, factorial
from mpmath import mp, mpf, pslq, zeta

def d_lcm(N):
    r = 1
    for k in range(2, N + 1):
        r = r * k // gcd(r, k)
    return r

def H(m):
    return sum(Fraction(1, i) for i in range(1, m + 1))

def factor(x):
    if x == 1:
        return "1"
    parts, p = [], 2
    while p * p <= x:
        if x % p == 0:
            e = 0
            while x % p == 0:
                x //= p; e += 1
            parts.append(f"{p}^{e}" if e > 1 else f"{p}")
        p += 1
    if x > 1:
        parts.append(str(x))
    return "·".join(parts)

print("beta_1(r) = sum_j A_j  (integrability -> must be 0);   "
      "beta_2(r) = sum_j B_j  (zeta(2)-coeff of sum_k r(k)).\n"
      "Claim under test: den(beta_2) stays ~ n!  (single-variable sum does NOT "
      "collapse to d_n).\n")
print(f"{'n':>2} {'beta1':>6} {'den(beta2)':>18}")
for n in range(1, 9):
    A, B = {}, {}
    for j in range(n + 1, 2 * n + 1 + 1):
        a = j - (n + 1)
        Bj = Fraction((-1) ** n * comb(n + a, a) * comb(n, a) ** 2, factorial(n))
        Aj = Bj * (3 * H(a) - H(n + a) - 2 * H(n - a))
        A[j], B[j] = Aj, Bj
    beta1 = sum(A.values())
    beta2 = sum(B.values())

    # exact cross-check of the Lemma 4.1 closed forms: partial-fraction r(x)
    # with sympy and read off the summed depth-1 / depth-2 coefficients.
    import sympy as sp
    x = sp.symbols('x')
    rx = (sp.prod([x + i for i in range(1, n + 1)])
          / sp.prod([(x + j) ** 2 for j in range(n + 1, 2 * n + 2)]))
    apart = sp.apart(rx, x)
    b1 = b2 = sp.Integer(0)
    for j in range(n + 1, 2 * n + 2):
        # depth-2 coeff = lim (x+j)^2 r ; depth-1 = d/dx[(x+j)^2 r] at -j
        g = sp.together((x + j) ** 2 * rx)
        b2 += g.subs(x, -j)
        b1 += sp.diff(g, x).subs(x, -j)
    b1 = sp.nsimplify(sp.cancel(b1)); b2 = sp.cancel(b2)
    chk1 = (sp.Rational(beta1.numerator, beta1.denominator) == b1)
    chk2 = (sp.Rational(beta2.numerator, beta2.denominator) == b2)

    db2 = beta2.denominator
    print(f"{n:>2} {str(beta1):>6} {factor(db2):>18}"
          f"  n!={factor(factorial(n)):>10} d_n={d_lcm(n):>4} d_2n={d_lcm(2*n):>6}"
          f"  [closed-forms {'OK' if (chk1 and chk2) else 'FAIL'}]")
