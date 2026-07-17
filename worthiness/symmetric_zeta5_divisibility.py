"""Exact arithmetic laboratory for the symmetric Brown--Zudilin denominator law.

For Zudilin's rational function R_n(t), compute its partial-fraction
coefficients a[i,j] at t=-j without symbolic algebra.  Multiplication by
-t(t+n) gives the companion coefficients.  Eliminating zeta(3) then produces

    F_n(t) = 12/binom(2n,n) * (wtilde_n + w_n*t*(t+n)) * R_n(t),

whose sum is 12/binom(2n,n) * (q_n*zeta(5)-p_n).  Therefore the target
12*d_n^5*P_n in Z is exactly the assertion that d_n^5 times the rational
part of sum F_n(t) is integral.

This script is proof-discovery code: every computation is exact Fraction
arithmetic, but finite verification is not presented as a proof.
"""

from fractions import Fraction
from math import comb, factorial, gcd
import sys


ORDER = 5


def mul_trunc(a, b, order=ORDER):
    out = [Fraction(0) for _ in range(order + 1)]
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            if i + j <= order:
                out[i + j] += ai * bj
    return out


def linear_factor(c):
    return [Fraction(c), Fraction(1)]


def inverse_sixth_factor(c, order=ORDER):
    """Taylor coefficients of (c+x)^(-6)."""
    c = Fraction(c)
    return [Fraction((-1) ** r * comb(5 + r, r), 1) * c ** (-6 - r)
            for r in range(order + 1)]


def base_coefficients(n):
    """Return a[i,j] for R_n(t)=sum a[i,j]/(t+j)^i, 1<=i<=6."""
    a = {}
    for j in range(n + 1):
        series = [Fraction(factorial(n) ** 4)]
        series = mul_trunc(series, linear_factor(Fraction(n, 2) - j))
        for m in range(1, n + 1):
            series = mul_trunc(series, linear_factor(-j - m))
            series = mul_trunc(series, linear_factor(n + m - j))
        for m in range(n + 1):
            if m != j:
                series = mul_trunc(series, inverse_sixth_factor(m - j))
        for r in range(6):
            a[6 - r, j] = series[r]
    return a


def companion_coefficients(n, a):
    """Coefficients for -t(t+n)R_n(t)."""
    at = {}
    for i in range(1, 7):
        for j in range(n + 1):
            at[i, j] = (j * (n - j) * a[i, j]
                        + (2 * j - n) * a.get((i + 1, j), 0)
                        - a.get((i + 2, j), 0))
    return at


def harmonic(j, power):
    return sum((Fraction(1, k ** power) for k in range(1, j + 1)), Fraction(0))


def lcm_upto(n):
    ans = 1
    for k in range(2, n + 1):
        ans = ans * k // gcd(ans, k)
    return ans


def eliminated_data(n):
    a = base_coefficients(n)
    at = companion_coefficients(n, a)
    w = sum(a[3, j] for j in range(n + 1))
    wt = sum(at[3, j] for j in range(n + 1))
    scale = Fraction(12, comb(2 * n, n))
    f = {(i, j): scale * (wt * a[i, j] - w * at[i, j])
         for i in range(1, 7) for j in range(n + 1)}
    rational_part = sum(
        (f[i, j] * harmonic(j, i)
         for i in range(1, 7) for j in range(n + 1)),
        Fraction(0),
    )
    zeta3 = sum(f[3, j] for j in range(n + 1))
    zeta5 = sum(f[5, j] for j in range(n + 1))
    return w, wt, f, rational_part, zeta3, zeta5


def check(n):
    w, wt, f, rational_part, zeta3, zeta5 = eliminated_data(n)
    d = lcm_upto(n)
    target = d ** 5 * rational_part
    bad_term_denominators = set()
    for i in range(1, 7):
        for j in range(n + 1):
            term = d ** 5 * f[i, j] * harmonic(j, i)
            if term.denominator != 1:
                bad_term_denominators.add(term.denominator)
    return {
        "n": n,
        "w": w,
        "wtilde": wt,
        "zeta3": zeta3,
        "zeta5": zeta5,
        "target": target,
        "target_integral": target.denominator == 1,
        "bad_term_denominators": sorted(bad_term_denominators),
    }


if __name__ == "__main__":
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    for n in range(1, limit + 1):
        result = check(n)
        print(
            f"n={n}: target_integral={result['target_integral']} "
            f"zeta3={result['zeta3']} "
            f"bad_term_denominators={result['bad_term_denominators']}"
        )
