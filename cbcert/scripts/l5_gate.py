"""L5 ground-truth gate.

Computes, in exact Fraction arithmetic (adapting worthiness/lemma_cb_explore.py's
all_data chain), for each n:

    pn      = wt*v - w*vt            (canonical Cbcert.pn)
    P_n     = (-1)^(n+1) * pn / C(2n,n)     (Brown-Zudilin symmetric value)
    law_n   = 12 * d_n^5 * P_n       (must be an integer -- the corrected law)

Prints a table and asserts law_n in Z for every n in the range.  If ANY n fails,
that FALSIFIES the corrected 12*d_n^5*P_n in Z law -- a major finding; the script
exits non-zero and prints FAIL.

Usage:  python3 l5_gate.py [LO] [HI]
"""

from fractions import Fraction
from math import comb, factorial, gcd
import sys

ORDER = 5


def mul_trunc(a, b, order=ORDER):
    out = [Fraction(0) for _ in range(order + 1)]
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            if i + j <= order and bj != 0:
                out[i + j] += ai * bj
    return out


def linear_factor(c):
    return [Fraction(c), Fraction(1)]


def inverse_sixth_factor(c, order=ORDER):
    c = Fraction(c)
    return [Fraction((-1) ** r * comb(5 + r, r), 1) * c ** (-6 - r)
            for r in range(order + 1)]


def base_coefficients(n):
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


def pn_of(n):
    a = base_coefficients(n)
    at = companion_coefficients(n, a)
    w = sum(a[3, j] for j in range(n + 1))
    wt = sum(at[3, j] for j in range(n + 1))
    v = sum((a[i, j] * harmonic(j, i)
             for i in range(1, 7) for j in range(n + 1)), Fraction(0))
    vt = sum((at[i, j] * harmonic(j, i)
              for i in range(1, 7) for j in range(n + 1)), Fraction(0))
    return wt * v - w * vt


def data_for(n):
    pn = pn_of(n)
    C = comb(2 * n, n)
    P = Fraction((-1) ** (n + 1)) * pn / C
    d = lcm_upto(n)
    law = 12 * Fraction(d) ** 5 * P
    return pn, C, P, d, law


if __name__ == "__main__":
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    print(f"{'n':>3} {'d_n':>10} {'law_digits':>10} {'law in Z':>8}  law = 12*d^5*P_n")
    ok = True
    rows = []
    for n in range(lo, hi + 1):
        pn, C, P, d, law = data_for(n)
        is_int = (law.denominator == 1)
        ok = ok and is_int
        digits = len(str(abs(law.numerator)))
        rows.append((n, pn, C, P, d, law, is_int))
        print(f"{n:>3} {d:>10} {digits:>10} {str(is_int):>8}  {law}")
    print()
    if ok:
        print("GATE PASS: 12*d_n^5*P_n in Z for all n in", (lo, hi))
    else:
        print("GATE FAIL: corrected law violated -- MAJOR FINDING, STOP")
        sys.exit(1)
