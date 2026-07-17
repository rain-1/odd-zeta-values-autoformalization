"""Mod-p exploration lab for the Central-Binomial Cancellation Lemma.

Builds the exact Zudilin zeta(5) partial-fraction data and exposes the
individual building blocks

    w_n      = sum_j a_{3,j}
    wtilde_n = sum_j atilde_{3,j}
    v_n      = sum_{i,j} a_{i,j}   H_j^{(i)}
    vtilde_n = sum_{i,j} atilde_{i,j} H_j^{(i)}
    p_n      = wtilde_n v_n - w_n vtilde_n
    u_n      = sum_j a_{5,j}                (zeta(5) coeff of r_n)
    utilde_n = sum_j atilde_{5,j}
    q_n      = u_n wtilde_n - utilde_n w_n

All are exact Fractions.  For a prime p with n < p <= 2n every denominator is
coprime to p (harmonic denominators only carry primes <= n < p), so each
quantity is a p-adic integer and can be reduced mod p^m exactly.

This is proof-DISCOVERY code: finite verification is evidence, not a theorem.
"""

from fractions import Fraction
from math import comb, factorial, gcd
import sys

ORDER = 5  # need Taylor up to order 5 to reach a_{1,j} from the sixth pole


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


_H_cache = {}


def harmonic(j, power):
    key = (j, power)
    if key in _H_cache:
        return _H_cache[key]
    val = sum((Fraction(1, k ** power) for k in range(1, j + 1)), Fraction(0))
    _H_cache[key] = val
    return val


def lcm_upto(n):
    ans = 1
    for k in range(2, n + 1):
        ans = ans * k // gcd(ans, k)
    return ans


def all_data(n):
    a = base_coefficients(n)
    at = companion_coefficients(n, a)
    w = sum(a[3, j] for j in range(n + 1))
    wt = sum(at[3, j] for j in range(n + 1))
    u = sum(a[5, j] for j in range(n + 1))
    ut = sum(at[5, j] for j in range(n + 1))
    v = sum((a[i, j] * harmonic(j, i)
             for i in range(1, 7) for j in range(n + 1)), Fraction(0))
    vt = sum((at[i, j] * harmonic(j, i)
              for i in range(1, 7) for j in range(n + 1)), Fraction(0))
    p_n = wt * v - w * vt
    q_n = u * wt - ut * w
    return {
        "a": a, "at": at,
        "w": w, "wt": wt, "u": u, "ut": ut,
        "v": v, "vt": vt, "p_n": p_n, "q_n": q_n,
    }


def mod_reduce(fr, p, m=1):
    """Reduce a Fraction (p-adic integer, denom coprime to p) mod p^m."""
    mod = p ** m
    num = fr.numerator % mod
    den = fr.denominator % mod
    return (num * pow(den, -1, mod)) % mod


def ord_p_fraction(fr, p):
    """p-adic valuation of a nonzero Fraction."""
    if fr == 0:
        return None
    num, den = fr.numerator, fr.denominator
    v = 0
    num = abs(num)
    while num % p == 0:
        num //= p
        v += 1
    while den % p == 0:
        den //= p
        v -= 1
    return v


def primes_in(lo, hi):
    out = []
    for k in range(max(2, lo), hi + 1):
        if all(k % d for d in range(2, int(k ** 0.5) + 1)):
            out.append(k)
    return out


if __name__ == "__main__":
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    print(f"{'n':>3} {'p':>4} {'t':>3} "
          f"{'w%p':>6} {'wt%p':>6} {'v%p':>6} {'vt%p':>6} "
          f"{'p_n%p':>6} {'ord_p(p_n)':>10}")
    for n in range(lo, hi + 1):
        data = all_data(n)
        for p in primes_in(n + 1, 2 * n):
            if p < 5:
                continue
            t = p - n
            w_ = mod_reduce(data["w"], p)
            wt_ = mod_reduce(data["wt"], p)
            v_ = mod_reduce(data["v"], p)
            vt_ = mod_reduce(data["vt"], p)
            pn_ = mod_reduce(data["p_n"], p)
            op = ord_p_fraction(data["p_n"], p)
            print(f"{n:>3} {p:>4} {t:>3} "
                  f"{w_:>6} {wt_:>6} {v_:>6} {vt_:>6} "
                  f"{pn_:>6} {str(op):>10}")
