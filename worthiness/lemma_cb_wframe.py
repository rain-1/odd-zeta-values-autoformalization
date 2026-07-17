"""Integer reframing of (W) and verification of the normal-form starting point.

(F1) 2 d_n^2 w_n and 2 d_n^2 wtilde_n are integers (tight power; d^1 fails).
(F2) B_n^high = prod of primes p in (n,2n], p>=5, divides both integers.
(F3) Normal form for the summand:
        a_{3,j} = a_{6,j} * (b_3 + b_1 b_2 + b_1^3/6),
     where b_r = psi_r(-j)/r! and
        psi_r(-j) = (-1)^{r-1}(r-1)! [ (n/2-j)^{-r}
                     + sum_{m=1}^n ((-1)^r (j+m)^{-r} + (n+m-j)^{-r})
                     - 6 sum_{m!=j,0<=m<=n} (m-j)^{-r} ].
     This exhibits w_n = sum_j a_{6,j}*(weight-<=3 harmonic polynomial):
     the binomial product a_{6,j} times harmonic factors that carry 1/p poles,
     which is why 2 d_n^2 a_{3,j} is not termwise integral (global cancellation).
"""

import sys
from fractions import Fraction
from math import prod
from lemma_cb_explore import all_data, lcm_upto, primes_in


def psi(r, j, n):
    coeff = Fraction((-1) ** (r - 1)) * _fact(r - 1)
    s = Fraction(1) / (Fraction(n, 2) - j) ** r
    for m in range(1, n + 1):
        s += Fraction((-1) ** r) / Fraction(j + m) ** r
        s += Fraction(1) / Fraction(n + m - j) ** r
    for m in range(0, n + 1):
        if m != j:
            s -= 6 * Fraction(1) / Fraction(m - j) ** r
    return coeff * s


def _fact(k):
    out = 1
    for i in range(2, k + 1):
        out *= i
    return out


def check(lo, hi):
    f1_ok = f2_ok = f3_ok = True
    for n in range(lo, hi + 1):
        d = all_data(n)
        a = d["a"]
        w, wt = d["w"], d["wt"]
        dn = lcm_upto(n)
        W, WT = 2 * dn ** 2 * w, 2 * dn ** 2 * wt
        if W.denominator != 1 or WT.denominator != 1:
            f1_ok = False
            print(f"  F1 FAIL n={n}")
        ph = [p for p in primes_in(n + 1, 2 * n) if p >= 5]
        B = prod(ph) if ph else 1
        if W.denominator == 1 and W.numerator % B:
            f2_ok = False
            print(f"  F2 FAIL (w) n={n}")
        if WT.denominator == 1 and WT.numerator % B:
            f2_ok = False
            print(f"  F2 FAIL (wt) n={n}")
        # F3 normal form (valid for j != n/2; at the middle pole a_{6,j}=0
        # and log G_j is singular -- separate limiting expression needed there)
        for j in range(n + 1):
            if 2 * j == n:
                continue
            b1 = psi(1, j, n) / 1
            b2 = psi(2, j, n) / 2
            b3 = psi(3, j, n) / 6
            pred = a[6, j] * (b3 + b1 * b2 + b1 ** 3 / 6)
            if pred != a[3, j]:
                f3_ok = False
                print(f"  F3 FAIL n={n} j={j}: pred={pred} act={a[3,j]}")
    print(f"F1 (2 d^2 w, wt integral): {'OK' if f1_ok else 'FAIL'}")
    print(f"F2 (B_high | W, WT):       {'OK' if f2_ok else 'FAIL'}")
    print(f"F3 (a3j = a6j*(b3+b1b2+b1^3/6)): {'OK' if f3_ok else 'FAIL'}")


if __name__ == "__main__":
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    check(lo, hi)
