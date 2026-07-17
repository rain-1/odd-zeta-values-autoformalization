"""F_p-moment reduction of (W) to the residue layer.

Verified facts (this script):
  M1  All a_{i,j} are p-integral for p > n, p >= 5 (only p=2 fails, via n/2).
  M2  PRIZE: w_n     ≡ 3 * sum_j j^2 a_{1,j}      (mod p)  [X  ]
      and    wtilde_n ≡ 3 * sum_j j^2 atilde_{1,j} (mod p)  [Xt ]
      for all primes n < p <= 2n, p >= 5.  Hence (W) <=> X ≡ 0 and Xt ≡ 0.
  M3  The reduction is a GENUINE mod-p fact: w_n - 3X is a nonzero rational,
      but ord_p(w_n - 3X) >= 1 for every p in (n,2n], p>=5.  (Not circular with
      the exact-Q identity w_n = 2 sum_j j a_{2,j} - X, which comes from the
      k^{-3} coefficient of R_n at infinity.)
  M4  PARITY of the moment-vanishing sum_{i=1}^{min(6,s)} C(s,i) M_{s-i,i} mod p,
      M_{s,i} = sum_j a_{i,j}(n/2-j)^s:  vanishes for even s (sigma-parity,
      provable) and for s=1,3, but NOT for s=5,7 (so the general odd-s family is
      false; only the s=3 relation feeding the prize holds).

X := sum_j j^2 a_{1,j} is the residue-layer target: 2 d_n^4 X in Z and
B_n^high | 2 d_n^4 X (window primes divide it).
"""

import sys
from fractions import Fraction
from math import comb, prod
from lemma_cb_explore import (all_data, ord_p_fraction, primes_in, lcm_upto,
                              companion_coefficients)


def modp(fr, p, m=1):
    mod = p ** m
    if fr.denominator % mod == 0:
        return None
    return (fr.numerator % mod) * pow(fr.denominator % mod, -1, mod) % mod


def X_of(a, n):
    return sum((j * j * a[1, j] for j in range(n + 1)), Fraction(0))


def M(a, n, s, i):
    return sum((a[i, j] * (Fraction(n, 2) - j) ** s for j in range(n + 1)),
               Fraction(0))


def run(lo, hi):
    bad_int = bad_w = bad_wt = bad_gen = 0
    tot = 0
    for n in range(lo, hi + 1):
        d = all_data(n)
        a = d["a"]
        at = companion_coefficients(n, a)
        for p in primes_in(n + 1, 2 * n):
            if p < 5:
                continue
            tot += 1
            # M1
            for i in range(1, 7):
                for j in range(n + 1):
                    o = ord_p_fraction(a[i, j], p)
                    if o is not None and o < 0:
                        bad_int += 1
            # M2
            X = X_of(a, n)
            Xt = sum((j * j * at[1, j] for j in range(n + 1)), Fraction(0))
            if modp(d["w"], p) != modp(3 * X, p):
                bad_w += 1
            if modp(d["wt"], p) != modp(3 * Xt, p):
                bad_wt += 1
            # M3 genuineness
            diff = d["w"] - 3 * X
            if diff != 0:
                o = ord_p_fraction(diff, p)
                if o is not None and o < 1:
                    bad_gen += 1
    print(f"checked {tot} pairs, n in [{lo},{hi}]")
    print(f"M1 all a_ij p-integral (p>=5): {'OK' if bad_int==0 else f'{bad_int} FAIL'}")
    print(f"M2 w  ≡ 3 sum j^2 a_1j  mod p: {'OK' if bad_w==0 else f'{bad_w} FAIL'}")
    print(f"M2 wt ≡ 3 sum j^2 at_1j mod p: {'OK' if bad_wt==0 else f'{bad_wt} FAIL'}")
    print(f"M3 ord_p(w-3X)>=1 (genuine): {'OK' if bad_gen==0 else f'{bad_gen} FAIL'}")
    # M4 parity table
    print("\nM4 moment-vanishing sum_i C(s,i)M_{s-i,i} mod p (should be 0):")
    for (n, want_p) in [(11, 13), (12, 17)]:
        d = all_data(n)
        a = d["a"]
        p = want_p
        row = [modp(sum((comb(s, i) * M(a, n, s - i, i)
                         for i in range(1, min(6, s) + 1)), Fraction(0)), p)
               for s in range(1, 8)]
        print(f"   n={n} p={p}: s=1..7 -> {row}   (s=5,7 nonzero => general odd-s FALSE)")


if __name__ == "__main__":
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    run(lo, hi)
