"""Verification battery for the CB lemma structure.

(V1) Pole-order accounting: ord_p(a_{6,j}) = [j>=t] + [j<=n-t] for p=n+t in (n,2n].
(V2) Reflection symmetry: a_{i,n-j} = (-1)^{i+1} a_{i,j}  (exact, over Q).
(V3) Exact even-layer vanishing: S_1=S_2=S_4=S_6=0 (over Q).
(V4) mod-p^2 refinement of w_n, wtilde_n.
(V5) Phase-2 ledger p<=n: ord_p(A_n) vs ord_p binom(2n,n) - ord_p(6).
"""

import sys
from fractions import Fraction
from math import comb
from lemma_cb_explore import (all_data, ord_p_fraction, mod_reduce,
                              primes_in, lcm_upto)


def check_V1_V2_V3(lo, hi):
    v1_fail = v2_fail = v3_fail = 0
    for n in range(lo, hi + 1):
        data = all_data(n)
        a = data["a"]
        # V3 exact even vanishing
        for i in (1, 2, 4, 6):
            if sum(a[i, j] for j in range(n + 1)) != 0:
                v3_fail += 1
        # V2 reflection
        for i in range(1, 7):
            for j in range(n + 1):
                if a[i, n - j] != (-1) ** (i + 1) * a[i, j]:
                    v2_fail += 1
        # V1 pole order accounting
        for p in primes_in(n + 1, 2 * n):
            t = p - n
            for j in range(n + 1):
                predicted = (1 if j >= t else 0) + (1 if j <= n - t else 0)
                actual = ord_p_fraction(a[6, j], p)
                actual = 0 if actual is None else actual
                # a[6,j] may be exactly 0 (the n/2-j factor) -> ord infinite
                if a[6, j] == 0:
                    continue
                if actual != predicted:
                    v1_fail += 1
                    if v1_fail <= 5:
                        print(f"  V1 mismatch n={n} p={p} j={j}: "
                              f"pred={predicted} act={actual}")
    print(f"V1 (pole order) failures: {v1_fail}")
    print(f"V2 (reflection)  failures: {v2_fail}")
    print(f"V3 (even vanish) failures: {v3_fail}")


def check_V4(lo, hi):
    """mod p^2 of w, wtilde: is ord exactly 1 generically, and when 2?"""
    print("\n(V4) cases where ord_p(w) or ord_p(wt) >= 2 (n<p<=2n):")
    for n in range(lo, hi + 1):
        data = all_data(n)
        for p in primes_in(n + 1, 2 * n):
            t = p - n
            ow = ord_p_fraction(data["w"], p)
            owt = ord_p_fraction(data["wt"], p)
            if (ow or 0) >= 2 or (owt or 0) >= 2:
                print(f"    n={n} p={p} t={t}: ord(w)={ow} ord(wt)={owt} "
                      f"(t==1? {t==1})")


def check_V5(lo, hi):
    """Phase 2: primes p<=n. Compute A_n = 2 d_n^5 p_n and the required
    inequality ord_p(A_n) >= ord_p binom(2n,n) - ord_p(6)."""
    print("\n(V5) Phase-2 ledger p<=n: tight cases (slack==0) and any failures:")
    fails = 0
    tight = 0
    for n in range(lo, hi + 1):
        data = all_data(n)
        d = lcm_upto(n)
        A = 2 * d ** 5 * data["p_n"]
        assert A.denominator == 1, f"A_n not integer at n={n}"
        A = A.numerator
        for p in primes_in(2, n):
            # ord_p binom(2n,n)
            ordbin = 0
            pk = p
            while pk <= 2 * n:
                ordbin += (2 * n) // pk - 2 * ((n) // pk)
                pk *= p
            ord6 = 1 if p in (2, 3) else 0
            need = ordbin - ord6
            oA = 0
            AA = A
            if AA != 0:
                while AA % p == 0:
                    AA //= p
                    oA += 1
            slack = oA - need
            if slack < 0:
                fails += 1
                print(f"    FAIL n={n} p={p}: ord(A)={oA} need={need}")
            elif slack == 0 and need > 0:
                tight += 1
    print(f"  Phase-2 failures: {fails}, tight(slack==0,need>0) count: {tight}")


if __name__ == "__main__":
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    check_V1_V2_V3(lo, hi)
    check_V4(lo, hi)
    check_V5(lo, hi)
