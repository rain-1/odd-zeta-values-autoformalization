"""Verify the coordinator's three (W)-proof ingredients, exactly, over many (n,p).

R1  WRAPAROUND: sum_{k=1}^{p-1-n} 2 R_n(k) ≡ 0 (mod p),  p in (n,2n], p>=5.
R2  b-parity: b_r(n-j) = (-1)^r b_r(j)   (b_1 odd, b_2 even, b_3 odd).
R3  eps-cancellation: leading pole coeff of
        b_1 ~ (-[j>=t]+[j<=n-t]) / p      (opposite signs -> cancels in middle)
        b_2 ~ (-1/2)([j>=t]+[j<=n-t]) / p^2   (same sign  -> adds in middle)
        b_3 ~ (1/3)(-[j>=t]+[j<=n-t]) / p^3   (opposite signs -> cancels)
    plus TAIL: ord_p R_n(p-j) = [j>=t]+[j<=n-t] - 6.
    plus middle/edge decomposition of w_n mod p.
"""

import sys
from fractions import Fraction
from math import comb, factorial
from lemma_cb_explore import all_data, ord_p_fraction, primes_in
from lemma_cb_wframe import psi


def R_eval(n, k):
    """Exact R_n(k) for integer k not a pole (k>=1 here)."""
    num = Fraction(factorial(n) ** 4) * (Fraction(n, 2) + k)
    for m in range(1, n + 1):
        num *= Fraction(k - m) * Fraction(k + n + m)
    den = Fraction(1)
    for j in range(n + 1):
        den *= Fraction(k + j) ** 6
    return num / den


def modf(fr, p):
    return (fr.numerator % p) * pow(fr.denominator % p, -1, p) % p


def verify_R1(lo, hi):
    fails = 0
    for n in range(lo, hi + 1):
        for p in primes_in(n + 1, 2 * n):
            if p < 5:
                continue
            M = p - 1 - n
            S = sum((2 * R_eval(n, k) for k in range(1, M + 1)), Fraction(0))
            # S is p-integral; reduce
            if S.denominator % p == 0:
                fails += 1
                print(f"  R1 non-integral n={n} p={p}")
                continue
            if modf(S, p) != 0:
                fails += 1
                print(f"  R1 FAIL n={n} p={p}: {modf(S,p)}")
    print(f"R1 wraparound vanishing: {'OK' if fails==0 else f'{fails} FAILS'}")


def verify_R2(lo, hi):
    fails = 0
    for n in range(lo, hi + 1):
        for j in range(n + 1):
            if 2 * j == n or 2 * (n - j) == n:
                continue
            for r in (1, 2, 3):
                bj = psi(r, j, n) / factorial(r)
                bnj = psi(r, n - j, n) / factorial(r)
                if bnj != (-1) ** r * bj:
                    fails += 1
                    if fails <= 5:
                        print(f"  R2 FAIL n={n} j={j} r={r}")
    print(f"R2 b-parity b_r(n-j)=(-1)^r b_r(j): {'OK' if fails==0 else f'{fails} FAILS'}")


def verify_R3(lo, hi):
    fp = fe = ft = 0
    # signed pole-coefficient predictions
    for n in range(lo, hi + 1):
        for p in primes_in(n + 1, 2 * n):
            if p < 5:
                continue
            t = p - n
            for j in range(n + 1):
                ind_hi = 1 if j >= t else 0
                ind_lo = 1 if j <= n - t else 0
                # b_1: ord should be -1 iff eps1!=0 else >=0
                if 2 * j != n:
                    b1 = psi(1, j, n)
                    eps1 = -ind_hi + ind_lo
                    o1 = ord_p_fraction(b1, p)
                    o1 = 99 if o1 is None else o1
                    if eps1 != 0 and o1 != -1:
                        fp += 1
                    if eps1 == 0 and o1 < 0:
                        fp += 1
                    # b_2 leading pole: ord -2 iff both indicators (same sign add)
                    b2 = psi(2, j, n)
                    o2 = ord_p_fraction(b2, p)
                    o2 = 99 if o2 is None else o2
                    add2 = ind_hi + ind_lo  # coefficient magnitude of 1/p^2
                    if add2 == 2 and o2 != -2:
                        fp += 1
                    # b_3 leading: eps3 same opposite-sign pattern as b_1
                    b3 = psi(3, j, n)
                    o3 = ord_p_fraction(b3, p)
                    o3 = 99 if o3 is None else o3
                    eps3 = -ind_hi + ind_lo
                    if eps3 != 0 and o3 != -3:
                        fp += 1
                    if eps3 == 0 and o3 < -2:
                        # middle: leading 1/p^3 cancels -> ord >= -2
                        fp += 1
                # tail: ord_p R_n(p-j) = ind_hi+ind_lo-6
                ot = ord_p_fraction(R_eval(n, p - j), p)
                if ot != ind_hi + ind_lo - 6:
                    ft += 1
    print(f"R3 pole-sign structure of b_1,b_2,b_3: {'OK' if fp==0 else f'{fp} FAILS'}")
    print(f"R3 tail ord_p R_n(p-j)=[j>=t]+[j<=n-t]-6: {'OK' if ft==0 else f'{ft} FAILS'}")


def decompose_middle_edge(lo, hi):
    """Split w_n mod p into middle (t<=j<=n-t) and edge (j<t or j>n-t)."""
    print("\n  n  p   t | ord(a3) middle-range set | Smid%p Sedge%p  (w=Smid+Sedge)")
    both_mid_zero = True
    for n in range(lo, hi + 1):
        data = all_data(n)
        a = data["a"]
        for p in primes_in(n + 1, 2 * n):
            if p < 5:
                continue
            t = p - n
            mid = [j for j in range(n + 1) if t <= j <= n - t]
            edge = [j for j in range(n + 1) if not (t <= j <= n - t)]
            Smid = sum((a[3, j] for j in mid), Fraction(0))
            Sedge = sum((a[3, j] for j in edge), Fraction(0))
            smid = modf(Smid, p) if Smid.denominator % p else None
            sedge = modf(Sedge, p) if Sedge.denominator % p else None
            ords = sorted({ord_p_fraction(a[3, j], p) for j in mid}) if mid else []
            if smid not in (0, None):
                both_mid_zero = False
            if n <= 14:
                print(f" {n:>2} {p:>2} {t:>3} | mid={mid} ords={ords} | "
                      f"{smid} {sedge}")
    print(f"  middle-range partial sum Smid ≡ 0 mod p always? {both_mid_zero}")


if __name__ == "__main__":
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    verify_R1(lo, hi)
    verify_R2(lo, hi)
    verify_R3(lo, hi)
    decompose_middle_edge(lo, min(hi, 14))
