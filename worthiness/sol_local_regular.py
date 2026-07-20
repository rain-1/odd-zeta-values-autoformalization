"""Exact finite tests for Sol's Phase-2 solution-specific regularity target.

HONESTY: every PASS printed by this program is finite exact-arithmetic evidence,
not a proof.  The algebraic reductions defining the two residue rows are exact
polynomial identities (checked with SymPy assertions below).

Tests:

  (LR)  v_p(c0 P_m+c1 P_{m+1}+c2 P_{m+2})
          >= min_i v_p(P_{m+i}) + v_p((2m+5)*a0(m)).

  (MID1) At a simple midpoint digit (p != 7), the fixed residue row
          11907*x0 - 334374*x1 - 19292*x2 = 0 mod p.

  (CUB1) Away from denominator primes 37,557, the degree-2 residue row modulo
         a0 annihilates the normalized local P-vector mod p.

  (FROB-P) For n=ap+r, the division-free last-row witness
          p^5 P_n = P_a (Q_r + E_{n,p}), E_{n,p} in Z_p,
          tested as v_p(p^5 P_n-P_a Q_r) >= v_p(P_a).

Usage: PYTHONPATH=worthiness python3 worthiness/sol_local_regular.py [N]
Default N=60 (the current exact-data cache range).
"""

from fractions import Fraction
import sys

import sympy as sp

from salvage_data import get_all, triple
from salvage_v6_desing import a0, c0, c1, c2, n, vp


A0 = sp.Poly(a0, n)
C = [sp.Poly(sp.expand(x), n) for x in (c0, c1, c2)]
MID = sp.Poly(2*n + 5, n)

# Exact midpoint residue.  The factor 7 is intrinsic.
MID_ROW = (11907, -334374, -19292)
for Ci, ri in zip(C, MID_ROW):
    assert sp.rem(Ci, MID).as_expr() == Fraction(7 * ri, 128)

# Primitive degree <= 2 residue row after clearing the common denominator D.
CUB_D = 688444586089376  # 2^5 * 37^5 * 557^2
CUB_ROW = (
    7502522434517190247*n**2 + 27377435999133628028*n + 23682487355887746399,
    14*(3763413087280622569*n**2 + 11453615933815386820*n
        + 8744992879372731313),
    17052*(1395403006376645*n**2 + 4537329573624116*n
           + 3700105031529293),
)
for Ci, Ri in zip(C, CUB_ROW):
    assert sp.rem(Ci, A0).as_expr() == sp.cancel(Ri / CUB_D)

DISC_A0 = int(sp.discriminant(A0))
RES_MID_A0 = abs(int(sp.resultant(A0, MID)))
assert sp.factorint(abs(DISC_A0)) == {2: 2, 3: 3, 7: 2, 29: 2,
                                     107: 1, 557: 1, 673: 1}
assert sp.factorint(RES_MID_A0) == {2: 3, 43: 1, 701: 1}


def primes_dividing(x):
    return [int(p) for p in sp.factorint(abs(int(x))) if p >= 5]


def val_row(row, m, key):
    return sum((Fraction(int(sp.expand(R).subs(n, m))) * Fraction(triple(m+i)[key])
                for i, R in enumerate(row)), Fraction(0))


def local_regular(hi):
    """Test the full local inequality at every singular prime in m<=hi-3."""
    print("=== (LR) full solution-specific local regularity [FINITE EVIDENCE] ===")
    counts = {key: [0, 0] for key in ("Q", "P", "Ph")}
    first = {key: [] for key in counts}
    multi = []
    for m in range(0, hi - 2):
        av = int(a0.subs(n, m))
        mid = 2*m + 5
        for p in sorted(set(primes_dividing(mid) + primes_dividing(av))):
            gval = vp(mid, p) + vp(av, p)
            if gval > 1:
                multi.append((m, p, vp(mid, p), vp(av, p)))
            coeff = [int(Ci.eval(m)) for Ci in C]
            for key in counts:
                ys = [Fraction(triple(m+i)[key]) for i in range(3)]
                e = min(vp(y, p) for y in ys)
                lhs = sum((Fraction(coeff[i])*ys[i] for i in range(3)), Fraction(0))
                good = vp(lhs, p) >= e + gval
                counts[key][0] += 1
                counts[key][1] += int(not good)
                if not good and len(first[key]) < 8:
                    first[key].append((m, p, vp(lhs, p), e + gval))
    for key, (total, bad) in counts.items():
        print(f"  {key:>2}: {total} singular (m,p) rows; violations={bad}")
        if first[key]:
            print("      first (m,p,got,need):", first[key])
    print("  rows with singular multiplicity >1 (m,p,v_mid,v_a0):", multi[:20],
          f"[total {len(multi)}]")


def residue_rows(hi):
    print("\n=== (MID1)/(CUB1) small uniform residue rows [FINITE EVIDENCE] ===")
    for key in ("Q", "P", "Ph"):
        mt = mb = ct = cb = 0
        for m in range(0, hi - 2):
            mid = 2*m + 5
            av = int(a0.subs(n, m))
            ys = [Fraction(triple(m+i)[key]) for i in range(3)]
            for p in primes_dividing(mid):
                if p == 7:
                    continue
                e = min(vp(y, p) for y in ys)
                R = sum((Fraction(MID_ROW[i])*ys[i] for i in range(3)), Fraction(0))
                mt += 1
                mb += int(vp(R, p) < e + 1)
            for p in primes_dividing(av):
                if p in (37, 557):
                    continue
                e = min(vp(y, p) for y in ys)
                R = val_row(CUB_ROW, m, key)
                ct += 1
                cb += int(vp(R, p) < e + 1)
        print(f"  {key:>2}: MID1 {mt} rows/{mb} violations; CUB1 {ct} rows/{cb} violations")


def frobenius_last_row(hi):
    print("\n=== (FROB-P) division-free last row [FINITE EVIDENCE] ===")
    total = bad = 0
    min_delta = 10**9
    first = []
    for p in list(sp.primerange(5, hi + 1)):
        for nn in range(p, hi + 1):
            aa, rr = divmod(nn, p)
            Pa = Fraction(triple(aa)["P"])
            if Pa == 0:
                continue
            F = Fraction(p**5)*Fraction(triple(nn)["P"]) - Pa*Fraction(triple(rr)["Q"])
            delta = vp(F, p) - vp(Pa, p)
            min_delta = min(min_delta, delta)
            total += 1
            if delta < 0:
                bad += 1
                if len(first) < 8:
                    first.append((nn, p, aa, rr, delta))
    print(f"  rows={total}; violations={bad}; min(v_p(F)-v_p(P_a))={min_delta}")
    if first:
        print("  first (n,p,a,r,delta):", first)
    print("  Algebraic implication (proved, not finite): if every witness F/P_a is")
    print("  p-integral and Q_r is integral, then v_p(P_n)>=v_p(P_a)-5, i.e. (D).")

    print("\n  Filtered diagonal strengthening: p^w Y_n/Y_a = Q_r (mod p)")
    for key, wt in (("P", 5), ("Ph", 3)):
        strong_bad = []
        strong_total = 0
        for p in list(sp.primerange(5, hi + 1)):
            for nn in range(p, hi + 1):
                aa, rr = divmod(nn, p)
                Ya = Fraction(triple(aa)[key])
                if Ya == 0:
                    continue
                F = Fraction(p**wt)*Fraction(triple(nn)[key]) \
                    - Ya*Fraction(triple(rr)["Q"])
                delta = vp(F, p) - vp(Ya, p)
                strong_total += 1
                if delta < 1:
                    strong_bad.append((nn, p, aa, rr, delta))
        print(f"    ({key},w={wt}): rows={strong_total}; failures={len(strong_bad)}; "
              f"first={strong_bad[:8]}")


if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    get_all(0, hi)
    print("Exact polynomial identity checks: PASS")
    print("Cubic row denominator:", CUB_D, "=", sp.factorint(CUB_D))
    print("disc(a0):", DISC_A0, "=", sp.factorint(abs(DISC_A0)))
    print("|Res(a0,2n+5)|:", RES_MID_A0, "=", sp.factorint(RES_MID_A0))
    local_regular(hi)
    residue_rows(hi)
    frobenius_last_row(hi)
