"""Extend the a=1 head-window experiment to every residue 0 <= r < p.

Exact Fraction arithmetic.  This is finite evidence only, never a proof.

For n=p+r and each of the base/companion partial-fraction coefficient arrays,
test

  p^5 * sum_{i=1}^6 (-1)^(i+1) p^(-i) sum_{j=0}^r a[i,j]
    - (29/28) u_n - (101/84) p^2 w_n

and its tilded analogue.  The earlier dwork_hw.py restricted its report to an
upper band; the true-singularity midpoint r=(p-5)/2 lies below that band.

Usage: PYTHONPATH=worthiness python3 worthiness/sol_hw_allr.py
"""

from fractions import Fraction

from dwork_hw import RHO1, SIG1, data, head
from lemma_cb_explore import ord_p_fraction as vp


def error(p, r, tilde=False):
    d = data(p+r)
    a = d["at" if tilde else "a"]
    u = d["ut" if tilde else "u"]
    w = d["wt" if tilde else "w"]
    singular = sum(
        (Fraction((-1)**(i+1), p**i) * head(a, i, r) for i in range(1, 7)),
        Fraction(0),
    )
    return Fraction(p**5)*singular - RHO1*u - SIG1*Fraction(p**2)*w


if __name__ == "__main__":
    primes = (5, 7, 11, 13, 17, 19, 23, 29)
    print("a=1 head-window, all residues [FINITE EXACT EVIDENCE]")
    total = bad4 = 0
    for p in primes:
        rows = []
        for r in range(p):
            vals = []
            for tilde in (False, True):
                E = error(p, r, tilde)
                vals.append(vp(E, p) if E else 10**9)
                total += 1
                bad4 += int(vals[-1] < 4)
            rows.append(tuple(vals))
        print(f"  p={p:2d}: min(base)={min(x[0] for x in rows)}, "
              f"min(tilde)={min(x[1] for x in rows)}, residues={len(rows)}")
    print(f"  scalar rows={total}; violations of valuation >=4: {bad4}")
    print("  Status: finite exact verification only; the uniform block identity is open.")
