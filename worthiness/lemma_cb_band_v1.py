"""V1 -- Exact decomposition check (Phase-2 band blueprint).

Band: n/2 < p <= 2n/3 (kappa = ord_p C(2n,n) = 1). Write n = p + r, so r = n-p.
In this band r in [ceil(p/2), p-1], and the ONLY multiple of p in [1,n] is p.

Decompose each harmonic:  H_j^{(i)} = Hhat_j^{(i)} + [j>=p] p^{-i},  Hhat p-integral.
Hence
    v = sum_{i,j} a_{i,j} Hhat_j^{(i)}  +  sum_i p^{-i} S_i^tail,
    S_i^tail = sum_{j>=p} a_{i,j} = (-1)^{i+1} S_i^head   (reflection P1),
    S_i^head := sum_{j=0}^{r} a_{i,j}.

So RESIDUAL(v) := v - sum_i p^{-i} (-1)^{i+1} S_i^head  =  sum_{i,j} a_{i,j} Hhat_j^{(i)}.
The tail (H-)singularity is fully removed; the residual's ord_p is governed only by
the a-singularities (blueprint 2b). This script reports ord_p(RESIDUAL) and the
ord_p of every S_i^head, for v and its companion vtilde, across the band table.

Exact Fraction arithmetic throughout.
"""
import sys
from fractions import Fraction
sys.path.insert(0, '.')
from lemma_cb_explore import (all_data, primes_in, harmonic, ord_p_fraction)


def band_primes(n):
    # n/2 < p <= 2n/3, p>=5
    return [p for p in primes_in(n // 2 + 1, (2 * n) // 3) if p >= 5]


def head_sums(a, r, tilde=False, at=None):
    src = at if tilde else a
    return {i: sum((src[i, j] for j in range(r + 1)), Fraction(0)) for i in range(1, 7)}


def Hhat(j, i, p):
    """H_j^{(i)} with the single 1/p^i tail term (present iff j>=p) removed."""
    h = harmonic(j, i)
    if j >= p:
        h = h - Fraction(1, p ** i)
    return h


def residual(a, n, p, headS):
    """v - sum_i p^{-i}(-1)^{i+1} S_i^head, computed two independent ways for a self-check."""
    # way A: direct sum a_{i,j} Hhat
    A = sum((a[i, j] * Hhat(j, i, p) for i in range(1, 7) for j in range(n + 1)),
            Fraction(0))
    # way B: full v minus the constructed tail
    v = sum((a[i, j] * harmonic(j, i) for i in range(1, 7) for j in range(n + 1)),
            Fraction(0))
    tail = sum((Fraction((-1) ** (i + 1), p ** i) * headS[i] for i in range(1, 7)),
               Fraction(0))
    B = v - tail
    assert A == B, f"residual mismatch n={n} p={p}"
    return A, v


def run(lo, hi):
    print("V1: exact decomposition -- residual after removing H-tail singular part")
    print("Legend: ord(res)=ord_p(v - sum_i p^-i(-1)^{i+1} S_i^head); ordS[i]=ord_p(S_i^head)")
    print()
    hdr = (f"{'n':>3} {'p':>3} {'r':>3} | {'ord(v)':>6} {'ord(res)':>8} | "
           f"{'S1':>3}{'S2':>3}{'S3':>3}{'S4':>3}{'S5':>3}{'S6':>3} || "
           f"{'ordvt':>6} {'ordrest':>8} | {'St1':>3}{'St2':>3}{'St3':>3}{'St4':>3}{'St5':>3}{'St6':>3}")
    print(hdr)
    rows = []
    for n in range(lo, hi + 1):
        bp = band_primes(n)
        if not bp:
            continue
        d = all_data(n)
        a, at = d["a"], d["at"]
        for p in bp:
            r = n - p
            headS = head_sums(a, r)
            headSt = head_sums(at, r, tilde=True, at=at)
            res, v = residual(a, n, p, headS)
            rest, vt = residual(at, n, p, headSt)
            oS = [ord_p_fraction(headS[i], p) for i in range(1, 7)]
            oSt = [ord_p_fraction(headSt[i], p) for i in range(1, 7)]
            ov = ord_p_fraction(v, p)
            ores = ord_p_fraction(res, p) if res != 0 else None
            ovt = ord_p_fraction(vt, p)
            orest = ord_p_fraction(rest, p) if rest != 0 else None
            def s(x): return 'oo' if x is None else str(x)
            print(f"{n:>3} {p:>3} {r:>3} | {s(ov):>6} {s(ores):>8} | "
                  + "".join(f"{s(x):>3}" for x in oS)
                  + f" || {s(ovt):>6} {s(orest):>8} | "
                  + "".join(f"{s(x):>3}" for x in oSt))
            rows.append((n, p, r, ov, ores, oS, ovt, orest, oSt))
    # summary
    print()
    resids = [r[4] for r in rows if r[4] is not None]
    if resids:
        print(f"ord_p(residual of v):   min={min(resids)}  max={max(resids)}  "
              f"(over {len(rows)} band pairs)")
    resids_t = [r[7] for r in rows if r[7] is not None]
    if resids_t:
        print(f"ord_p(residual of vt):  min={min(resids_t)}  max={max(resids_t)}")
    return rows


if __name__ == "__main__":
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 45
    run(lo, hi)
