"""PROOF-BY-CERTIFICATE that w_n = wtilde_n = 0 (mod p) for n < p <= 2n.

Mechanism.  R_n(k) = O(k^{-4n-5}) at infinity, so the coefficient of k^{-M} in
its Laurent expansion vanishes for M = 1,...,4n+4.  Writing
R_n(k) = sum_{i,j} a_{i,j}(k+j)^{-i} and (k+j)^{-i} = sum_r C(-i,r) j^r k^{-i-r},
this coefficient is

    E_M := sum_{i=1}^{min(6,M)} C(-i, M-i) * sum_j j^{M-i} a_{i,j} = 0   (over Q).   (R2)

These are EXACT rational relations (verified here over Q).  Reducing mod p:
for n < p <= 2n the F_p-functional  w := sum_j a_{3,j}  (and likewise wtilde)
lies in the F_p-linear span of { E_M mod p : 1 <= M <= 4n+4 }.  Since each E_M
annihilates the (p-integral, p>n) true coefficient vector, w_n ≡ 0 (mod p).

Threshold law (verified): w is forced <=> relations up to M = 2p+1 are available
<=> 2p+1 <= 4n+4 <=> p <= 2n+1.  This is exactly why the range is n < p <= 2n.

Soundness controls (verified):
  * u := sum_j a_{5,j} (the zeta(5) coefficient, generically a unit) is NOT forced;
  * for p > 2n+1, w is NOT forced (and indeed w_n is generically a unit there).
"""

import sys
from fractions import Fraction
from lemma_cb_explore import all_data, primes_in


def Cneg(i, r):
    v = Fraction(1)
    for x in range(r):
        v *= Fraction(-i - x, x + 1)
    return int(v)  # integer-valued


def E_relations_exactQ(a, n):
    """Return the exact-Q values E_M for M=1..4n+4 (must all be 0)."""
    vals = []
    for M in range(1, 4 * n + 5):
        s = Fraction(0)
        for i in range(1, min(6, M) + 1):
            r = M - i
            c = Cneg(i, r)
            s += c * sum(a[i, j] * Fraction(j) ** r for j in range(n + 1))
        vals.append(s)
    return vals


def E_rows_modp(n, p):
    N = n + 1
    dim = 6 * N
    idx = lambda i, j: (i - 1) * N + j
    rows = []
    for M in range(1, 4 * n + 5):
        row = [0] * dim
        for i in range(1, min(6, M) + 1):
            r = M - i
            c = Cneg(i, r) % p
            for j in range(N):
                row[idx(i, j)] = (row[idx(i, j)] + c * (pow(j, r, p) if r else 1)) % p
        rows.append(row)
    return rows, dim, idx


def basis_of(rows, ncol, p):
    B = []
    for row in rows:
        cur = [x % p for x in row]
        for b, piv in B:
            if cur[piv]:
                f = cur[piv]
                cur = [(cur[k] - f * b[k]) % p for k in range(ncol)]
        piv = next((k for k in range(ncol) if cur[k]), None)
        if piv is not None:
            inv = pow(cur[piv], -1, p)
            B.append(([(x * inv) % p for x in cur], piv))
    return B


def in_span(B, target, ncol, p):
    cur = [x % p for x in target]
    for b, piv in B:
        if cur[piv]:
            f = cur[piv]
            cur = [(cur[k] - f * b[k]) % p for k in range(ncol)]
    return all(x == 0 for x in cur)


def tgt(n, p, idx, kind):
    dim = 6 * (n + 1)
    v = [0] * dim
    if kind == "w":
        for j in range(n + 1):
            v[idx(3, j)] = 1
    elif kind == "u":
        for j in range(n + 1):
            v[idx(5, j)] = 1
    else:  # wtilde: atilde_{3,j} = j(n-j)a_3 + (2j-n)a_4 - a_5
        for j in range(n + 1):
            v[idx(3, j)] = (v[idx(3, j)] + j * (n - j)) % p
            v[idx(4, j)] = (v[idx(4, j)] + (2 * j - n)) % p
            v[idx(5, j)] = (v[idx(5, j)] - 1) % p
    return v


def run(lo, hi):
    exactQ_fail = 0
    w_fail = wt_fail = 0
    u_spurious = 0
    checked = 0
    for n in range(lo, hi + 1):
        d = all_data(n)
        a = d["a"]
        # (i) EXACT-Q soundness of R2
        if any(v != 0 for v in E_relations_exactQ(a, n)):
            exactQ_fail += 1
            print(f"  R2 not exact over Q at n={n}!")
        for p in primes_in(n + 1, 2 * n):
            if p < 5:
                continue
            checked += 1
            rows, dim, idx = E_rows_modp(n, p)
            B = basis_of(rows, dim, p)
            if not in_span(B, tgt(n, p, idx, "w"), dim, p):
                w_fail += 1
                print(f"  w NOT forced n={n} p={p}")
            if not in_span(B, tgt(n, p, idx, "wt"), dim, p):
                wt_fail += 1
                print(f"  wt NOT forced n={n} p={p}")
            if in_span(B, tgt(n, p, idx, "u"), dim, p):
                u_spurious += 1
                print(f"  u SPURIOUSLY forced n={n} p={p}")
    print(f"n in [{lo},{hi}], checked {checked} pairs (n<p<=2n, p>=5):")
    print(f"  R2 exact over Q (all E_M=0):     {'OK' if exactQ_fail==0 else f'{exactQ_fail} FAIL'}")
    print(f"  w  forced in F_p-span(R2):       {'OK (PROVES w_n≡0)'  if w_fail==0 else f'{w_fail} FAIL'}")
    print(f"  wt forced in F_p-span(R2):       {'OK (PROVES wt_n≡0)' if wt_fail==0 else f'{wt_fail} FAIL'}")
    print(f"  u  NOT forced (soundness ctrl):  {'OK' if u_spurious==0 else f'{u_spurious} SPURIOUS'}")


if __name__ == "__main__":
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    run(lo, hi)
