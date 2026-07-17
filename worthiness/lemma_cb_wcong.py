"""Characterize the w_n, wtilde_n congruences on the clean interval n<p<=2n.

Findings to test at scale:
  (W)   w_n      ≡ 0 (mod p)   for all primes n < p <= 2n
  (Wt)  wtilde_n ≡ 0 (mod p)   for all primes n < p <= 2n
and the exact valuations ord_p(w_n), ord_p(wtilde_n), ord_p(p_n),
plus the layer sums S_i = sum_j a_{i,j} (i=1..6).
"""

import sys
from fractions import Fraction
from lemma_cb_explore import all_data, ord_p_fraction, mod_reduce, primes_in


def layer_sums(data, n):
    a = data["a"]
    return {i: sum(a[i, j] for j in range(n + 1)) for i in range(1, 7)}


def run(lo, hi, show_fail_only=False):
    fails = 0
    checked = 0
    ord_w_dist = {}
    ord_wt_dist = {}
    for n in range(lo, hi + 1):
        data = all_data(n)
        S = layer_sums(data, n)
        # exact identities that should hold for ALL n (well-poised vanishing)
        for i in (1, 2, 4, 6):
            if S[i] != 0:
                print(f"  !! n={n}: exact layer sum S_{i} = {S[i]} != 0")
        for p in primes_in(n + 1, 2 * n):
            if p < 5:
                continue
            checked += 1
            ow = ord_p_fraction(data["w"], p)
            owt = ord_p_fraction(data["wt"], p)
            opn = ord_p_fraction(data["p_n"], p)
            ord_w_dist[ow] = ord_w_dist.get(ow, 0) + 1
            ord_wt_dist[owt] = ord_wt_dist.get(owt, 0) + 1
            ok = (ow is None or ow >= 1) and (owt is None or owt >= 1) \
                and (opn is None or opn >= 1)
            if not ok:
                fails += 1
                print(f"  FAIL n={n} p={p} t={p-n}: "
                      f"ord_p(w)={ow} ord_p(wt)={owt} ord_p(p_n)={opn}")
            elif not show_fail_only:
                pass
    print(f"\nchecked {checked} (n,p) pairs in n in [{lo},{hi}], "
          f"failures={fails}")
    print(f"ord_p(w_n) distribution : {dict(sorted((k if k is not None else 999, v) for k,v in ord_w_dist.items()))}")
    print(f"ord_p(wt_n) distribution: {dict(sorted((k if k is not None else 999, v) for k,v in ord_wt_dist.items()))}")


if __name__ == "__main__":
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    run(lo, hi)
