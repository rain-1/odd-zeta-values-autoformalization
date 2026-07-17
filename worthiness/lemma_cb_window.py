"""Inspect the mod-p window structure of a_{i,j} for n<p<=2n, p=n+t.

Coordinator foothold: with p=n+t,
   binom(n+j,n) ≡ 0 (mod p)  <=>  j >= t
   binom(2n-j,n) ≡ 0 (mod p) <=> j <= n-t
so a_{6,j} ≡ 0 outside the open window (n-t, t), EMPTY when p<=3n/2.
This script prints a_{i,j} mod p for each pole j and each order i, marking
the theoretical support, to reveal how S_3=sum_j a_{3,j} cancels mod p.
"""

import sys
from math import comb
from lemma_cb_explore import all_data, mod_reduce


def show(n, p):
    t = p - n
    data = all_data(n)
    a = data["a"]
    print(f"\n=== n={n} p={p} t={t}  (3n/2={3*n/2}) ===")
    print(f"    j : a1  a2  a3  a4  a5  a6   |  C(n+j,n)%p C(2n-j,n)%p C(n,j)%p")
    for j in range(n + 1):
        row = [mod_reduce(a[i, j], p) for i in range(1, 7)]
        cnj = comb(n + j, n) % p
        c2nj = comb(2 * n - j, n) % p
        cnj2 = comb(n, j) % p
        mark = ""
        if row[2] != 0:
            mark = "  <-a3!=0"
        print(f"  {j:>3} : " + " ".join(f"{r:>3}" for r in row)
              + f"   |  {cnj:>3} {c2nj:>3} {cnj2:>3}" + mark)
    w = mod_reduce(data["w"], p)
    print(f"  S_3 = w_n mod p = {w}")


if __name__ == "__main__":
    pairs = [(5, 7), (7, 11), (8, 13), (9, 13), (10, 17), (12, 23), (11, 19)]
    if len(sys.argv) > 2:
        pairs = [(int(sys.argv[1]), int(sys.argv[2]))]
    for n, p in pairs:
        show(n, p)
