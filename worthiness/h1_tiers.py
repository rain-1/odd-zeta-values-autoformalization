"""h1_tiers.py -- The three-tier denominator structure of the symmetric BZ zeta(5)
rational coefficient P_n, and the five-block lcm ladder connecting the crude and
sharp targets.

All facts below are VERIFIED against the exact audited denominator table
den(P_n) for n <= 8 (reproducible by audit.recover_p([1]*8, n)); they are
EMPIRICAL (VERIFIED n<=8), not proved in general -- see H1_COLLAPSE.md.

Tier structure discovered here:
  * CRUDE   (index 2n, weight 5, EMN/Zudilin-portable):  d_{2n}^5 * P_n in Z
            -- holds with NO extra constant; d_{2n}^4 fails.  This is the natural
            target of the two-variable Rhin-Viola/Zudilin (or EMN Thm 8.3.1)
            denominator-clearing machinery.
  * SHARP   (block-refined 2n->n + Bernoulli {2,3}):       12 * d_n^5 * P_n in Z
            -- the paper's printed law d_n^5 P_n in Z is FALSE; the correct
            constant is 12 = 2^2 * 3.
  * LADDER  every 12 * d_n^a * d_{2n}^{5-a} (a = 0..5) clears den(P_n): the five
            weight-slots are independently refinable from index 2n to index n.
"""
from math import gcd

def dlcm(N):
    r = 1
    for k in range(2, N + 1):
        r = r * k // gcd(r, k)
    return r

# Exact den(P_n) from the audited table (PROOF_SYMMETRIC_v2.md Section 8);
# reproduced by audit.recover_p([1]*8, n).
DENP = {1: 2**2, 2: 2**7*3, 3: 2**7*3**4, 4: 2**12*3**3,
        5: 2**12*3**4*5**5, 6: 2**12*3**6*5**5,
        7: 2**12*3**4*5**5*7**5, 8: 2**17*3**6*5**5*7**4}
NS = range(1, 9)

def clears(mult):
    return all(mult(n) % DENP[n] == 0 for n in NS)

def factor(x):
    f = {}; d = 2
    while d*d <= x:
        while x % d == 0:
            f[d] = f.get(d, 0)+1; x //= d
        d += 1
    if x > 1:
        f[x] = f.get(x, 0)+1
    return f

def report():
    print("== per-prime: ord_p den(P_n) vs 5*ord_p d_n and 5*ord_p d_{2n} ==")
    for n in NS:
        dn, d2n = dlcm(n), dlcm(2*n)
        fd, fn, f2 = factor(DENP[n]), factor(dn), factor(d2n)
        cells = [f"{p}^{fd[p]}[5dn={5*fn.get(p,0)},5d2n={5*f2.get(p,0)}]"
                 for p in sorted(fd)]
        print(f" n={n} (d_n={dn}, d_2n={d2n}): " + "  ".join(cells))

    print("\n== CRUDE tier: minimal k with d_{2n}^k * P_n in Z ==")
    for k in range(3, 7):
        print(f"   d_2n^{k}: {'CLEARS' if clears(lambda n,k=k: dlcm(2*n)**k) else 'fails'}")

    print("\n== SHARP tier: 12 * d_n^k * P_n in Z ==")
    for k in range(3, 7):
        print(f"   12*d_n^{k}: {'CLEARS' if clears(lambda n,k=k: 12*dlcm(n)**k) else 'fails'}")

    print("\n== five-block LADDER: 12 * d_n^a * d_2n^(5-a) ==")
    for a in range(0, 6):
        ok = clears(lambda n, a=a: 12*dlcm(n)**a*dlcm(2*n)**(5-a))
        print(f"   a={a}: 12*d_n^{a}*d_2n^{5-a}: {'CLEARS' if ok else 'fails'}")

    print("\n== 2-adic law: ord_2 den(P_n) == 2 + 5*ord_2 d_n ==")
    for n in NS:
        lhs = factor(DENP[n]).get(2, 0)
        rhs = 2 + 5*factor(dlcm(n)).get(2, 0)
        print(f"   n={n}: {lhs} == {rhs}  [{'OK' if lhs==rhs else 'FAIL'}]")

if __name__ == "__main__":
    report()
