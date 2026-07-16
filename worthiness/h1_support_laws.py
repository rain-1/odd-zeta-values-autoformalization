"""h1_support_laws.py -- exact denominator laws for the symmetric P_n, sharpened.

Reads den(P_n) from audit.recover_p for n<=5 (exact, live) and from the
PROOF_SYMMETRIC_v2 verified table for n=6,7,8 (den only; integrality laws
depend only on den(P_n)).  Checks, per prime:

  (T)  target        : ord_p den(P_n) <= 5*ord_p(d_n) + [p==2]*2 + [p==3]*1
  (WP) well-poised    : for p>=5,  p | den(P_n)  =>  p <= n      (NOT just <=2n+1)
  (EMN) degree bound  : ord_p den(P_n) <= 5*ord_p(d_{2n})   (what an EMN/Zudilin
                        degree-(2n+1) partial-fraction bound would give)
  (GAP) whether (EMN) is strictly weaker than (T): exhibit a prime in (n,2n]
        that (EMN) allows but (WP)/(T) forbids.

The point: (WP) -- absence of primes in (n,2n] for p>=5 -- is the Rhin-Viola
well-poised collapse; it is what makes the constant d_n rather than d_{2n}.
"""
from fractions import Fraction
from math import gcd

def d_lcm(N):
    r = 1
    for k in range(2, N + 1):
        r = r * k // gcd(r, k)
    return r

def ordp(m, p):
    if m == 0:
        return float('inf')
    e = 0
    while m % p == 0:
        m //= p
        e += 1
    return e

# den(P_n): exact.  n<=5 recomputed live; 6..8 from the verified v2 table.
DEN = {}
try:
    from audit import recover_p
    for n in range(1, 6):
        _, P, _ = recover_p([1] * 8, n)
        DEN[n] = P.denominator
    print("den(P_n) for n<=5 recomputed live via recover_p.")
except Exception as e:
    print(f"[live recompute skipped: {e}] using table values for all n.")
    DEN.update({1: 2**2, 2: 2**7*3, 3: 2**7*3**4,
                4: 2**12*3**3, 5: 2**12*3**4*5**5})
DEN[6] = 2**12 * 3**6 * 5**5
DEN[7] = 2**12 * 3**4 * 5**5 * 7**5
DEN[8] = 2**17 * 3**6 * 5**5 * 7**4

def primes_in(m):
    out = []
    x = m
    p = 2
    while p * p <= x:
        if x % p == 0:
            out.append(p)
            while x % p == 0:
                x //= p
        p += 1
    if x > 1:
        out.append(x)
    return out

print(f"\n{'n':>2} {'den(P_n)':>28}  target  well-poised  EMN-degree(2n)")
allT = allWP = True
for n in sorted(DEN):
    den = DEN[n]
    dn = d_lcm(n)
    d2n = d_lcm(2 * n)
    okT = okWP = okEMN = True
    for p in primes_in(den):
        e = ordp(den, p)
        cap_T = 5 * ordp(dn, p) + (2 if p == 2 else 1 if p == 3 else 0)
        cap_EMN = 5 * ordp(d2n, p)
        if e > cap_T:
            okT = False
        if p >= 5 and e > 0 and p > n:
            okWP = False
        if e > cap_EMN + (2 if p == 2 else 1 if p == 3 else 0):
            okEMN = False
    allT &= okT
    allWP &= okWP
    # factor string
    fs = "·".join(f"{p}^{ordp(den,p)}" if ordp(den,p) > 1 else f"{p}"
                  for p in primes_in(den))
    print(f"{n:>2} {fs:>28}  {'PASS' if okT else 'FAIL':>6}  "
          f"{'PASS' if okWP else 'FAIL':>10}  {'PASS' if okEMN else 'FAIL':>13}")

print(f"\n(T)  target  12*d_n^5*P_n in Z, 2-excess<=2, 3-excess<=1 : "
      f"{'ALL PASS' if allT else 'FAIL'}")
print(f"(WP) p>=5 support of den(P_n) lies in {{p<=n}}            : "
      f"{'ALL PASS' if allWP else 'FAIL'}")

# The gap: which primes does EMN-degree allow but WP forbids?
print("\nGap primes (in (n,2n], p>=5): EMN degree bound d_{2n} admits them, "
      "well-poised (data) excludes them:")
for n in sorted(DEN):
    gap = [p for p in range(n + 1, 2 * n + 1)
           if p >= 5 and all(p % q for q in range(2, p))]
    if gap:
        appear = [p for p in gap if DEN[n] % p == 0]
        print(f"  n={n}: primes in (n,2n]={gap}; actually dividing den(P_n): "
              f"{appear if appear else 'NONE  <-- well-poised collapse'}")
