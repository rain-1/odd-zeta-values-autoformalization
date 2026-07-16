#!/usr/bin/env python3
"""Route 2: identify A_n = 1,61,52921 (zeta(7) leading coeff) as a TRIPLE Apery-like sum,
generalizing the zeta(5) double sum  Q_n = sum w(k1)w(k2) C(n+k1+k2,n),
where w(k)=C(n+k,n)*C(n,k)^2  and  Q_0,Q_1,Q_2 = 1,21,2989."""
from math import comb
from itertools import product

def w(n, k):
    return comb(n+k, n) * comb(n, k)**2

def C(n, k):
    return comb(n, k) if 0 <= k <= n else 0

# sanity: reproduce Q_n double sum
def Q(n):
    return sum(w(n,k1)*w(n,k2)*comb(n+k1+k2, n) for k1 in range(n+1) for k2 in range(n+1))
print("Q_n (zeta5 double sum) n=0,1,2,3:", [Q(n) for n in range(4)], " expect 1,21,2989,...")

TARGET = [1, 61, 52921]

def triple(n, coupling):
    tot = 0
    for k1,k2,k3 in product(range(n+1), repeat=3):
        tot += w(n,k1)*w(n,k2)*w(n,k3)*coupling(n,k1,k2,k3)
    return tot

cands = {
 "total-sum C(n+k1+k2+k3,n)": lambda n,a,b,c: comb(n+a+b+c, n),
 "all-pairs prod C(n+ki+kj,n)": lambda n,a,b,c: comb(n+a+b,n)*comb(n+b+c,n)*comb(n+a+c,n),
 "chain C(n+k1+k2)C(n+k2+k3)": lambda n,a,b,c: comb(n+a+b,n)*comb(n+b+c,n),
 "total^2": lambda n,a,b,c: comb(n+a+b+c,n)**2,
 "all-pairs+total": lambda n,a,b,c: comb(n+a+b,n)*comb(n+b+c,n)*comb(n+a+c,n)*comb(n+a+b+c,n),
 "pair(1,2)*total": lambda n,a,b,c: comb(n+a+b,n)*comb(n+a+b+c,n),
}

print("\nTRIPLE-sum candidates vs A_n=1,61,52921:")
for name, cp in cands.items():
    vals = [triple(n, cp) for n in range(3)]
    match = (vals == TARGET)
    ratio = (vals[1]/vals[0], vals[2]/vals[1]) if vals[0] else None
    print(f"  {name:38s}: {vals}  match={match}")
