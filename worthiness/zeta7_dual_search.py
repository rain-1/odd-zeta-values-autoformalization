#!/usr/bin/env python3
"""Broad structured search for A_n = 1,61,52921 as an Apery-like multisum.
Building blocks generalize Q_n = sum_{k1,k2} w(k1)w(k2) C(n+k1+k2,n),
  w(k) = C(n+k,n) C(n,k)^2."""
from math import comb
from itertools import product

def wpow(n, k, a, b):
    # C(n+k,n)^a * C(n,k)^b
    return comb(n+k, n)**a * comb(n, k)**b

TARGET = [1, 61, 52921]

def cbin(n, s):  # C(n+s, n)
    return comb(n+s, n)

# --- DOUBLE sums with varied weight and coupling ---
def double(n, wa, wb, coup):
    t = 0
    for k1 in range(n+1):
        for k2 in range(n+1):
            t += wpow(n,k1,wa,wb)*wpow(n,k2,wa,wb)*coup(n,k1,k2)
    return t

double_coups = {
 "C(n+k1+k2)": lambda n,a,b: cbin(n,a+b),
 "C(n+k1+k2)^2": lambda n,a,b: cbin(n,a+b)**2,
 "C(n+k1+k2)C(n+k1)C(n+k2)": lambda n,a,b: cbin(n,a+b)*cbin(n,a)*cbin(n,b),
 "C(2n+k1+k2,n)": lambda n,a,b: comb(2*n+a+b, n),
 "C(n+k1+k2)*C(n+k1+k2,k1)": lambda n,a,b: cbin(n,a+b)*comb(n+a+b, a) if a+b<=n+a+b else cbin(n,a+b),
}

print("DOUBLE-sum scan (wa,wb)=weight exps, vs [1,61,52921]:")
found=[]
for wa in range(0,3):
    for wb in range(0,4):
        for cn,cp in double_coups.items():
            try:
                vals=[double(n,wa,wb,cp) for n in range(3)]
            except Exception: continue
            if vals==TARGET:
                print("  *** MATCH:", f"w=C(n+k,n)^{wa}C(n,k)^{wb}", cn, vals); found.append((wa,wb,cn))
            elif vals[0]==1 and vals[1]==61:
                print("  partial(61):", f"w^{wa},{wb}", cn, vals)

# --- TRIPLE sums, weight w(k)=C(n+k,n)C(n,k)^2, many couplings ---
def triple(n, coup):
    t=0
    for k1,k2,k3 in product(range(n+1),repeat=3):
        t += wpow(n,k1,1,2)*wpow(n,k2,1,2)*wpow(n,k3,1,2)*coup(n,k1,k2,k3)
    return t

triple_coups = {
 "min pair sums": lambda n,a,b,c: cbin(n, min(a+b,b+c,a+c)),
 "C(n+k1+k2)*C(n+k3)": lambda n,a,b,c: cbin(n,a+b)*cbin(n,c),
 "C(n+k1+k2+k3) - correction": lambda n,a,b,c: cbin(n,a+b+c),
 "C(n+k1+k2)+C(n+k2+k3)+..pairs (sum not prod)": lambda n,a,b,c: cbin(n,a+b)+cbin(n,b+c)+cbin(n,a+c)-2,
}
print("\nTRIPLE-sum extra couplings:")
for cn,cp in triple_coups.items():
    try:
        vals=[triple(n,cp) for n in range(3)]
    except Exception: continue
    print(f"  {cn:40s}: {vals}  match={vals==TARGET}")

# --- recurrence probe: does 1,61,52921 fit a nice 2nd/3rd order? need 4th term though ---
print("\nRatios: 61/1=%.3f  52921/61=%.3f" % (61, 52921/61))
