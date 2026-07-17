"""Phase-2 reconnaissance: p-adic valuations in the first open band n/2 < p <= 2n/3.
1) Verify Kummer band structure: kappa = [p <= 2n/3] for n/2 < p <= n.
2) Exact ords of w, wt, v, vt, p_n at band primes; slack of (CB).
3) Verify the p-adic lift: k^p - k - ((k+j)^p - (k+j)) = p*G_j, G_j in Z[u].
"""
from fractions import Fraction
from math import comb
import sys
sys.path.insert(0, '.')
from lemma_cb_explore import all_data, primes_in

def ordp(x, p):
    if x == 0: return 99
    num, den = x.numerator, x.denominator
    v = 0
    while num % p == 0: num //= p; v += 1
    while den % p == 0: den //= p; v -= 1
    return v

# 1) Kummer check
bad = 0
for n in range(4, 200):
    for p in primes_in(n//2+1, n):
        if p < 5: continue
        kappa = ordp(Fraction(comb(2*n,n)), p)
        pred = 1 if p <= 2*n/3 else 0
        if kappa != pred: bad += 1; print("KUMMER MISMATCH", n, p, kappa, pred)
print(f"Kummer band law (n<200): {'OK' if bad==0 else 'FAIL'}")

# 3) p-adic lift check (polynomial identity over Z)
from sympy import symbols, expand, Poly
k = symbols('k')
lift_ok = True
for p in [5,7,11]:
    for j in [0,1,3]:
        diff = expand((k**p - k) - ((k+j)**p - (k+j)))
        P = Poly(diff, k)
        if any(c % p != 0 for c in P.all_coeffs()):
            lift_ok = False; print("LIFT FAIL", p, j)
print(f"p-adic lift k^p-k = (k+j)^p-(k+j) + p*G_j over Z: {'OK' if lift_ok else 'FAIL'}")

# 2) band-prime valuations
print("\n n   p | ord: w    wt    v    vt   p_n | need>=  slack")
for n in range(6, 25):
    d = all_data(n)
    for p in primes_in(n//2+1, (2*n)//3):
        if p < 5: continue
        w, wt = d["w"], d["wt"]; v, vt = d["v"], d["vt"]
        pn = wt*v - w*vt
        need = 1 - 5*1  # kappa=1, L=1 in this band
        print(f"{n:3d} {p:3d} |     {ordp(w,p):3d}  {ordp(wt,p):3d}  {ordp(v,p):3d}  {ordp(vt,p):3d}  {ordp(pn,p):3d} |  {need:3d}   {ordp(pn,p)-need:3d}")
