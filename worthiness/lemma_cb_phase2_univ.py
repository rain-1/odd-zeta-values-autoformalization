"""Test: is p_n/q_n a universal p-adic constant across n sharing a band prime p?
rho_n := p_n/q_n  (p-adic). Universality: v_p(rho_n - rho_m) large for n != m.
Also test the 2x2 dependence directly: v ~ lambda*w + mu*u with same (lambda,mu) for both forms.
"""
from fractions import Fraction
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

for p in [5, 7, 11, 13]:
    lo = (3*p)//2  # n >= 3p/2  (p <= 2n/3)
    hi = 2*p - 1   # n < 2p     (p > n/2)
    rows = []
    for n in range(lo, hi+1):
        d = all_data(n)
        w, wt, v, vt, u, ut = d["w"], d["wt"], d["v"], d["vt"], d["u"], d["ut"]
        pn = wt*v - w*vt
        qn = u*wt - ut*w
        rows.append((n, pn, qn))
    print(f"p={p}: band n in [{lo},{hi}]")
    for i in range(len(rows)):
        n, pn, qn = rows[i]
        print(f"   n={n:3d}: ord(p_n)={ordp(pn,p):3d}  ord(q_n)={ordp(qn,p):3d}  rho=p_n/q_n ord={ordp(pn/qn,p) if qn else 'inf'}")
    # pairwise universality of rho
    for i in range(len(rows)):
        for j in range(i+1, len(rows)):
            n1, p1, q1 = rows[i]; n2, p2, q2 = rows[j]
            if q1 and q2:
                diff = p1/q1 - p2/q2
                print(f"   v_p(rho_{n1} - rho_{n2}) = {ordp(diff,p)}   [terms have ord {ordp(p1/q1,p)},{ordp(p2/q2,p)}]")
