"""proof_sym_v2_descent.py -- numeric confirmation of the (P-hat) descent (v2 SS6).

Checks that the zeta(3) descent sum equals 2*I''_n = 2(Q_n zeta(3) - Phat_n),
confirming the structural factor 1/2 in (P-hat).  n=1 (fast, 18 digits).
"""
import mpmath as mp
from math import comb
from fractions import Fraction
mp.mp.dps = 18

def J3(p0, p1, p2, p3, q1, q2, q3):
    def f(y1, y2, y3):
        return (y1**p1*(1-y1)**q1*y2**p2*(1-y2)**q2*y3**p3*(1-y3)**q3
                / (1 - y3*(1 - y1*y2))**(p0 + 1))
    return mp.quad(lambda y1: mp.quad(lambda y2: mp.quad(
        lambda y3: f(y1, y2, y3), [0, 1]), [0, 1]), [0, 1])

def descent_sum(n):
    tot = mp.mpf(0)
    for k in range(n, 2*n + 1):
        c = comb(k, n) * comb(n, k - n)**2
        if c == 0:
            continue
        tot += (-1)**k * c * J3(n, n, n, 2*n - k, n, n, k)
    return (-1)**(3*n) * tot

data = {1: (21, Fraction(101, 4))}   # (Q_n, Phat_n)
for n, (Q, Ph) in data.items():
    S = descent_sum(n)
    Ipp = Q*mp.zeta(3) - mp.mpf(Ph.numerator)/Ph.denominator     # I''_n
    d1 = abs(S - Ipp); d2 = abs(S - 2*Ipp)
    print(f"n={n}: descent sum = {mp.nstr(S,12)}")
    print(f"      2*I''_n     = {mp.nstr(2*Ipp,12)}   |sum-2 I''|={mp.nstr(d2,4)}  "
          f"(vs |sum-I''|={mp.nstr(d1,4)})")
    print(f"      => descent computes 2 I''_n, so Phat carries the structural 1/2: "
          f"{'OK' if d2 < mp.mpf(10)**-12 else 'FAIL'}")
