"""Sector measurement for the zeta(7) family linear forms (2026-07-17 night).

Fact: chi(lambda) = lambda^4 - 6340 lambda^3 + 67974 lambda^2 - 6340 lambda + 1
factors over Q(sqrt(3)) as (lambda^2 - a lambda + 1)(lambda^2 - b lambda + 1),
a,b = 3170 +- 1824 sqrt(3)  [check: a+b=6340, 2+ab=2+3170^2-3*1824^2=67974].
Sector A roots: {6329.2605, 1.57996e-4}; sector B roots: {10.6454, 0.0939374}.

Irrationality threshold for a weight-7 form with d_n^7-type denominators:
decay < e^{-7} = 9.1188e-4.  Sector A's small root PASSES (margin e^{1.75});
sector B's 0.0939 FAILS by two orders.

MEASUREMENT: I''_n = -9 q_n zeta(5) + 2 s_n zeta(3) - Phat_n satisfies the exact
order-4 operator (q, s, Phat all do). Propagating I''_n numerically at 300 digits
from the four exact anchors (using s_3 = 1396906795/3, Phat_3 = 232175579999/972)
gives ratios I''_{n+1}/I''_n:
  0.0042, 0.0181, 0.0306, 0.0402, ..., 0.0833 (n=29), monotone toward 0.0939374.
VERDICT: the descended weight-5 ladder rides sector B. It is definitively
un-worthy (0.0939 >> e^{-5} = 6.74e-3, its own threshold).

OPEN: the primitive form I'_n = (75/4) q_n zeta(7) - 3 s_n zeta(5) - P_n does NOT
satisfy the operator (P_n is not in its solution span); its own operator L' is
unknown. Its n<=2 transient ratios (0.0034, 0.0180) track I'' almost exactly.
If I' asymptotically rides sector A's 1.58e-4: d_n^7 |I'_n| -> 0 and (given a
denominator theorem of the (CB) type) one of zeta(5), zeta(7) is irrational.
If it rides sector B: the family is un-worthy at weight 7 as well.
Everything converges on I'_3 / the primitive operator L'.
"""
import json
from mpmath import mp, zeta, mpf

mp.dps = 300
op = json.load(open('worthiness/zeta7_q_recurrence.json' if __name__ != '__main__' else 'zeta7_q_recurrence.json'))
C = op['Cpoly']

def cval(k, n):
    coeffs = C[str(k)] if isinstance(C, dict) else C[k]
    return sum(int(c) * n**e for e, c in enumerate(coeffs))

z5, z3 = zeta(5), zeta(3)
q = [mpf(1), mpf(61), mpf(52921), mpf(94357501)]
s = [mpf(0), mpf(300), mpf(261153), mpf(1396906795)/3]
Ph = [mpf(0), mpf(152), mpf(535857)/4, mpf(232175579999)/972]
I = [-9*q[n]*z5 + 2*s[n]*z3 - Ph[n] for n in range(4)]
for n in range(4, 30):
    I.append(-(sum(cval(k, n-4)*I[n-4+k] for k in range(4))) / cval(4, n-4))
for n in range(1, 30):
    print(n, mp.nstr(I[n]/I[n-1], 8))
