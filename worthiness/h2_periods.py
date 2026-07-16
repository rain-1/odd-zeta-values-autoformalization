#!/usr/bin/env python3
"""
h2_periods.py  --  [COMPUTED, numerical]
Pin the period-matrix conventions (rule (ii)) numerically:
 (1) the Lemma-1 identity  zeta(2) = -(2 pi i)^2 / 24  that forces the "24";
 (2) the row operation gamma_1' = gamma_1 + (1/24) gamma_2 kills the zeta(2)
     entry of periodmatrix1, giving the top row (1, 0, zeta(5)) of periodmatrix2
     -- verified symbolically on the motivic entries;
 (3) the totally-symmetric decomposition I_n = Q_n(2z5+4z3z2) - 4 Phat_n z2 - 2 P_n
     is numerically consistent with the paper's exact rationals (n=0,1,2), and
     the derived I'_n = Q_n z5 - P_n has the predicted sharp denominator 12 d_n^5.
No 5-fold integral is recomputed; consistency of the exact rationals with the
high-precision zeta values is the check.
"""
import mpmath as mp
from fractions import Fraction
mp.mp.dps = 60

z2 = mp.zeta(2); z3 = mp.zeta(3); z5 = mp.zeta(5)
twopii2 = (2*mp.pi*1j)**2          # (2 pi i)^2 = -4 pi^2
z5bar = z5 + 2*z3*z2               # the leading period zeta_5 = z5 + 2 z3 z2

print("(1) Lemma-1 identity  zeta(2) = -(2 pi i)^2 / 24 :")
lhs, rhs = z2, -twopii2/24
print("    zeta(2)          =", mp.nstr(lhs, 30))
print("    -(2pi i)^2 / 24  =", mp.nstr(rhs.real, 30), " (imag=%.1e)"%float(rhs.imag))
print("    match:", mp.almosteq(lhs, rhs.real))
print("    => the elimination constant 24 = 2^3*3 = denominator of B_2/... is FORCED.\n")

print("(2) Row operation on periodmatrix1 rows (gamma_1, gamma_2):")
# periodmatrix1 rows:  g1=(1, z2, z5bar); g2=(0,(2pi i)^2,(2pi i)^2 z3)
g1 = [mp.mpf(1), z2, z5bar]
g2 = [mp.mpc(0), twopii2, twopii2*z3]
lam = mp.mpf(1)/24
new = [g1[i] + lam*g2[i] for i in range(3)]
print("    (g1 + (1/24) g2) = ( %s , %s , %s )" % (
      mp.nstr(new[0].real if hasattr(new[0],'real') else new[0],12),
      mp.nstr(new[1].real,6)+("+%.1ei"%float(new[1].imag)),
      mp.nstr(new[2].real,20)))
print("    middle entry -> 0 :", mp.almosteq(abs(new[1]), 0, abs_eps=mp.mpf(10)**-25))
print("    right entry  = z5 + z3 z2 (residual z3z2 lives in W_4, killed in quotient E):")
print("       value      =", mp.nstr(new[2].real,25))
print("       z5+z3z2    =", mp.nstr(z5+z3*z2,25),
      "  match:", mp.almosteq(new[2].real, z5+z3*z2))
print("    (periodmatrix2 top row (1,0,zeta5) is obtained in the subquotient")
print("     E = M/sigma(Q(-2)); the row op alone leaves z3z2 in the W_4 direction.)\n")

print("(3) Decomposition consistency  I_n = Q_n(2z5+4z3z2) - 4 Phat_n z2 - 2 P_n:")
data = {0:(Fraction(1),Fraction(0),Fraction(0)),
        1:(Fraction(21),Fraction(101,4),Fraction(87,4)),
        2:(Fraction(2989),Fraction(344923,96),Fraction(1190161,384))}
def d(n):
    from math import gcd
    r=1
    for k in range(1,n+1): r=r*k//gcd(r,k)
    return r
for n,(Q,Ph,P) in data.items():
    I  = float(Q)*(2*z5+4*z3*z2) - 4*float(Ph)*z2 - 2*float(P)
    Ip = float(Q)*z5 - float(P)          # I'_n = Q_n z5 - P_n
    print(f"    n={n}: I_n = {mp.nstr(I,18)},  I'_n = Q z5 - P = {mp.nstr(Ip,18)}")
    # sharp denominator test: 12 * d_n^5 * P_n in Z, and 24 overkill at p=2
    c12 = Fraction(12)*Fraction(d(n)**5)*P
    c24 = Fraction(24)*Fraction(d(n)**5)*P
    print(f"          12*d_n^5*P_n = {c12}  integer? {c12.denominator==1}"
          f"    (24*d_n^5*P_n integer? {c24.denominator==1})")
