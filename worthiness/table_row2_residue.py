#!/usr/bin/env python3
r"""
table_row2_residue.py  -- [COMPUTED, exact - sympy + mpmath]

ROW 2 of the lattice-index table: the weight-3 Apery/Beukers zeta(3) family on M_{0,6}.

GOAL. Locate the factor 2 in Rhin-Viola's "Q + 2 Z zeta(3)" (Acta Arith. 97 (2001),
Thm 2.1) inside the Beukers triple integral
     J_n = \int\int\int_{[0,1]^3} [x(1-x)y(1-y)z(1-z)]^n / (1-(1-xy)z)^{n+1} dx dy dz.
We route the valuation chain the SAME way as the weight-5 case (h2_p2_deRham.py):
compute the integrand's de Rham normalization by exact iterated residue / integration,
and decide whether the 2 is
  (i)   a de Rham period-normalization factor (an integrand feature, present at n=0),
  (ii)  a Betti integral-lattice index (a homology-lattice refinement, like M_{0,8} p=2),
  (iii) a genuinely different double-pole / log-doubling residue phenomenon.

This script does the n=0 GEOMETRIC PERIOD exactly and isolates the 2.
"""
import sympy as sp

x, y, z, k = sp.symbols('x y z k', positive=True)
m = sp.symbols('m', positive=True, integer=True)

print("="*74)
print("ROW 2 -- the n=0 geometric period of the Beukers zeta(3) integrand")
print("="*74)

# ---- Step 1: the z-integral of the simple pole 1/(1-(1-xy)z) over [0,1] -------
# The only z-pole is at z = 1/(1-xy) > 1 (OUTSIDE [0,1] for xy in (0,1)):
# so this is NOT a residue at an interior pole -- it is a boundary logarithm.
w = 1 - x*y
zint = sp.integrate(1/(1-w*z), (z, 0, 1))
zint = sp.simplify(zint)
print("\n[Step 1] int_0^1 dz/(1-(1-xy)z) =", zint)
# expected: -ln(xy)/(1-xy)  =  (-ln x - ln y)/(1-xy)
zint_target = (-sp.log(x) - sp.log(y))/(1-x*y)
print("         equals (-ln x - ln y)/(1-xy)? ",
      sp.simplify(zint - zint_target) == 0)
print("  --> the z-pole sits at z=1/(1-xy) > 1, outside [0,1]: the integral is a")
print("      BOUNDARY LOGARITHM ln(xy), not an interior residue.  ln(xy)=ln x+ln y")
print("      is the symmetric double-log; the two summands are the seed of the 2.")

# ---- Step 2: the (x,y)-integral, term by term, isolating the 2 ---------------
# 1/(1-xy) = sum_{k>=0} (xy)^k ;  -ln(xy) = -ln x - ln y.
# int_0^1 x^k (-ln x) dx = 1/(k+1)^2 ;  int_0^1 y^k dy = 1/(k+1).
# So the (-ln x) piece and the (-ln y) piece EACH give 1/(k+1)^3, summing to
#   [1/(k+1)^3] + [1/(k+1)^3] = 2/(k+1)^3.
kk = sp.symbols('kk', integer=True, nonnegative=True)
term_lnx = sp.integrate(x**kk*(-sp.log(x)), (x,0,1)) * sp.integrate(y**kk, (y,0,1))
term_lny = sp.integrate(x**kk, (x,0,1)) * sp.integrate(y**kk*(-sp.log(y)), (y,0,1))
print("\n[Step 2] per-mode k contributions of -ln(xy)/(1-xy):")
print("   from -ln x :", sp.simplify(term_lnx), "   from -ln y :", sp.simplify(term_lny))
print("   SUM        :", sp.simplify(term_lnx+term_lny),
      "  <-- the factor 2 = (two IDENTICAL log-summands), a de Rham symmetry")
total = sp.summation(sp.simplify(term_lnx+term_lny), (kk, 0, sp.oo))
print("\n[Step 2] J_0 = sum_{k>=0} 2/(k+1)^3 =", total, " = 2*zeta(3)")
J0_num = sp.N(total, 30)
print("         numeric:", J0_num, "  2*zeta(3) =", sp.N(2*sp.zeta(3),30))

print("\n[VERDICT-n0] The n=0 geometric period is J_0 = 2*zeta(3) EXACTLY.")
print("  The 2 is the coefficient of zeta(3) in the intrinsic period of the")
print("  rank-2 motive (gr^W = Q(0) + Q(-3)); it originates from the SYMMETRIC")
print("  double-logarithm ln(xy)=ln x+ln y in the integrand -- a de Rham /")
print("  integrand-normalization feature, NOT a homology-lattice index.")
