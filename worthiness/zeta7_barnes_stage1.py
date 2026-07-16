"""
Stage 1: simplicial -> cubical change of variables for the totally symmetric
M_{0,10} cellular integral I_n.

Primal (over 0<t1<...<t7<1):
  B = t1 (t2-t1)(t3-t2)(t4-t3)(t5-t4)(t6-t5)(t7-t6)(1-t7)
  D = (t3-t1) t3 t5 (t5-t2)(t7-t2)(t7-t4)(1-t4)(1-t6)
  I_n = int B^n / D^{n+1} dt

Cubical map: x_i = t_i / t_{i+1} (t_8:=1), i.e. t_i = prod_{j>=i} x_j.
CLAIM (derived by hand):
  I_n = int_{[0,1]^7}
        x1^n x2^{2n+1} x3^n x4^{2n+1} x5^n x6^{2n+1} x7^n
        * prod_i (1-x_i)^n / P^{n+1} dx
  P = (1-x1 x2)(1-x2 x3 x4)(1-x2 x3 x4 x5 x6)(1-x4 x5 x6)(1-x4 x5 x6 x7)(1-x6 x7)
"""
import sympy as sp

x = sp.symbols('x1:8', positive=True)
x1,x2,x3,x4,x5,x6,x7 = x
n = sp.symbols('n', nonnegative=True, integer=True)

# t_i = product of x_j for j>=i
t = [sp.prod(x[j] for j in range(i,7)) for i in range(7)]  # t[0]=t1 ... t[6]=t7
t1,t2,t3,t4,t5,t6,t7 = t

B = t1*(t2-t1)*(t3-t2)*(t4-t3)*(t5-t4)*(t6-t5)*(t7-t6)*(1-t7)
D = (t3-t1)*t3*t5*(t5-t2)*(t7-t2)*(t7-t4)*(1-t4)*(1-t6)

# Jacobian d t / d x for t_i = prod_{j>=i} x_j : |J| = prod_j x_j^{j-1} (j=1..7)
J = sp.prod(x[j]**j for j in range(7))   # x1^0 x2^1 ... x7^6

# pushforward integrand for exponent n: B^n / D^{n+1} * J
# compare with claim
Pfactors = [1-x1*x2, 1-x2*x3*x4, 1-x2*x3*x4*x5*x6, 1-x4*x5*x6, 1-x4*x5*x6*x7, 1-x6*x7]
P = sp.prod(Pfactors)
mono = x1**n * x2**(2*n+1) * x3**n * x4**(2*n+1) * x5**n * x6**(2*n+1) * x7**n
claim = mono * sp.prod((1-x[i])**n for i in range(7)) / P**(n+1)

lhs = B**n / D**(n+1) * J

# Check ratio is identically 1 (do it for symbolic n via simplification of B, D, J structure)
ratio = sp.simplify(lhs/claim)
print("symbolic ratio lhs/claim =", ratio)
