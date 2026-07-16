import sympy as sp
y1,y2,y3,y4,y5,y6,y7=sp.symbols('y1:8',positive=True)
# rewrite the 3 clean factors in BZ (1-y3)(1+z y1y2) style
A=y3*y4; B=y3*y4*y5*(1-y6*y7); C=y4*y5*(1-y6*y7); Dd=y4*y5*(1-y7)
P2=1-A*(1-y1*y2); P3=1-B*(1-y1*y2); P4=1-C; P5=1-Dd
# P2=(1-A)(1+Z2 y1y2), Z2=A/(1-A);  P3=(1-B)(1+Z3 y1y2), Z3=B/(1-B)
print("P2/(1-A) =", sp.simplify(P2/(1-A)))     # expect 1+ Z2 y1 y2
print("P3/(1-B) =", sp.simplify(P3/(1-B)))
print("check 1+A/(1-A)*y1y2 - P2/(1-A):", sp.simplify((1+A/(1-A)*y1*y2)-P2/(1-A)))
print("check 1+B/(1-B)*y1y2 - P3/(1-B):", sp.simplify((1+B/(1-B)*y1*y2)-P3/(1-B)))
# So LEFT pair (y1,y2) sits under TWO factors (1+Z2 y1y2)(1+Z3 y1y2): Appell-type
# RIGHT: P4,P5 do NOT contain y1y2; the right pair (y6,y7) enters P3,P4 via (1-y6y7)
# and P5 via (1-y7) alone -> asymmetric.
