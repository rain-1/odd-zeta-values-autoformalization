"""
Stage 2 exploration: y-substitution (BZ-style leaf collapse) on the cubical form.

Cube form denominators: P1=1-x1x2, P2=1-x2x3x4, P3=1-x2x3x4x5x6,
P4=1-x4x5x6, P5=1-x4x5x6x7, P6=1-x6x7.

BZ (M_{0,8}) collapsed the two outer leaves (1-x1x2),(1-x4x5) to monomials
y1,y5 via x1=(1-y1)/(1-y1y2), x2=1-y1y2 (and mirror on the right), leaving 2
coupled factors 1-y3(1-y1y2), 1-y3(1-y4y5).

Here we test the analogous leaf collapse:
  x1=(1-y1)/(1-y1 y2), x2=1-y1 y2        -> P1 = 1-x1x2 = y1
  x7=(1-y7)/(1-y6 y7), x6=1-y6 y7        -> P6 = 1-x6x7 = y7
  x3=y3, x4=y4, x5=y5
and print the transformed P2..P5 to see how many coupled factors remain and
whether they collapse further.
"""
import sympy as sp

y1,y2,y3,y4,y5,y6,y7 = sp.symbols('y1:8', positive=True)

x1=(1-y1)/(1-y1*y2)
x2=1-y1*y2
x3=y3
x4=y4
x5=y5
x6=1-y6*y7
x7=(1-y7)/(1-y6*y7)

def show(name,expr):
    print(name,"=",sp.simplify(sp.factor(sp.together(expr))))

show("P1=1-x1x2", 1-x1*x2)
show("P6=1-x6x7", 1-x6*x7)
show("P2=1-x2x3x4", 1-x2*x3*x4)
show("P3=1-x2x3x4x5x6", 1-x2*x3*x4*x5*x6)
show("P4=1-x4x5x6", 1-x4*x5*x6)
show("P5=1-x4x5x6x7", 1-x4*x5*x6*x7)

# Jacobian of (x1..x7)->(y1..y7): only x1,x2 depend on y1,y2 and x6,x7 on y6,y7,
# rest identity. Block-diagonal.
X=[x1,x2,x3,x4,x5,x6,x7]
Y=[y1,y2,y3,y4,y5,y6,y7]
Jac=sp.Matrix([[sp.diff(X[i],Y[j]) for j in range(7)] for i in range(7)])
detJ=sp.simplify(Jac.det())
print("Jacobian det =", sp.factor(detJ))
