import sympy as sp
y=sp.symbols('y1:8',positive=True); y1,y2,y3,y4,y5,y6,y7=y
n=sp.symbols('n',integer=True,nonnegative=True)
x1=(1-y1)/(1-y1*y2); x2=1-y1*y2; x3=y3; x4=y4; x5=y5; x6=1-y6*y7; x7=(1-y7)/(1-y6*y7)
X=[x1,x2,x3,x4,x5,x6,x7]; b=[n,2*n+1,n,2*n+1,n,2*n+1,n]
P=[1-x1*x2,1-x2*x3*x4,1-x2*x3*x4*x5*x6,1-x4*x5*x6,1-x4*x5*x6*x7,1-x6*x7]
integ_x=sp.prod(X[i]**b[i]*(1-X[i])**n for i in range(7))/sp.prod(P[i]**(n+1) for i in range(6))
Jac=sp.Matrix([[sp.diff(X[i],y[j]) for j in range(7)] for i in range(7)])
integ_y=sp.simplify(integ_x*Jac.det())
P2=1-y3*y4*(1-y1*y2); P3=1-y3*y4*y5*(1-y1*y2)*(1-y6*y7); P4=1-y4*y5*(1-y6*y7); P5=1-y4*y5*(1-y7)
meas=y4**(2*n+1)*y1**n*y2**n*y3**n*y5**n*y6**n*y7**n*sp.prod((1-y[i])**n for i in range(7))
claim=meas/(P2*P3*P4*P5)**(n+1)
print("corrected J-form ratio =", sp.simplify(integ_y/claim))
