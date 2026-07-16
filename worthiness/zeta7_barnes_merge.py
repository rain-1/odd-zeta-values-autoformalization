import sympy as sp
y1,y2,y3,y4,y5=sp.symbols('y1:6',positive=True); a,b=sp.symbols('a b',positive=True)
xset={y1,y2,y3,y4,y5,a,b}
for nval in (0,1,2):
    n=nval
    y6=(1-a)/(1-a*b); y7=1-a*b
    P2=1-y3*y4*(1-y1*y2); P3=1-y3*y4*y5*(1-y1*y2)*(1-y6*y7); P4=1-y4*y5*(1-y6*y7); P5=1-y4*y5*(1-y7)
    meas=y4**(2*n+1)*y1**n*y2**n*y3**n*y5**n*y6**n*y7**n*((1-y1)*(1-y2)*(1-y3)*(1-y4)*(1-y5)*(1-y6)*(1-y7))**n
    Jac=a/(1-a*b)   # computed |d(y6,y7)/d(a,b)|
    integ=sp.cancel(meas*Jac/(P2*P3*P4*P5)**(n+1))
    num,den=sp.fraction(integ)
    facs=[(tuple(sorted(str(v) for v in (f.free_symbols&xset))),e) for f,e in sp.factor_list(den)[1] if len(f.free_symbols&xset)>=2]
    print(f"n={n}: #coupled denom factors={len(facs)}")
    for s,e in sorted(facs): print("   ",s,"^",e)
