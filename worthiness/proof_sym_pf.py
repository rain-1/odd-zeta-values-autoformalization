import sympy as sp
from math import gcd
s = sp.symbols('s')
def d_lcm(N):
    r=1
    for k in range(2,N+1): r=r*k//gcd(r,k)
    return r
def analyze(n):
    num = sp.prod([s+i for i in range(1,n+1)])
    den = sp.prod([(s+j)**2 for j in range(n+1,2*n+2)])
    r = num/den
    dn=d_lcm(n); d2n=d_lcm(2*n)
    res=[]
    maxden=1; maxdenA=1; maxdenB=1
    for j in range(n+1,2*n+2):
        g = sp.cancel((s+j)**2 * r)
        Bj = sp.Rational(g.subs(s,-j))
        Aj = sp.Rational(sp.diff(g,s).subs(s,-j))
        res.append((j,Aj,Bj))
        maxden=sp.ilcm(maxden,Aj.q,Bj.q)
        maxdenA=sp.ilcm(maxdenA,Aj.q); maxdenB=sp.ilcm(maxdenB,Bj.q)
    return dn,d2n,maxden,maxdenA,maxdenB,res
for n in range(1,8):
    dn,d2n,maxden,mA,mB,res = analyze(n)
    print(f"n={n}: d_n={dn} d_2n={d2n} | lcm den(A,B)={maxden}={sp.factorint(maxden)} | denA={sp.factorint(mA)} denB={sp.factorint(mB)}")
    print(f"      d_2n^2={sp.factorint(d2n**2)}  d_n*d_2n={sp.factorint(dn*d2n)} d_2n={sp.factorint(d2n)}")
