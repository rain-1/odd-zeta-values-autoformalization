import sympy as sp
from math import comb, gcd, factorial
s = sp.symbols('s')
def H(m): return sum(sp.Rational(1,i) for i in range(1,m+1))
def d_lcm(N):
    r=1
    for k in range(2,N+1): r=r*k//gcd(r,k)
    return r

def verify_closed(n):
    num = sp.prod([s+i for i in range(1,n+1)])
    den = sp.prod([(s+j)**2 for j in range(n+1,2*n+2)])
    r = num/den
    ok=True
    for j in range(n+1,2*n+2):
        a = j-(n+1)
        g = sp.cancel((s+j)**2*r)
        Bj_true = sp.Rational(g.subs(s,-j))
        Aj_true = sp.Rational(sp.diff(g,s).subs(s,-j))
        Bj_form = sp.Integer((-1)**n)*comb(n+a,a)*comb(n,a)**2/sp.Integer(factorial(n))
        Aj_form = Bj_form*(3*H(a)-H(n+a)-2*H(n-a))
        if sp.nsimplify(Bj_true-Bj_form)!=0 or sp.simplify(Aj_true-Aj_form)!=0:
            ok=False; print(f"  MISMATCH n={n} j={j}: B {Bj_true} vs {Bj_form}, A {Aj_true} vs {Aj_form}")
    return ok

for n in range(1,7):
    print(f"n={n}: closed forms verified = {verify_closed(n)}")
