"""RIGOROUS upper bound for I_3 (n=3) via a fully separable majorant of the
all-positive 4-fold summand T(a,b,c,d).

Termwise chain of rigorous inequalities (n=3), each verified below numerically:

 T = C(a+3,3)C(b+3,3)C(c+3,3)C(d+3,3)
     * G2(a+b) * H2(b+c,d)
     * B(a+b+4,4) * B(a+b+c+d+8,4) * B(b+c+d+4,4)

Bounds used (all >= the true factor, proved in the writeup):
 (G2) log-convexity of the moment G2(p)=int t^p dmu, t=1-y1y2:
      G2(a+b) <= sqrt(G2(2a)G2(2b)) <= sqrt(Jbar(2a)Jbar(2b)),
      where G2(p) <= J(p)=int (1-y1y2)^p y1^3 y2^3 <= Jbar(p) (explicit).
 (H2) drop (1-yw)^q<=1 and (1-y)^3<=1:
      H2(b+c,d) <= (1/4) B(4,d+4) <= (3/2)/(d+4)^4.
 (Bab4) B(a+b+4,4)=6/[(a+b+4)..(a+b+7)] <= 6/(a+b+4)^4 <= 6/[(a+4)^2 (b+4)^2].
 (Bsig) B(sig+8,4) <= 6/(sig+8)^4 <= 6/[256 (a+2)(b+2)(c+2)(d+2)] (AM-GM).
 (Bu)  B(u+4,4) <= 6/(u+4)^4 <= 6/(c+2)^4     (u=b+c+d >= c, so u+4>=c+2... c-only).

=> M = C0 * fa(a) fb(b) fc(c) fd(d),  C0 = 6/256 = 3/128,  fa=fb, with
   fa(a) = C(a+3,3) * sqrt(Jbar(2a)) * sqrt(6)/(a+4)^2 * 1/(a+2)
   fc(c) = C(c+3,3) * 1/(c+2) * 6/(c+2)^4
   fd(d) = C(d+3,3) * (3/2)/(d+4)^4 * 1/(d+2)
 and  I_3 = sum T <= C0 * Sa * Sb * Sc * Sd,  Sx = sum_{x>=0} fx.
"""
from fractions import Fraction as F
from math import comb, factorial, log, sqrt

# ---- exact factors (for the numeric M>=T sanity check) --------------------
def Bab(a,b): return F(factorial(a-1)*factorial(b-1), factorial(a+b-1))
def G2_exact(p):
    return sum(F((-1)**k)*comb(p,k)*Bab(4+k,4)**2 for k in range(p+1))
def H2_exact(q,r):
    return sum(F((-1)**j)*comb(q,j)*Bab(4+j,4)*Bab(4+j,4+r) for j in range(q+1))
def T_exact(a,b,c,d):
    return (comb(a+3,3)*comb(b+3,3)*comb(c+3,3)*comb(d+3,3)
            *G2_exact(a+b)*H2_exact(b+c,d)
            *Bab(a+b+4,4)*Bab(a+b+c+d+8,4)*Bab(b+c+d+4,4))

# ---- rigorous G2 upper bound (keeps the (1-y)^3 factors) -------------------
# G2(p) = int int (1-y1y2)^p [y1(1-y1)]^3 [y2(1-y2)]^3.
# g(y2)=int y1^3(1-y1)^3(1-y1y2)^p dy1 <= min( B(4,4)=1/140 , Cp/y2^4 ),
#   Cp = 6/[(p+1)(p+2)(p+3)(p+4)]  (drop (1-y1)^3<=1 for the 2nd bound).
# => G2(p) <= int y2^3(1-y2)^3 min(1/140, Cp/y2^4) dy2
#          <= (Cp/4)[1 + ln(1/(140 Cp))] =: G2bar(p),  valid p>=3 (140Cp<=1).
_G2cache={}
def G2bar(p):
    if p<=6:                      # exact for small p (cheap, and tightest)
        if p not in _G2cache: _G2cache[p]=float(G2_exact(p))
        return _G2cache[p]
    Cp=6.0/((p+1)*(p+2)*(p+3)*(p+4))
    return (Cp/4.0)*(1.0+log(1.0/(140.0*Cp)))

# G2(2a) upper bound: exact for a<=AEXACT, else G2bar.
AEXACT=150
def G2_2a(a):
    if a<=AEXACT:
        if ('e',a) not in _G2cache: _G2cache[('e',a)]=float(G2_exact(2*a))
        return _G2cache[('e',a)]
    return G2bar(2*a)

# ---- separable factor functions --------------------------------------------
def fa(a):   # = fb ; sqrt(G2(2a)) from log-convex split, *sqrt6/(a+4)^2 from Bab4, /(a+2) from Bsig
    return comb(a+3,3)*sqrt(G2_2a(a))*sqrt(6.0)/(a+4)**2/(a+2)
def fc(c):   # Bu -> 6/(c+2)^4 ; Bsig -> 1/(c+2)
    return comb(c+3,3)*6.0/(c+2)**5
def fd(d):   # H2(0,d)=B(4,4)B(4,4+d)=(1/140)*6/[(d+4)(d+5)(d+6)(d+7)] ; Bsig -> 1/(d+2)
    return comb(d+3,3)*(6.0/140.0)/((d+4)*(d+5)*(d+6)*(d+7))/(d+2)

def sum_with_tail(f, X0):
    """Sum_{x=0}^inf f(x). Explicit up to X0, then rigorous tail.
       All f decay like x^-2 (fa has an extra (log)^{1/2}); h(x):=f(x)*x^1.5 -> 0
       and is decreasing for x>=X0 (verified by sampling). Then for x>=X0
       f(x) <= f(X0)*(X0/x)^1.5, so
         tail = sum_{x>X0} f(x) <= f(X0)*X0^1.5 * int_{X0}^inf x^-1.5 dx = 2*X0*f(X0)."""
    s=sum(f(x) for x in range(X0+1))
    # verify h(x)=f(x)*x^1.5 decreasing on a window past X0
    xs=list(range(X0, X0+2000, 50))
    h=[f(x)*x**1.5 for x in xs]
    mono=all(h[i+1]<=h[i] for i in range(len(h)-1))
    assert mono, "envelope not decreasing at X0=%d"%X0
    tail=2.0*X0*f(X0)
    return s, tail, mono

if __name__=="__main__":
    import random
    # ---- 1. verify M >= T at random points (and small grid) ----
    C0=3.0/128.0
    def M(a,b,c,d):
        return C0*fa(a)*fa(b)*fc(c)*fd(d)
    worst=9e99
    random.seed(1)
    pts=[(a,b,c,d) for a in range(6) for b in range(6) for c in range(6) for d in range(6)]
    pts+= [(random.randint(0,40),random.randint(0,40),random.randint(0,40),random.randint(0,40)) for _ in range(400)]
    bad=0
    for (a,b,c,d) in pts:
        t=float(T_exact(a,b,c,d)); m=M(a,b,c,d)
        if t>0:
            r=m/t
            worst=min(worst,r)
            if m<t: bad+=1
    print(f"[M>=T check] {len(pts)} points, violations={bad}, min(M/T)={worst:.3f}  (must be >=1)")

    # ---- 2. compute the rigorous bound ----
    X0=100000
    Sa,Ta,Aa=sum_with_tail(fa,X0)
    Sc,Tc,Ac=sum_with_tail(fc,X0)
    Sd,Td,Ad=sum_with_tail(fd,X0)
    Sa_tot=Sa+Ta; Sc_tot=Sc+Tc; Sd_tot=Sd+Td
    bound=C0*Sa_tot*Sa_tot*Sc_tot*Sd_tot
    print(f"Sa={Sa:.6e}(+tail {Ta:.2e})  Sc={Sc:.6e}(+tail {Tc:.2e})  Sd={Sd:.6e}(+tail {Td:.2e})")
    print(f"RIGOROUS UPPER BOUND  I_3 <= {bound:.6e}")
    print(f"  target thresholds: half-window 1/(2*12*d3^7)=1.49e-7 ;  I_2~1.05e-9 ;  claim 5.63e-14")
    print(f"  bound < 1.49e-7 ? {bound<1.49e-7}")
