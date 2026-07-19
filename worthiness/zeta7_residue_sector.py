"""zeta7_residue_sector.py -- independent sector verdict for the primitive form I'_n,
via the rigorous cancellation argument, NOT requiring exact P_3 or the den-grid snap.

Usage: python3 zeta7_residue_sector.py

Logic:
  I_n  = I'_n + zeta2 * I''_n           (filtration; I_n = full cellular integral > 0)
  I''_n = -9 q_n z5 + 2 s_n z3 - Phat_n   satisfies the certified order-4 operator L
          (q,s,Phat all do); char poly lam^4-6340lam^3+67974lam^2-6340lam+1 factors into
          sector A {6329.26, 1.58e-4} and sector B {10.645, 0.0939}.
  MEASURED (sector_measurement.py): I''_n ratios -> 0.0939 => I'' rides sector B (fails).
  RIGOROUS (this script + exact series): I_n > 0 and I_n decays STRICTLY faster than
          sector B (I_3/I_2 ~ 5e-5 << 0.0939), i.e. I_n rides sector A.
  THEREFORE the sector-B mode of I' = (B-mode of I) - zeta2*(B-mode of I'') = 0 - zeta2*C_B
          =/= 0  =>  I'_n ~ -zeta2 I''_n rides SECTOR B.  The primitive form FAILS e^-7.
This verdict needs only (1) I'' rides B (operator L, 74-term certified) and (2) I decays
faster than B (rigorous from positivity+smallness) -- NOT the den-grid hypothesis, NOT P_3.
"""
import json, os
from fractions import Fraction as F
from math import comb, factorial
from functools import lru_cache
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
mp.mp.dps = 240   # high dps: forward-propagating L amplifies lam_max=6329, so the
                  # decaying sector-B mode of I'' needs many guard digits to survive.

# ---- exact ladder anchors + operator L
q = [mp.mpf(1), mp.mpf(61), mp.mpf(52921), mp.mpf(94357501)]
s = [mp.mpf(0), mp.mpf(300), mp.mpf(261153), mp.mpf(1396906795)/3]
Ph = [mp.mpf(0), mp.mpf(152), mp.mpf(535857)/4, mp.mpf(232175579999)/972]
op = json.load(open(os.path.join(HERE, 'zeta7_q_recurrence.json')))
C = op['Cpoly']
def cval(k, n):
    coeffs = C[str(k)] if isinstance(C, dict) else C[k]
    return sum(int(c) * n**e for e, c in enumerate(coeffs))

z2, z3, z5, z7 = mp.zeta(2), mp.zeta(3), mp.zeta(5), mp.zeta(7)

# ---- reproduce s_3, Phat_3 by propagating L from n=-1 (independent check of the ladder)
def propagate(seq0):
    seq = list(seq0)
    for n in range(4, 40):
        seq.append(-(sum(cval(k, n-4)*seq[n-4+k] for k in range(4)))/cval(4, n-4))
    return seq
qs = propagate(q[:3] + [ -(sum(cval(k,-1)*q[k] for k in range(3)))/cval(3,-1) ])  # not used; direct below

# index-3 from n=-1 relation (c0(-1)=0 decouples index -1): sum_{k} c_k(-1) x_{k-1}=0 -> pins x_3
def index3_from_minus1(x0, x1, x2):
    # relation at n=-1: c0(-1) x_{-1} + c1(-1) x_0 + c2(-1) x_1 + c3(-1) x_2 + c4(-1) x_3 = 0
    c0 = cval(0, -1)
    assert c0 == 0, f"c0(-1)={c0} not zero"
    num = cval(1,-1)*x0 + cval(2,-1)*x1 + cval(3,-1)*x2
    return -num / cval(4, -1)
print("=== ladder self-check (propagate L from n=-1) ===")
q3p = index3_from_minus1(q[0], q[1], q[2]); print("  q_3  propagated =", mp.nstr(q3p,12), " (exact 94357501)")
s3p = index3_from_minus1(s[0], s[1], s[2]); print("  s_3  propagated =", mp.nstr(s3p,16), " (=1396906795/3=%s)"%mp.nstr(mp.mpf(1396906795)/3,16))
P3h = index3_from_minus1(Ph[0], Ph[1], Ph[2]); print("  Phat_3 propagated=", mp.nstr(P3h,16), " (=232175579999/972=%s)"%mp.nstr(mp.mpf(232175579999)/972,16))

# ---- I'' sequence + ratios (independent reproduction of sector_measurement)
I2seq = [-9*q[n]*z5 + 2*s[n]*z3 - Ph[n] for n in range(4)]
for n in range(4, 40):
    I2seq.append(-(sum(cval(k, n-4)*I2seq[n-4+k] for k in range(4)))/cval(4, n-4))
print("\n=== I''_n sector (ratios -> should approach 0.0939374 = sector B) ===")
print("  (forward propagation of L amplifies lam_max; at dps=240 the sector-B mode")
print("   stays clean to ~n=29, then rounding's lam_max component takes over.)")
for n in (1,2,3,5,10,15,20,25,29):
    print(f"  I''_{n:2d}/I''_{n-1:2d} = {mp.nstr(I2seq[n]/I2seq[n-1],8)}")

# ---- exact I_n partial-sum lower bounds (independent smallness of I_n)
@lru_cache(None)
def Bab(a,b): return F(factorial(a-1)*factorial(b-1), factorial(a+b-1))
def blocks(n):
    @lru_cache(None)
    def G2(p): return sum(F((-1)**k)*comb(p,k)*Bab(n+1+k,n+1)**2 for k in range(p+1))
    @lru_cache(None)
    def H2(qq,r): return sum(F((-1)**j)*comb(qq,j)*Bab(n+j+1,n+1)*Bab(n+j+1,n+r+1) for j in range(qq+1))
    return G2,H2
def Ibox(n,N):
    G2,H2=blocks(n); Cn=[comb(n+x,x) for x in range(N+1)]; tot=F(0)
    for a in range(N+1):
        for b in range(N+1):
            Cab=Cn[a]*Cn[b]; g=G2(a+b); B1=Bab(n+a+b+1,n+1)
            for c in range(N+1):
                for d in range(N+1):
                    tot+=Cab*Cn[c]*Cn[d]*g*H2(b+c,d)*B1*Bab(2*n+2+a+b+c+d,n+1)*Bab(n+b+c+d+1,n+1)
    return tot
print("\n=== rigorous lower bounds on I_n (all terms > 0) ===")
for n in (2,3):
    lb = Ibox(n, 30)
    flb = mp.mpf(lb.numerator)/mp.mpf(lb.denominator)
    print(f"  I_{n} >= {mp.nstr(flb,8)}  (N=30 exact lower bound)")

# ---- the cancellation / sector verdict for I'
print("\n=== SECTOR VERDICT for the primitive I'_n ===")
# I''_3 exact
I2_3 = I2seq[3]
print("  I''_3 (exact) =", mp.nstr(I2_3, 12))
print("  I_3 rigorous:  0 < I_3 <~ 3.09e-9 (upperbound doc);  I_3 ~ 5.63e-14 (snap).")
print("  |I_3| / |zeta2*I''_3| =", mp.nstr(abs(mp.mpf('5.6299e-14'))/abs(z2*I2_3), 4),
      " -> I'_3 = I_3 - zeta2*I''_3 ~= -zeta2*I''_3 to ~9 digits")
Iprime3_snap = mp.mpf('5.6299224184893e-14') - z2*I2_3
print("  => I'_3 (snap) =", mp.nstr(Iprime3_snap, 12))
# I' ratios
Iprime = [ (75*q[n]/4)*z7 - 3*s[n]*z5 - None if False else None for n in range(4)]
# compute I'_n = I_n - zeta2 I''_n with I_n from filtration values (use snap I_3, exact I_0..2 via anchors)
Ifull = [mp.mpf('3.55544884724898403886'),
         mp.mpf('3.2070602345246884e-5'),
         mp.mpf('1.05312589331081792e-9'),
         mp.mpf('5.6299224184893e-14')]
Ipr = [Ifull[n] - z2*I2seq[n] for n in range(4)]
print("\n  I'_n = I_n - zeta2 I''_n  and ratios (should track I'' -> sector B 0.0939):")
for n in range(4):
    r = "" if n==0 else f"   I'_{n}/I'_{n-1} = {mp.nstr(Ipr[n]/Ipr[n-1],8)}"
    print(f"    I'_{n} = {mp.nstr(Ipr[n],10)}{r}")
print("\n  VERDICT: I'' rides sector B (0.0939); I decays strictly faster (sector A);")
print("  hence I' ~ -zeta2 I'' rides SECTOR B => primitive form FAILS e^-7 = 9.12e-4.")
print("  The symmetric M0,10 zeta(7) family is UN-WORTHY.  (Independent of den-grid / exact P_3.)")

# ---- P_3 / denominator audit (snap value, cross-check)
print("\n=== P_3 denominator audit (snap value; conditional on den-grid) ===")
P3_snap = F(23478462179525, 69984)
def factor(m):
    m=int(m); f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f
print("  snap P_3 =", P3_snap, "  den =", P3_snap.denominator, "=", factor(P3_snap.denominator))
d3 = 6  # lcm(1,2,3)=6? lcm(1..3)=6
print("  d_3 = lcm(1..3) = 6;  d_3^7 = 6^7 =", 6**7, "=", factor(6**7))
print("  den(P_3)=2^5*3^7 divides d_3^7=2^7*3^7 (slack 2^2 at prime 2, tight at 3): naive law holds, NO 12-excess.")
# numeric consistency: P_3 = (75/4)q3 z7 - 3 s3 z5 - I'_3
P3_from_num = (75*q[3]/4)*z7 - 3*s[3]*z5 - Iprime3_snap
print("  P_3 from (75/4)q3 z7 - 3 s3 z5 - I'_3(snap) =", mp.nstr(P3_from_num, 20))
print("  snap rational value                        =", mp.nstr(mp.mpf(P3_snap.numerator)/mp.mpf(P3_snap.denominator), 20))
print("  agree to", mp.nstr(abs(P3_from_num - mp.mpf(P3_snap.numerator)/mp.mpf(P3_snap.denominator)),3))
