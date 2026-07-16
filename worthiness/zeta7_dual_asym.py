#!/usr/bin/env python3
"""Systematic ASYMMETRIC / spread-pole VWP scan for BZ I'_n (form in 1,z5,z7).
Family (compute_Zn-style, small parameters):
  num = (k - P n)_{P n}^B (k + Q n + 1)_{P n}^B          (well-poised pair)
  den = prod_{u=1}^{U} (k + (M-u) n)_{(base + step*u) n + 1}   (staircase spread)
  half-shift = Q n / 2 ,  operator (1/C!) d^C ,  C in {0,2}
Engine reports zeta content + ratios. We LOG: (a) any config giving z5/z7 < 0
(the BZ sign, the key discriminator), (b) exact ratio matches to BZ I'_n.
BZ targets: n=1 (r5=-48/61, rc=-176/915); n=2 (-1044612/1323025, -2007073/10584200)."""
from fractions import Fraction as F
from math import factorial
import sys
sys.path.insert(0,'/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from zn_check import linear_form_coeffs

T5={1:F(-48,61),2:F(-1044612,1323025)}
Tc={1:F(-176,915),2:F(-2007073,10584200)}

def build(n, P, Q, B, U, M, base, step, C):
    num=[]
    for _ in range(B):
        for i in range(P*n): num.append(F(-P*n+i))       # (k-Pn)_{Pn}
    for _ in range(B):
        for i in range(P*n): num.append(F(Q*n+1+i))       # (k+Qn+1)_{Pn}
    den=[]
    for u in range(1,U+1):
        off=(M-u)*n
        length=(base+step*u)*n+1
        if length<=0: return None
        for i in range(length): den.append(off+i)
    # convergence: den-deg - num-deg(incl shift) >= 2
    ndeg = 1 + 2*B*P*n
    ddeg = sum((base+step*u)*n+1 for u in range(1,U+1))
    if ddeg - ndeg < 2: return None
    pref=F(factorial(n))**0   # normalization irrelevant for ratios; keep 1
    try:
        As,const=linear_form_coeffs(pref, F(Q*n,2), num, den, C)
    except Exception:
        return None
    return {s:As.get(s,F(0)) for s in range(1,14)}, const

neg_r5_hits=[]
exact_hits=[]
checked=0
# bounded grid
for C in (2,0):
 for B in (1,2,3):
  for P in (1,2,3):
   for Q in range(P, 3*P+1):          # Q>=P so blocks separate
    for U in (2,3,4,5):
     for M in range(1, 8):
      for base in range(0,3):
       for step in (1,2):
        # quick n=1
        res=build(1,P,Q,B,U,M,base,step,C)
        if res is None: continue
        d1,c1=res
        checked+=1
        # require top zeta 7, and content within {3,5,7} (no 9+,no even)
        if d1.get(9,F(0))!=0 or any(d1.get(s,F(0))!=0 for s in (11,13)): continue
        if any(d1.get(s,F(0))!=0 for s in (2,4,6,8,10,12)): continue
        z5,z7=d1.get(5,F(0)),d1.get(7,F(0))
        if z7==0 or z5==0: continue
        r5=z5/z7; rc=c1/z7
        tag=f"C={C} B={B} P={P} Q={Q} U={U} M={M} base={base} step={step} z3={'y' if d1.get(3,F(0))!=0 else 'n'}"
        if r5<0:
            neg_r5_hits.append((tag,r5,rc))
        if r5==T5[1] and rc==Tc[1] and d1.get(3,F(0))==0:
            res2=build(2,P,Q,B,U,M,base,step,C)
            m2=False
            if res2:
                d2,c2=res2
                if d2.get(7,F(0))!=0:
                    m2=(d2.get(5,F(0))/d2[7]==T5[2] and c2/d2[7]==Tc[2] and d2.get(3,F(0))==0)
            exact_hits.append((tag,m2))
            print(f"*** EXACT n=1 {tag}  n=2match={m2}")

print(f"\nchecked={checked}")
print(f"configs with NEGATIVE r5 (BZ sign): {len(neg_r5_hits)}")
for t,r5,rc in neg_r5_hits[:20]:
    print(f"   r5={r5} rc={rc}  |  {t}")
print(f"exact hits: {exact_hits}")
