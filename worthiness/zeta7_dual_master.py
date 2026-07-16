#!/usr/bin/env python3
"""KR master family S_{n,A,B,C,r}(z=(-1)^A) [KR math/0311114 eq.782].
For A even: linear form in 1, zeta(C+3), zeta(C+5),...,zeta(C+A-1).
=> A=6, C=2  gives {1, zeta5, zeta7} = I'_n structure (NO zeta3).
Summand R = n!^{A-2Br}(k+n/2)(k-rn)_{rn}^B (k+n+1)_{rn}^B/(k)_{n+1}^A, operator (1/C!)d^C.
Test RAW within-n ratios r5=z5/z7, rc=const/z7 vs BZ I'_n:
 n=1 (-48/61, -176/915) ; n=2 (-1044612/1323025, -2007073/10584200)."""
from fractions import Fraction as F
from math import factorial
import sys
sys.path.insert(0,'/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from zn_check import linear_form_coeffs

T5={1:F(-48,61),2:F(-1044612,1323025)}
Tc={1:F(-176,915),2:F(-2007073,10584200)}

def S(n, A, B, C, r):
    num=[]
    for _ in range(B):
        for i in range(r*n): num.append(F(-r*n+i))     # (k-rn)_{rn}
    for _ in range(B):
        for i in range(r*n): num.append(F(n+1+i))       # (k+n+1)_{rn}
    den=[]
    for _ in range(A):
        for j in range(n+1): den.append(j)              # (k)_{n+1}^A
    pref=F(factorial(n))**(A-2*B*r)
    As,const=linear_form_coeffs(pref, F(n,2), num, den, C)
    return {s:As.get(s,F(0)) for s in range(1,12)}, const

print("BZ I' targets: n=1",(T5[1],Tc[1]),"  n=2",(T5[2],Tc[2]))
print()
# A=6,C=2 -> {z5,z7}; scan B,r with 2Br<A=6
for A,C in [(6,2)]:
  for B in (1,2):
    for r in (1,2):
      if 2*B*r>=A: continue
      d1,c1=S(1,A,B,C,r)
      nz={s:d1[s] for s in range(1,12) if d1[s]!=0}
      tag=f"A={A} B={B} C={C} r={r}"
      if d1.get(7,F(0))==0:
        print(f"  {tag}: n=1 zetas={nz} const={c1}  (no z7)")
        continue
      r5=d1[5]/d1[7]; rc=c1/d1[7]
      print(f"  {tag}: n=1 z5={d1[5]} z7={d1[7]} const={c1}  r5={r5} rc={rc}")
      if r5==T5[1] and rc==Tc[1]:
        d2,c2=S(2,A,B,C,r)
        m2=(d2.get(7,F(0))!=0 and d2[5]/d2[7]==T5[2] and c2/d2[7]==Tc[2])
        print(f"     *** n=1 MATCH  n=2match={m2}")
