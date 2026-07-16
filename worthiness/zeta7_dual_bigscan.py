#!/usr/bin/env python3
"""Broad VWP scan for the BZ zeta(7) family I'_n (form in 1,z5,z7).
Base series S(n) = pref*(k+shift) * [num blocks]^B / [den]^A , operator (1/C!)d^C.
Companion ~S via tilde (j=0 vs j=1). Kill z3 in the combination, test within-n
ratios r5=z5/z7, rc=const/z7 against BZ targets at n=1 (then n=2).
BZ targets: n=1 (-48/61, -176/915); n=2 (-1044612/1323025, -2007073/10584200)."""
from fractions import Fraction as F
from math import factorial
import sys
sys.path.insert(0,'/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from zn_check import linear_form_coeffs

T5={1:F(-48,61),2:F(-1044612,1323025)}
Tc={1:F(-176,915),2:F(-2007073,10584200)}

def S(n, A, B, C, shift, tilde, numlen_mult):
    a=0 if tilde else 1
    L=numlen_mult*n
    num=[]
    for _ in range(B):
        for j in range(a, L+1): num.append(F(-j))         # (k-j), j=a..L
    for _ in range(B):
        for j in range(a, L+1): num.append(F(n+j))        # (k+n+j)
    den=[]
    for _ in range(A):
        for j in range(n+1): den.append(j)                # (k+j)^A
    pref=F(1)
    As,const=linear_form_coeffs(pref, shift, num, den, C)
    return {s:As.get(s,F(0)) for s in range(1,12)}, const

def zetas_ok_top7(d):
    # require top nonzero zeta is 7 and no even, no z9+, so combo lives in {z3,z5,z7}
    if d.get(9,F(0))!=0 or d.get(11,F(0))!=0: return False
    for s in (2,4,6,8,10):
        if d.get(s,F(0))!=0: return False
    if d.get(7,F(0))==0: return False
    return True

hits=[]
shifts={"n/2":lambda n:F(n,2)}
for A in (6,8,10):
  for B in (1,2,3):
    for C in (0,1,2):
      for sn,sf in shifts.items():
        for nlm in (1,2):
          # quick n=1 test
          try:
            d1,c1=S(1,A,B,C,sf(1),False,nlm); dt1,ct1=S(1,A,B,C,sf(1),True,nlm)
          except Exception: continue
          if not (zetas_ok_top7(d1) and zetas_ok_top7(dt1)): continue
          w=d1[3]; wt=dt1[3]
          Lz5=wt*d1[5]-w*dt1[5]; Lz7=wt*d1[7]-w*dt1[7]; Lz3=wt*d1[3]-w*dt1[3]
          Lc=wt*c1-w*ct1
          if Lz7==0 or Lz3!=0: continue
          r5=Lz5/Lz7; rc=Lc/Lz7
          tag=f"A={A} B={B} C={C} shift={sn} numlen={nlm}n"
          if r5==T5[1] and rc==Tc[1]:
            # confirm n=2
            d2,c2=S(2,A,B,C,sf(2),False,nlm); dt2,ct2=S(2,A,B,C,sf(2),True,nlm)
            w2=d2[3]; wt2=dt2[3]
            L2z5=wt2*d2[5]-w2*dt2[5]; L2z7=wt2*d2[7]-w2*dt2[7]; L2c=wt2*c2-w2*ct2
            m2=(L2z5/L2z7==T5[2] and L2c/L2z7==Tc[2])
            print(f"*** n=1 MATCH {tag}  n=2match={m2}  (r5={r5},rc={rc})")
            hits.append(tag)
          elif r5==T5[1]:
            print(f"  r5-only {tag} rc={rc}")
print("hits:",hits)
