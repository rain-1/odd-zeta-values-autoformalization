#!/usr/bin/env python3
"""Generalized VWP scan: den = prod_{j=0}^{M}(k+j)^A (center -M/2, shift M/2),
num = prod_{j=a}^{L}(k-j)^B * prod_{j=a}^{L}(k+M+j)^B  (reflection-symmetric about -M/2).
Companion via a=0 vs a=1 (tilde). Kill z3, test ratios vs BZ I'_n at n=1 then n=2."""
from fractions import Fraction as F
import sys
sys.path.insert(0,'/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from zn_check import linear_form_coeffs

T5={1:F(-48,61),2:F(-1044612,1323025)}
Tc={1:F(-176,915),2:F(-2007073,10584200)}

def S(n, M, L, A, B, C, tilde):
    a=0 if tilde else 1
    num=[]
    for _ in range(B):
        for j in range(a, L+1): num.append(F(-j))
    for _ in range(B):
        for j in range(a, L+1): num.append(F(M+j))
    den=[]
    for _ in range(A):
        for j in range(M+1): den.append(j)
    As,const=linear_form_coeffs(F(1), F(M,2), num, den, C)
    return {s:As.get(s,F(0)) for s in range(1,12)}, const

def top7(d):
    if d.get(9,F(0))!=0 or d.get(11,F(0))!=0: return False
    for s in (2,4,6,8,10):
        if d.get(s,F(0))!=0: return False
    return d.get(7,F(0))!=0

def killz3(d,c,dt,ct):
    w=d[3]; wt=dt[3]
    return (wt*d[5]-w*dt[5], wt*d[7]-w*dt[7], wt*d[3]-w*dt[3], wt*c-w*ct)

hits=[]; checked=0
for Mm in (1,2):        # M = Mm * n
 for Lm in (1,2,3):     # L = Lm * n
  for A in (6,8,10):
   for B in (1,2,3):
    for C in (0,1,2):
      M=Mm*1; L=Lm*1
      try:
        d1,c1=S(1,M,L,A,B,C,False); dt1,ct1=S(1,M,L,A,B,C,True)
      except Exception: continue
      checked+=1
      if not (top7(d1) and top7(dt1)): continue
      z5,z7,z3,cc=killz3(d1,c1,dt1,ct1)
      if z7==0 or z3!=0: continue
      r5=z5/z7; rc=cc/z7
      tag=f"M={Mm}n L={Lm}n A={A} B={B} C={C}"
      if r5==T5[1] and rc==Tc[1]:
        M2,L2=Mm*2,Lm*2
        d2,c2=S(2,M2,L2,A,B,C,False); dt2,ct2=S(2,M2,L2,A,B,C,True)
        z5b,z7b,z3b,ccb=killz3(d2,c2,dt2,ct2)
        m2=(z7b!=0 and z5b/z7b==T5[2] and ccb/z7b==Tc[2])
        print(f"*** MATCH n=1 {tag}  n=2match={m2}")
        hits.append((tag,m2))
      elif r5==T5[1]:
        print(f"  r5-only {tag}  rc={rc}")
      elif abs(r5)<0 or (r5<0):  # note any negative-r5 (correct sign) candidates
        pass
print(f"checked={checked} hits={hits}")
# also: print the sign pattern of a few base series to understand
print("\nsample base decompositions (n=1):")
for (M,L,A,B,C) in [(1,1,8,1,0),(2,2,8,1,0),(1,2,8,1,0),(1,1,8,1,1),(1,1,8,2,0)]:
    try:
        d,c=S(1,M,L,A,B,C,False)
        nz={s:d[s] for s in range(1,12) if d[s]!=0}
        print(f"  M={M}L={L}A={A}B={B}C={C}: z={nz} const={c}")
    except Exception as e:
        print("  err",e)
