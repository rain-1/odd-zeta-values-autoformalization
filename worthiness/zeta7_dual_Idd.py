#!/usr/bin/env python3
"""Match I''_n (form in 1,z3,z5, NO z7) to a single Zudilin-type series.
BZ: I''_n = A_n*9 z5 - B_n*2 z3 + D_n.
 n=1: 549 z5 - 600 z3 + 152      (A1=61,B1=300,D1=152)
 n=2: 476289 z5 - 522306 z3 + 535857/4   (A2=52921,B2=261153,D2=535857/4)
Within-n ratios (single series, normalization-free): r3=z3/z5, rc=const/z5."""
from fractions import Fraction as F
import sys
sys.path.insert(0,'/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from zn_check import linear_form_coeffs

# targets
def tgt(n):
    if n==1: cz5,cz3,c=F(549),F(-600),F(152)
    if n==2: cz5,cz3,c=F(476289),F(-522306),F(535857,4)
    return cz3/cz5, c/cz5
print("I'' target ratios (r3=z3/z5, rc=const/z5): n=1",tgt(1)," n=2",tgt(2))

def S(n, M, L, A, B, C, tilde):
    a=0 if tilde else 1
    num=[]
    for _ in range(B):
        for j in range(a,L+1): num.append(F(-j))
    for _ in range(B):
        for j in range(a,L+1): num.append(F(M+j))
    den=[]
    for _ in range(A):
        for j in range(M+1): den.append(j)
    As,c=linear_form_coeffs(F(1),F(M,2),num,den,C)
    return {s:As.get(s,F(0)) for s in range(1,12)}, c

def only35(d):
    for s in range(1,12):
        if s in (3,5): continue
        if d.get(s,F(0))!=0: return False
    return d.get(5,F(0))!=0

hits=[]
for Mm in (1,2):
 for Lm in (1,2,3):
  for A in (4,6,8):
   for B in (1,2,3):
    for C in (0,1,2):
      try:
        d1,c1=S(1,Mm,Lm,A,B,C,False)
      except Exception: continue
      if not only35(d1): continue
      z3,z5=d1[3],d1[5]
      if z5==0: continue
      r3=z3/z5; rc=c1/z5
      tag=f"M={Mm}n L={Lm}n A={A} B={B} C={C}"
      if (r3,rc)==tgt(1):
        d2,c2=S(2,Mm*2,Lm*2,A,B,C,False)
        m2 = only35(d2) and d2[5]!=0 and (d2[3]/d2[5], c2/d2[5])==tgt(2)
        print(f"*** MATCH n=1 {tag}  n=2match={m2}")
        hits.append((tag,m2))
      elif r3==tgt(1)[0]:
        print(f"  r3-only {tag} rc={rc}")
print("hits:",hits)
# also try tilde variants
print("\n-- tilde variants --")
for Mm in (1,2):
 for Lm in (1,2,3):
  for A in (4,6,8):
   for B in (1,2,3):
    for C in (0,1,2):
      try:
        d1,c1=S(1,Mm,Lm,A,B,C,True)
      except Exception: continue
      if not only35(d1) or d1[5]==0: continue
      if (d1[3]/d1[5], c1/d1[5])==tgt(1):
        print(f"*** tilde MATCH n=1 M={Mm}n L={Lm}n A={A} B={B} C={C}")
