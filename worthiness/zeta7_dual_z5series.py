#!/usr/bin/env python3
"""Reconstruct the symmetric zeta(5) VWP series I'_n = Q_n zeta5 - P_n (pure {1,zeta5}).
Q_n=1,21,2989 ; P_n=0,87/4,1190161/384.  within-n ratio const/z5 = -P_n/Q_n.
Scan Zudilin/Rivoal-type summands: pref*(k+shift)*(k-rn)_{rn}^B (k+n+1)_{rn}^B / (k)_{n+1}^A ,
operator (1/C!)d^C. Filter: only zeta5 present, ratio matches at n=1,2."""
from fractions import Fraction as F
import sys
sys.path.insert(0,'/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from zn_check import linear_form_coeffs

Q={0:1,1:21,2:2989}; P={0:F(0),1:F(87,4),2:F(1190161,384)}
def ratio(n): return -P[n]/Q[n] if Q[n] else F(0)

def build(n, A, B, r, shift):
    # num: (k-rn)_{rn}^B  and (k+n+1)_{rn}^B ; den: (k)_{n+1}^A
    num=[]
    for _ in range(B):
        for i in range(r*n): num.append(F(-r*n+i))          # (k-rn)_{rn}
    for _ in range(B):
        for i in range(r*n): num.append(F(n+1+i))           # (k+n+1)_{rn}
    den=[]
    for _ in range(A):
        for i in range(n+1): den.append(i)                   # (k)_{n+1}
    return num,den

def scan():
    tgt1=ratio(1); tgt2=ratio(2)
    print("target ratios const/z5: n=1",tgt1," n=2",tgt2)
    for A in range(4,8):
        for B in range(1,4):
            for r in (1,2):
                for shiftname,shiftfn in [("n/2",lambda n:F(n,2)),("(n+1)/2",lambda n:F(n+1,2)),
                                          ("0",lambda n:F(0)),("n",lambda n:F(n)),
                                          ("rn/2",lambda n:F(r*n,2))]:
                    for C in range(0,3):
                        ok=True; ratios={}
                        pure=True
                        for n in (1,2):
                            num,den=build(n,A,B,r,shiftfn(n))
                            try:
                                As,const=linear_form_coeffs(F(1),shiftfn(n),num,den,C)
                            except Exception:
                                ok=False;break
                            z5=As.get(5,F(0))
                            others={s:As[s] for s in As if s!=5 and As[s]!=0}
                            if z5==0 or others:
                                pure=False;break
                            ratios[n]=const/z5
                        if not pure or not ok: continue
                        if ratios.get(1)==tgt1 and ratios.get(2)==tgt2:
                            print(f"*** MATCH A={A} B={B} r={r} shift={shiftname} C={C}  ratios={ratios}")
                        elif ratios.get(1)==tgt1:
                            print(f"  partial n=1 A={A} B={B} r={r} shift={shiftname} C={C} r2={ratios.get(2)}")

scan()
