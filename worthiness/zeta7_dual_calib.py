#!/usr/bin/env python3
"""CALIBRATION on zeta(5): the symmetric dual VWP series is  F_7(3n; n^7)
(b-dictionary lines 1249-1251 with a_i=n gives b0=3n, b1..b7=n).
Arithmetic normalization eq-nm (all b_i=b): [(b0-2b)!^6/(b2! b3!)] = n!^6/n!^2 = n!^4.
Check: does its decomposition reproduce Q_n=1,21,2989 (zeta5 coeff)?"""
from fractions import Fraction as F
from math import factorial
import sys
sys.path.insert(0,'/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from zn_check import linear_form_coeffs

def tildeF_general(b0, bs, sign_base):
    k=len(bs)
    num=list(range(0,b0+1))
    den=[]
    for bj in bs:
        den+=list(range(bj, b0-bj+1))
    # sign (-1)^{(k+1)mu}: for k odd, k+1 even -> +1. handle only +1 case here.
    assert (k+1)%2==0, "sign not +1"
    As,const=linear_form_coeffs(F(2), F(b0,2), num, den, C=0)
    return As, const

def calibrate_zeta5():
    print("zeta(5) calibration: F_7(3n; n^7), norm = n!^4")
    Qref={0:1,1:21,2:2989}
    for n in range(0,4):
        b0=3*n; bs=[n]*7
        As,const=tildeF_general(b0,bs,1)
        norm=F(factorial(n))**4
        z3=As.get(3,F(0))*norm; z5=As.get(5,F(0))*norm; z7=As.get(7,F(0))*norm
        c=const*norm
        print(f" n={n}: normalized  const={c}  z3={z3}  z5={z5}  z7={z7}")
        print(f"        Q_n(ref)={Qref.get(n)}   z5/Q_n = {z5/Qref[n] if Qref.get(n) else '-'}")

if __name__=='__main__':
    calibrate_zeta5()
