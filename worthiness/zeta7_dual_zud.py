#!/usr/bin/env python3
"""Validate engine on Zudilin's exact zeta(5) VWP series (math/0206178 eq 7), then
build the zeta(7) analog by the pattern den-power = weight+1.

Zudilin eq7:  r_n = n!^4 sum_k (k+n/2) prod_{j=1}^n(k-j) prod_{j=1}^n(k+n+j) / prod_{j=0}^n(k+j)^6
  r_0=z5 ; r_1=9z5+33z3-49 ; r_2=469z5+(6125/4)z3-74463/32
  ~r_n = -n!^4 sum_k (k+n/2) prod_{j=0}^n(k-j) prod_{j=0}^n(k+n+j) / prod_{j=0}^n(k+j)^6
  ~r_0=z3 ; ~r_1=2z5+12z3-33/2 ; ~r_2=552z5+1764z3-43085/16
"""
from fractions import Fraction as F
from math import factorial, comb
import sys
sys.path.insert(0,'/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from zn_check import linear_form_coeffs

def series(n, den_pow, pref_fac_pow, tilde=False):
    """(k+n/2)*num/den, prefactor n!^pref_fac_pow.
       num = prod_{j=a}^n (k-j) * prod_{j=a}^n (k+n+j), a=0 if tilde else 1.
       den = prod_{j=0}^n (k+j)^{den_pow}."""
    a = 0 if tilde else 1
    num=[]
    for j in range(a, n+1): num.append(F(-j))       # (k-j)
    for j in range(a, n+1): num.append(F(n+j))      # (k+n+j)
    den=[]
    for _ in range(den_pow):
        for j in range(n+1): den.append(j)          # (k+j)^den_pow
    pref = F(factorial(n))**pref_fac_pow
    As,const = linear_form_coeffs(pref, F(n,2), num, den, C=0)
    return As, const

def show(n, As, const, tag):
    zs={s:As.get(s,F(0)) for s in (2,3,4,5,6,7,8,9)}
    nz={s:v for s,v in zs.items() if v!=0}
    print(f"  {tag} n={n}: const={const}  nonzero zetas={nz}")
    return zs, const

print("=== VALIDATE engine on Zudilin zeta(5) r_n (den^6, n!^4) ===")
exp_r={0:(0,0,1,0),1:(0,33,9,-49),2:(0,F(6125,4),469,F(-74463,32))}  # (z2,z3,z5,-v)... store z3,z5,const
ok=True
for n in (0,1,2):
    As,const=series(n,6,4,tilde=False)
    z3=As.get(3,F(0)); z5=As.get(5,F(0)); z7=As.get(7,F(0))
    e_z3,e_z5,e_c = exp_r[n][1],exp_r[n][2],exp_r[n][3]
    good = (z3==e_z3 and z5==e_z5 and const==e_c and z7==0)
    ok = ok and good
    print(f"  r_{n}: z3={z3}(exp{e_z3}) z5={z5}(exp{e_z5}) z7={z7} const={const}(exp{e_c})  match={good}")
print("  Zudilin r_n VALIDATION:", "PASSED" if ok else "FAILED")

print("\n=== VALIDATE ~r_n (den^6, n!^4, tilde) ===")
exp_rt={0:(0,1,0,0),1:(0,12,2,F(-33,2)),2:(0,1764,552,F(-43085,16))}
okt=True
for n in (0,1,2):
    As,const=series(n,6,4,tilde=True)
    As={s:-v for s,v in As.items()}; const=-const   # tilde has overall minus sign
    z3=As.get(3,F(0)); z5=As.get(5,F(0)); z7=As.get(7,F(0))
    e_z3,e_z5,e_c=exp_rt[n][1],exp_rt[n][2],exp_rt[n][3]
    good=(z3==e_z3 and z5==e_z5 and const==e_c and z7==0)
    okt=okt and good
    print(f"  ~r_{n}: z3={z3}(exp{e_z3}) z5={z5}(exp{e_z5}) z7={z7} const={const}(exp{e_c}) match={good}")
print("  Zudilin ~r_n VALIDATION:", "PASSED" if okt else "FAILED")

print("\n=== zeta(7) ANALOG: rho_n (den^8, n!^6) and ~rho_n ===")
for n in (0,1,2,3):
    As,const=series(n,8,6,tilde=False)
    z3=As.get(3,F(0));z5=As.get(5,F(0));z7=As.get(7,F(0));z9=As.get(9,F(0))
    print(f"  rho_{n}: z3={z3} z5={z5} z7={z7} z9={z9} const={const}")
