#!/usr/bin/env python3
"""ZETA(7) identification. Two VWP series (den^8, n!^6):
   rho_n  : num prod_{j=1}^n ;  ~rho_n : num prod_{j=0}^n  (Zudilin-style pair).
Each is a form in 1,z3,z5,z7. Kill z3 via L_n = w~_n*rho_n - w_n*~rho_n  (w=coeff z3).
L_n is then a form in 1,z5,z7. Compare within-n ratios to BZ I'_n:
   I'_n = A_n*(75/4)z7 - 3B_n z5 - C_n
   coeff z7 = (75/4)A_n ; coeff z5 = -3B_n ; const = -C_n
   r5 = coeffz5/coeffz7 ,  rc = const/coeffz7   (normalization independent)."""
from fractions import Fraction as F
from math import factorial, comb
import sys
sys.path.insert(0,'/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from zn_check import linear_form_coeffs

def series(n, den_pow, pref_pow, tilde):
    a = 0 if tilde else 1
    num=[]
    for j in range(a,n+1): num.append(F(-j))
    for j in range(a,n+1): num.append(F(n+j))
    den=[]
    for _ in range(den_pow):
        for j in range(n+1): den.append(j)
    As,const=linear_form_coeffs(F(factorial(n))**pref_pow, F(n,2), num, den, C=0)
    return {s:As.get(s,F(0)) for s in (3,5,7,9)}, const

# BZ anchors
A={0:F(1),1:F(61),2:F(52921)}; B={0:F(0),1:F(300),2:F(261153)}; C={0:F(0),1:F(220),2:F(6021219,32)}
def tgt(n):
    cz7=F(75,4)*A[n]; cz5=-3*B[n]; cc=-C[n]
    return (cz5/cz7, cc/cz7)

print("BZ target ratios (r5=cz5/cz7, rc=const/cz7):")
for n in (1,2): print(f"  n={n}: r5={tgt(n)[0]}  rc={tgt(n)[1]}")
print()

for n in range(0,4):
    (rho,crho) = series(n,8,6,False)
    (rht,crht) = series(n,8,6,True)
    # ~rho has an overall -1 in Zudilin's convention; sign irrelevant for z3-kill combo
    w  = rho[3]; wt = rht[3]
    # L_n = wt*rho - w*~rho  kills z3
    Lz5 = wt*rho[5] - w*rht[5]
    Lz7 = wt*rho[7] - w*rht[7]
    Lz3 = wt*rho[3] - w*rht[3]
    Lc  = wt*crho   - w*crht
    line=f"n={n}: rho(z3,z5,z7)=({rho[3]},{rho[5]},{rho[7]}) ~rho=({rht[3]},{rht[5]},{rht[7]})"
    print(line)
    print(f"     L_n: z3={Lz3} z5={Lz5} z7={Lz7} const={Lc}")
    if Lz7!=0:
        r5=Lz5/Lz7; rc=Lc/Lz7
        print(f"     L ratios: r5={r5}  rc={rc}")
        if n in (1,2):
            t5,tc=tgt(n)
            print(f"     MATCH r5? {r5==t5}   MATCH rc? {rc==tc}")
