#!/usr/bin/env python3
# Parse the CT recurrence from zeta7_ct_lc.log (COEF c_k(n) lines, Mathematica InputForm),
# certify against all exact q_n (zeta7_lc_terms.txt), extract char poly/roots, save recurrence.json.
import re, os, json, sys
import sympy as sp

HERE=os.path.dirname(os.path.abspath(__file__))
LOG=os.path.join(HERE, sys.argv[1] if len(sys.argv)>1 else 'zeta7_ct_lc.log')
n=sp.symbols('n')
coefs={}
for line in open(LOG):
    m=re.match(r'COEF c_(\d+)\(n\) = (.+)', line.strip())
    if m:
        k=int(m.group(1)); expr=m.group(2)
        expr=expr.replace('nn','n').replace('^','**')
        coefs[k]=sp.expand(sp.sympify(expr))
if not coefs:
    print("no COEF lines found in", LOG); sys.exit(1)
order=max(coefs)
Cpoly=[]
deg=0
for k in range(order+1):
    p=sp.Poly(coefs.get(k,sp.Integer(0)), n)
    cl=[int(c) for c in reversed(p.all_coeffs())]  # a0..adeg
    Cpoly.append(cl); deg=max(deg,len(cl)-1)
# pad
for k in range(order+1):
    while len(Cpoly[k])<deg+1: Cpoly[k].append(0)
print(f"parsed CT recurrence: order {order}, degree {deg}")

# load exact q_n
seq={}
for l in open(os.path.join(HERE,'..','zeta7_lc_terms.txt')):
    m=re.match(r'q_(\d+)\s*=\s*(\d+)', l.strip())
    if m: seq[int(m.group(1))]=int(m.group(2))
N=0
while N in seq: N+=1
ex=[seq[i] for i in range(N)]
print("exact terms for cert:", len(ex))

def cval(pc,nn): return sum(pc[j]*nn**j for j in range(len(pc)))
ok=True; tested=0
for m in range(len(ex)-order):
    s=sum(cval(Cpoly[k],m)*ex[m+k] for k in range(order+1))
    tested+=1
    if s!=0: ok=False; print("CERT FAIL at n=",m); break
print(f"CERTIFY vs {tested} exact terms:", "ALL ZERO" if ok else "FAILED")
lead=[Cpoly[k][deg] for k in range(order+1)]
print("char poly coeffs (lambda^0..order):", lead)
import numpy as np
roots=sorted(np.roots(lead[::-1]), key=lambda z:-abs(z))
for z in roots: print(f"  root {z.real:+.6e}{z.imag:+.3e}i |.|={abs(z):.6e}")
json.dump({'order':order,'deg':deg,'Cpoly':Cpoly,'certified':ok,'ntested':tested,'char_lead':lead},
          open(os.path.join(HERE,'recurrence.json'),'w'), indent=1)
print("[saved recurrence.json]")
