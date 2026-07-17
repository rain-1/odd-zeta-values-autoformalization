#!/usr/bin/env python3
# Targeted CRT reconstruction of the order-4, degree-19 operator for q_n.
# Uses all fleet_<prime>.txt with >=105 contiguous terms; normalizes c_4 leading coeff = 1;
# CRT + rational reconstruction; certifies vs exact q_n; char poly + roots; saves recurrence.json.
import os, glob, json, re
from fractions import Fraction
from functools import reduce
from math import gcd, lcm

HERE=os.path.dirname(os.path.abspath(__file__))
ORDER, DEG = 4, 19
NC=(ORDER+1)*(DEG+1)            # 100
NORM_IDX=ORDER*(DEG+1)+DEG      # index of c_4's n^19 coeff = 99

def load(fn,p):
    d={}
    for l in open(fn):
        if '=' in l:
            a,b=l.split('=',1)
            try:
                if b.strip(): d[int(a)]=int(b)%p
            except: pass
    m=-1
    while (m+1) in d: m+=1
    return [d[i] for i in range(m+1)]

def nullvec(seq,p):
    nr=len(seq)-ORDER
    if nr<NC: return None
    M=[]
    for n in range(nr):
        row=[]
        for k in range(ORDER+1):
            b=seq[n+k]%p; nk=1
            for j in range(DEG+1): row.append(nk*b%p); nk=nk*n%p
        M.append(row)
    R=len(M); piv=[]; pr=0
    for col in range(NC):
        pv=next((r for r in range(pr,R) if M[r][col]%p),None)
        if pv is None: continue
        M[pr],M[pv]=M[pv],M[pr]; iv=pow(M[pr][col],p-2,p); M[pr]=[x*iv%p for x in M[pr]]
        for r in range(R):
            if r!=pr and M[r][col]:
                f=M[r][col]; M[r]=[(M[r][c]-f*M[pr][c])%p for c in range(NC)]
        piv.append(col); pr+=1
        if pr==R: break
    free=[c for c in range(NC) if c not in piv]
    if len(free)!=1: return None   # need exactly 1-dim nullspace
    fc=free[0]; vec=[0]*NC; vec[fc]=1
    for i,col in enumerate(piv): vec[col]=(-M[i][fc])%p
    # normalize so component NORM_IDX == 1
    if vec[NORM_IDX]%p==0: return None
    inv=pow(vec[NORM_IDX],p-2,p)
    return [v*inv%p for v in vec]

def crt(rs,ms):
    M=reduce(lambda a,b:a*b,ms); x=0
    for r,m in zip(rs,ms):
        Mi=M//m; x=(x+r*Mi*pow(Mi,-1,m))%M
    return x,M

def ratrec(a,m):
    if a==0: return Fraction(0)
    r0,r1=m,a%m; s0,s1=0,1; bound=int((m//2)**0.5)
    while r1>bound:
        q=r0//r1; r0,r1=r1,r0-q*r1; s0,s1=s1,s0-q*s1
    if s1==0 or abs(s1)>bound: return None
    return Fraction(r1,s1)

def main():
    primes={}
    for fn in glob.glob(os.path.join(HERE,'fleet_*.txt')):
        p=int(os.path.basename(fn)[len('fleet_'):-len('.txt')])
        seq=load(fn,p)
        if len(seq)>=104: primes[p]=seq
    print("primes with >=105 terms:", sorted(primes))
    vecs=[]; ms=[]
    for p in sorted(primes):
        v=nullvec(primes[p],p)
        if v is None: print(f"  prime {p}: nullvec failed (nulldim!=1 or norm 0)"); continue
        vecs.append(v); ms.append(p); print(f"  prime {p}: nullvec OK ({len(primes[p])} terms)")
    if len(ms)<2: print("need >=2 primes"); return
    # CRT + ratrec each component
    exact=[]
    for c in range(NC):
        x,M=crt([v[c] for v in vecs], ms); fr=ratrec(x,M); exact.append(fr)
    nfail=sum(1 for f in exact if f is None)
    if nfail: print(f"ratrecon failed for {nfail}/{NC} coeffs -> need more primes/bits"); return
    den=1
    for f in exact: den=lcm(den,f.denominator)
    ci=[int(f*den) for f in exact]
    g=0
    for c in ci: g=gcd(g,c)
    if g: ci=[c//g for c in ci]
    Cpoly=[[ci[k*(DEG+1)+j] for j in range(DEG+1)] for k in range(ORDER+1)]
    # certify vs exact q_n
    q={}
    for l in open(os.path.join(HERE,'..','zeta7_lc_terms.txt')):
        m=re.match(r'q_(\d+)\s*=\s*(\d+)',l.strip())
        if m: q[int(m.group(1))]=int(m.group(2))
    N=0
    while N in q: N+=1
    ex=[q[i] for i in range(N)]
    def cval(pc,n): return sum(pc[j]*n**j for j in range(len(pc)))
    ok=True; tested=0
    for n in range(len(ex)-ORDER):
        s=sum(cval(Cpoly[k],n)*ex[n+k] for k in range(ORDER+1)); tested+=1
        if s!=0: ok=False; print("CERT FAIL n=",n); break
    print(f"=== EXACT OPERATOR order {ORDER} deg {DEG} ===")
    for k in range(ORDER+1): print(f" c_{k}(n) =", Cpoly[k])
    print(f"CERTIFY vs {tested} exact q_n:", "ALL ZERO ✓" if ok else "FAILED")
    lead=[Cpoly[k][DEG] for k in range(ORDER+1)]
    print("char poly (lambda^0..4):", lead)
    import numpy as np
    roots=sorted(np.roots(lead[::-1]), key=lambda z:-abs(z))
    print("roots:", [complex(round(z.real,6),round(z.imag,8)) for z in roots])
    json.dump({'order':ORDER,'deg':DEG,'Cpoly':Cpoly,'certified':ok,'ntested':tested,'char_lead':lead},
              open(os.path.join(HERE,'recurrence.json'),'w'), indent=1)
    print("[saved recurrence.json]")

if __name__=="__main__": main()
