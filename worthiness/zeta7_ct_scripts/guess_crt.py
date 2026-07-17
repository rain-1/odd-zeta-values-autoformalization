#!/usr/bin/env python3
import sys, glob
from fractions import Fraction
PRIMES={'mlc_p1.txt':2000000011,'mlc_2000000033.txt':2000000033,
        'mlc_1999999973.txt':1999999973,'mlc_1999999943.txt':1999999943}
def load_mod(fn):
    d={}
    for l in open(fn):
        if '=' in l:
            n,v=l.split('='); d[int(n)]=int(v)%PRIMES[fn]
    N=0
    while N in d: N+=1
    return [d[i] for i in range(N)], PRIMES[fn]
def load_exact():
    seq={}
    for l in open('/home/ubuntu/fable-episode-2/zeta-math/worthiness/zeta7_mos_qn_values.txt'):
        n=int(l.split('_')[1].split('=')[0]); seq[n]=int(l.split('=')[1])
    try:
        for l in open('gen_lc.txt'):
            if '=' in l: n,v=l.split('='); seq[int(n)]=int(v)
    except FileNotFoundError: pass
    N=0
    while N in seq: N+=1
    return [seq[i] for i in range(N)]

def rref_null(seq, order, deg, p):
    # returns (nullspace_dim, reduced rows, pivots) for the ansatz matrix mod p
    ncols=(order+1)*(deg+1); nrows=len(seq)-order
    if nrows < ncols: return None
    M=[]
    for n in range(nrows):
        row=[]
        for k in range(order+1):
            b=seq[n+k]%p; nk=1
            for j in range(deg+1):
                row.append(nk*b%p); nk=nk*n%p
        M.append(row)
    R=nrows;C=ncols;pivots=[];prow=0
    for col in range(C):
        piv=next((r for r in range(prow,R) if M[r][col]%p),None)
        if piv is None: continue
        M[prow],M[piv]=M[piv],M[prow]
        invv=pow(M[prow][col],p-2,p); M[prow]=[x*invv%p for x in M[prow]]
        for r in range(R):
            if r!=prow and M[r][col]:
                f=M[r][col]; M[r]=[(M[r][c]-f*M[prow][c])%p for c in range(C)]
        pivots.append(col); prow+=1
        if prow==R: break
    free=[c for c in range(C) if c not in pivots]
    return len(free), M[:len(pivots)], pivots, free, ncols

def nullvec(seq, order, deg, p):
    dim,rows,pivots,free,C=rref_null(seq,order,deg,p)[0:5] if rref_null(seq,order,deg,p) else (0,None,None,None,0)
    r=rref_null(seq,order,deg,p)
    if r is None or r[0]!=1: return None
    dim,rows,pivots,free,C=r
    fc=free[0]; vec=[0]*C; vec[fc]=1
    for i,col in enumerate(pivots): vec[col]=(-rows[i][fc])%p
    return vec

def crt(rs, ms):
    from functools import reduce
    M=reduce(lambda a,b:a*b, ms); x=0
    for r,m in zip(rs,ms):
        Mi=M//m; x=(x+r*Mi*pow(Mi,-1,m))%M
    return x, M

def ratrecon(a, m):
    # rational reconstruction of a mod m
    if a==0: return Fraction(0)
    r0,r1=m,a%m; s0,s1=0,1; bound=int(m**0.5)
    while r1> bound:
        q=r0//r1
        r0,r1=r1,r0-q*r1
        s0,s1=s1,s0-q*s1
    if s1==0: return None
    from math import gcd
    if abs(s1)>bound: return None
    return Fraction(r1, s1)

if __name__=="__main__":
    ex=load_exact(); print("exact terms:",len(ex))
    seq1,p1=load_mod('mlc_p1.txt'); print("p1 mod terms:",len(seq1))
    # scan for minimal (order,degree)
    found=None
    for order in range(2,7):
        for deg in range(1,18):
            nc=(order+1)*(deg+1); nr=len(seq1)-order
            if nr < nc+3: continue
            r=rref_null(seq1,order,deg,p1)
            if r and r[0]>=1:
                print(f"order {order} deg {deg}: nulldim {r[0]} (unk {nc}, eq {nr})")
                if found is None and r[0]==1: found=(order,deg)
    if not found:
        print("NO recurrence yet"); sys.exit(0)
    order,deg=found; print("MINIMAL:",found)
    # reconstruct exact via CRT over available primes
    vecs=[]; ms=[]
    for fn,p in PRIMES.items():
        try: s,pp=load_mod(fn)
        except FileNotFoundError: continue
        if len(s)-order < (order+1)*(deg+1): continue
        v=nullvec(s,order,deg,pp)
        if v is None: continue
        vecs.append(v); ms.append(pp)
    print("primes used for CRT:",len(ms))
    C=(order+1)*(deg+1)
    exact_vec=[]
    for c in range(C):
        rs=[v[c] for v in vecs]; x,M=crt(rs,ms); fr=ratrecon(x,M); exact_vec.append(fr)
    if any(fr is None for fr in exact_vec):
        print("rational reconstruction failed for some coeff -> need more primes"); sys.exit(0)
    # clear denominators
    from math import lcm
    den=1
    for fr in exact_vec: den=lcm(den, fr.denominator)
    coeffs_int=[int(fr*den) for fr in exact_vec]
    from math import gcd
    g=0
    for c in coeffs_int: g=gcd(g,c)
    coeffs_int=[c//g for c in coeffs_int]
    # c_k(n) = sum_j coeffs_int[k*(deg+1)+j] n^j
    print("=== RECURRENCE (order",order,"deg",deg,") ===")
    C_polys=[]
    for k in range(order+1):
        pc=[coeffs_int[k*(deg+1)+j] for j in range(deg+1)]
        C_polys.append(pc); print(f" c_{k}(n) =", pc)
    # certify vs exact terms
    def cval(pc,n): return sum(pc[j]*n**j for j in range(len(pc)))
    ok=True; tested=0
    for n in range(len(ex)-order):
        s=sum(cval(C_polys[k],n)*ex[n+k] for k in range(order+1))
        tested+=1
        if s!=0: ok=False; print("CERT FAIL at n=",n)
    print(f"CERTIFY vs {tested} exact terms:", "ALL ZERO" if ok else "FAILED")
    # char poly (leading in n)
    D=deg
    lead=[C_polys[k][D] for k in range(order+1)]
    print("char poly coeffs (lambda^0..order):", lead)
