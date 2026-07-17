#!/usr/bin/env python3
# Robust recurrence guesser for q_n: modular nullspace at several primes + CRT + rational reconstruction.
# Loads fleet_<prime>.txt (n=v modular) and exact terms (ground truth + gen_lc) for certification.
import sys, glob, os
from fractions import Fraction
from functools import reduce
from math import gcd, lcm

HERE=os.path.dirname(os.path.abspath(__file__))
GT='/home/ubuntu/fable-episode-2/zeta-math/worthiness/zeta7_mos_qn_values.txt'

def load_mod(fn, p):
    d={}
    for l in open(fn):
        if '=' in l:
            n,v=l.split('=',1)
            try: n=int(n); v=int(v)
            except: continue
            d[n]=v%p
    N=0
    while N in d: N+=1
    return [d[i] for i in range(N)]

def load_exact():
    seq={}
    for l in open(GT):
        if '_' in l and '=' in l:
            n=int(l.split('_')[1].split('=')[0]); seq[n]=int(l.split('=')[1])
    lc=os.path.join(HERE,'gen_lc.txt')
    if os.path.exists(lc):
        for l in open(lc):
            if '=' in l:
                n,v=l.split('=',1)
                try: seq[int(n)]=int(v)
                except: pass
    N=0
    while N in seq: N+=1
    return [seq[i] for i in range(N)]

def rref(M,C,p):
    R=len(M); pivots=[]; prow=0
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
    return M[:len(pivots)], pivots

def build(seq, order, deg, p):
    ncols=(order+1)*(deg+1); nrows=len(seq)-order
    M=[]
    for n in range(nrows):
        row=[]
        for k in range(order+1):
            b=seq[n+k]%p; nk=1
            for j in range(deg+1):
                row.append(nk*b%p); nk=nk*n%p
        M.append(row)
    return M, ncols, nrows

def nulldim(seq, order, deg, p):
    M,C,nr=build(seq,order,deg,p)
    if nr < C: return None, C, nr
    rows,piv=rref(M,C,p)
    return C-len(piv), C, nr

def nullvec(seq, order, deg, p):
    M,C,nr=build(seq,order,deg,p)
    rows,piv=rref(M,C,p)
    free=[c for c in range(C) if c not in piv]
    if len(free)!=1: return None
    fc=free[0]; vec=[0]*C; vec[fc]=1
    for i,col in enumerate(piv): vec[col]=(-rows[i][fc])%p
    return vec

def crt(rs, ms):
    M=reduce(lambda a,b:a*b, ms); x=0
    for r,m in zip(rs,ms):
        Mi=M//m; x=(x+r*Mi*pow(Mi,-1,m))%M
    return x, M

def ratrecon(a, m):
    if a==0: return Fraction(0)
    r0,r1=m,a%m; s0,s1=0,1; bound=int((m//2)**0.5)
    while r1>bound:
        q=r0//r1; r0,r1=r1,r0-q*r1; s0,s1=s1,s0-q*s1
    if s1==0 or abs(s1)>bound: return None
    return Fraction(r1, s1)

def main():
    primes={}
    for fn in sorted(glob.glob(os.path.join(HERE,'fleet_*.txt'))):
        p=int(os.path.basename(fn)[len('fleet_'):-len('.txt')])
        seq=load_mod(fn,p)
        if len(seq)>=20: primes[p]=seq
    ex=load_exact()
    print(f"exact terms: {len(ex)} (n=0..{len(ex)-1})")
    for p in sorted(primes): print(f"  prime {p}: {len(primes[p])} terms")
    if not primes: print("no primes"); return
    # pick the longest prime for structure scan
    pbest=max(primes, key=lambda p: len(primes[p])); sbest=primes[pbest]
    print(f"structure scan on prime {pbest} ({len(sbest)} terms)")
    found=None
    for order in range(2,9):
        for deg in range(1,26):
            nc=(order+1)*(deg+1); nr=len(sbest)-order
            if nr < nc+2: continue
            dim,_,_=nulldim(sbest,order,deg,pbest)
            if dim is not None and dim>=1:
                print(f"  order {order} deg {deg}: nulldim {dim} (unk {nc}, eq {nr})")
                if dim==1 and found is None: found=(order,deg)
    if not found:
        print("NO minimal recurrence found in scan window"); return
    order,deg=found; print("MINIMAL:", found)
    # confirm same (order,deg) gives nulldim 1 at a second prime
    C=(order+1)*(deg+1)
    usable=[p for p in primes if len(primes[p])-order>=C]
    print("primes usable for CRT:", usable)
    vecs=[]; ms=[]
    for p in usable:
        v=nullvec(primes[p],order,deg,p)
        if v is None: print(f"  prime {p}: nulldim!=1 at ({order},{deg}) -- skip"); continue
        # normalize: make leading (highest coeff of c_order) monic-ish -> keep as is, CRT then ratrecon
        vecs.append(v); ms.append(p)
    print("primes contributing:", len(ms))
    if len(ms)<2: print("need >=2 primes for CRT"); return
    exact_vec=[]
    for c in range(C):
        rs=[v[c] for v in vecs]; x,M=crt(rs,ms); fr=ratrecon(x,M); exact_vec.append(fr)
    if any(fr is None for fr in exact_vec):
        print("ratrecon FAILED for", sum(1 for f in exact_vec if f is None),"coeffs -> need more primes"); return
    den=1
    for fr in exact_vec: den=lcm(den, fr.denominator)
    ci=[int(fr*den) for fr in exact_vec]
    g=0
    for c in ci: g=gcd(g,c)
    if g: ci=[c//g for c in ci]
    Cpoly=[[ci[k*(deg+1)+j] for j in range(deg+1)] for k in range(order+1)]
    print(f"=== RECURRENCE order {order} degree {deg} ===")
    for k in range(order+1): print(f" c_{k}(n) =", Cpoly[k])
    def cval(pc,n): return sum(pc[j]*n**j for j in range(len(pc)))
    ok=True; tested=0
    for n in range(len(ex)-order):
        s=sum(cval(Cpoly[k],n)*ex[n+k] for k in range(order+1))
        tested+=1
        if s!=0: ok=False; print("CERT FAIL n=",n)
    print(f"CERTIFY vs {tested} exact terms:", "ALL ZERO" if ok else "FAILED")
    lead=[Cpoly[k][deg] for k in range(order+1)]
    print("char poly (lambda^0..order):", lead)
    import numpy as np
    r=np.roots(lead[::-1])
    print("char roots:", sorted(r, key=lambda z: -abs(z)))
    import json
    json.dump({'order':order,'deg':deg,'Cpoly':Cpoly,'certified':ok,'ntested':tested,
               'char_lead':lead},
              open(os.path.join(HERE,'recurrence.json'),'w'), indent=1)
    print("[saved recurrence.json]")

if __name__=="__main__": main()
