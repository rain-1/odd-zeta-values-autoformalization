import numpy as np, mpmath as mp
mp.mp.dps=30
I0exact=float(mp.mpf(75)/4*mp.zeta(7)-9*mp.zeta(5)*mp.zeta(2))
def series(L):
    M=5*L+10
    H=np.zeros(M+1); H[1:]=np.cumsum(1.0/np.arange(1,M+1))
    k=np.arange(L+1)
    k3g,k4g,k5g=np.meshgrid(k,k,k,indexing='ij')
    s345=(k3g+k4g+k5g).astype(np.int64)
    h=(H[s345+1]-H[k5g])/(k3g+k4g+1.0)
    base=(h/(s345+1.0)).ravel()
    s345f=s345.ravel().astype(np.float64)
    k3f=k3g.ravel().astype(np.float64)
    tot=0.0
    for k2 in range(L+1):
        K=k2+k3f
        tot+=np.dot(H[(k2+k3g).ravel()+1]/(K+1.0)**2/(k2+s345f+2.0), base)
    return tot
Ls=[60,90,120,160]
S=[series(L) for L in Ls]
for L,v in zip(Ls,S): print(f"L={L:4d} S={v:.8f}  rem={I0exact-v:.4e}")
L1,L2,L3=Ls[-3:]; s1,s2,s3=S[-3:]
def f(q): return (s2-s1)*(L2**-q-L3**-q)-(s3-s2)*(L1**-q-L2**-q)
lo,hi=0.05,3.0
for _ in range(100):
    mid=(lo+hi)/2
    if f(lo)*f(mid)<=0: hi=mid
    else: lo=mid
q=(lo+hi)/2; a=(s3-s2)/(L2**-q-L3**-q); Sinf=s3+a*L3**-q
print(f"fit q={q:.3f} Sinf={Sinf:.6f}  exact={I0exact:.6f}  diff={Sinf-I0exact:.2e}")
