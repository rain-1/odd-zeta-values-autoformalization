import json
from math import gcd
def d_lcm(N):
    r=1
    for k in range(2,N+1): r=r*k//gcd(r,k)
    return r
def ordp(x,p):
    e=0
    while x%p==0: x//=p; e+=1
    return e
data=json.load(open('/home/ubuntu/fable-episode-2/zeta-math/worthiness/proof_sym_data.json'))
print("P_n:  ord_p(den) vs ord_p(12 d_n^5) [=bound]; and ord_p(d_n^5)")
for n in ['1','2','3','4','5']:
    r=data[n]; dn=r['dn']; denP=r['denP']
    row=[]
    for p in [2,3,5,7]:
        od=ordp(denP,p) if denP%p==0 else 0
        odn5=5*(ordp(dn,p) if dn%p==0 else 0)
        bound=odn5+({2:2,3:1}.get(p,0))
        row.append(f"p={p}:{od}(bnd{bound},d5^{odn5})")
    print(f" n={n}: den={r['denP_fac']:>12}  "+"  ".join(row))
print("\nP̂_n: ord_p(den) vs ord_p(2 d_n^2 d_2n) [=bound]")
for n in ['1','2','3','4','5']:
    r=data[n]; dn=r['dn']; d2n=r['d2n']; denPh=r['denPhat']
    B=2*dn*dn*d2n
    row=[]
    for p in [2,3,5,7]:
        od=ordp(denPh,p) if denPh%p==0 else 0
        ob=ordp(B,p) if B%p==0 else 0
        row.append(f"p={p}:{od}(bnd{ob})")
    print(f" n={n}: den={r['denPhat_fac']:>18} 2d_n^2d_2n={B}  "+" ".join(row))
