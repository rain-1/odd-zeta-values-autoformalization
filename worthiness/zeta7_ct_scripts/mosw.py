#!/usr/bin/env python3
# TRUE MOS ground-truth diagonal (full-coupler windows) for extra anchors. Slow.
import sys, time
from math import factorial
W=[{2,3},{2,3,4,5},{3,4,5},{3,4,5,6,7},{5,6,7},{7,8},{1,2,3,4,5,6,7,8},{1,2,3}]
def J(n,m=8):
    from collections import defaultdict
    lastwin={v:max(i for i,Wi in enumerate(W) if v in Wi) for v in range(1,m+1)}
    state=defaultdict(int); state[(0,)*m]=1
    def comps(t,pp):
        if pp==1: yield (t,); return
        for a in range(t+1):
            for r in comps(t-a,pp-1): yield (a,)+r
    for i,Wi in enumerate(W):
        idx=sorted(Wi); ns=defaultdict(int)
        for e,c in list(state.items()):
            for dist in comps(n,len(idx)):
                ne=list(e); ok=True
                for v,a in zip(idx,dist):
                    ne[v-1]+=a
                    if ne[v-1]>n: ok=False;break
                if not ok: continue
                for v in range(1,m+1):
                    if lastwin[v]<=i and ne[v-1]!=n: ok=False;break
                if not ok: continue
                mm=factorial(n)
                for a in dist: mm//=factorial(a)
                ns[tuple(ne)]+=c*mm
        state=ns
    return state.get((n,)*m,0)
n=int(sys.argv[1]); t=time.time(); v=J(n)
print(f"MOS {n}={v}", flush=True); sys.stderr.write(f"mos n={n} {time.time()-t:.1f}s\n")
