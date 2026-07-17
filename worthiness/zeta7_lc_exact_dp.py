#!/usr/bin/env python3
# Low-coupling-window DP for BZ zeta(7) M_{0,10} diagonal q_n.
# Two structurally-different reps (lc, r2), each reproduces the 31 known q_n. stdlib only.
# Usage: qnw.py <rep> validate | qnw.py <rep> <n>
import sys, time
from math import factorial
REPS = {
 "lc": [{1,2},{1,2,3,4},{2,3,4,5},{3,4,5},{4,5,6},{4,5,6,7},{5,6,7,8},{7,8}],
 "r2": [{1,2},{1,2,3},{2,3,4},{2,3,4,5,6},{3,4,5,6,7},{5,6,7},{6,7,8},{7,8}],
}
def J(n, W, m=8):
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
KNOWN={0:1,1:61,2:52921,3:94357501,4:235634763001,5:715362962769061,
 6:2467090298135229481,7:9307547697979861686781,8:37534429062230228638731001,
 9:159353643933835371998356995061,10:704783363364126892491454202797921,
 20:6732959503221479451702347582810393313180305780285025274478532779556001,
 30:170671539376011487684498427256431657819316155090186544275533813918760166019515993414639771720679404294753481}
if __name__=="__main__":
    rep=sys.argv[1]; W=REPS[rep]
    if sys.argv[2]=="validate":
        ok=all(J(n,W)==v for n,v in KNOWN.items())
        print("VALIDATE_OK" if ok else "VALIDATE_FAIL"); sys.exit(0 if ok else 1)
    n=int(sys.argv[2]); t=time.time(); v=J(n,W)
    print(f"{n}={v}", flush=True)
    sys.stderr.write(f"{rep} n={n} {time.time()-t:.1f}s\n"); sys.stderr.flush()
