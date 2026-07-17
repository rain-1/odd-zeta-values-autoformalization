#!/usr/bin/env python3
# FAST modular DP: within-window incremental token distribution (n^2 per window, not n^4).
import sys, time
from collections import defaultdict
REPS = {
 "lc": [{1,2},{1,2,3,4},{2,3,4,5},{3,4,5},{4,5,6},{4,5,6,7},{5,6,7,8},{7,8}],
 "r2": [{1,2},{1,2,3},{2,3,4},{2,3,4,5,6},{3,4,5,6,7},{5,6,7},{6,7,8},{7,8}],
}
def Jmod(n, W, p, m=8):
    fact=[1]*(n+1)
    for i in range(1,n+1): fact[i]=fact[i-1]*i%p
    inv=[1]*(n+1); inv[n]=pow(fact[n],p-2,p)
    for i in range(n,0,-1): inv[i-1]=inv[i]*i%p
    fn=fact[n]
    lastwin={v:max(i for i,Wi in enumerate(W) if v in Wi) for v in range(1,m+1)}
    state={(0,)*m:1}
    for i,Wi in enumerate(W):
        idx=sorted(Wi)
        cur=defaultdict(int)
        for key,w in state.items(): cur[(key,n)]=w   # (state, remaining tokens for this window)
        for vv in idx:
            nxt=defaultdict(int)
            for (key,rem),w in cur.items():
                base=key[vv-1]; maxa=min(rem, n-base)
                kl=list(key)
                for a in range(maxa+1):
                    kl[vv-1]=base+a
                    nxt[(tuple(kl),rem-a)]=(nxt[(tuple(kl),rem-a)]+w*inv[a])%p
            cur=nxt
        ns=defaultdict(int)
        for (key,rem),w in cur.items():
            if rem!=0: continue
            ok=True
            for v in range(1,m+1):
                if lastwin[v]<=i and key[v-1]!=n: ok=False;break
            if ok: ns[key]=(ns[key]+w*fn)%p
        state=ns
    return state.get((n,)*m,0)%p
if __name__=="__main__":
    rep=sys.argv[1]; p=int(sys.argv[2]); n=int(sys.argv[3])
    t=time.time(); v=Jmod(n,REPS[rep],p)
    print(f"{n}={v}", flush=True)
    sys.stderr.write(f"{rep} p={p} n={n} {time.time()-t:.1f}s\n"); sys.stderr.flush()
