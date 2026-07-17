from math import factorial
from itertools import combinations
import sys
def J(W, m, n):
    from collections import defaultdict
    state=defaultdict(int); state[(0,)*m]=1
    def comps(total,parts):
        if parts==1: yield (total,); return
        for a in range(total+1):
            for rest in comps(total-a,parts-1): yield (a,)+rest
    for Wi in W:
        idx=sorted(Wi); ns=defaultdict(int)
        for e,coef in list(state.items()):
            for dist in comps(n,len(idx)):
                ne=list(e); ok=True
                for v,a in zip(idx,dist):
                    ne[v-1]+=a
                    if ne[v-1]>n: ok=False;break
                if not ok: continue
                mm=factorial(n)
                for a in dist: mm//=factorial(a)
                ns[tuple(ne)]+=coef*mm
        state=ns
    return state.get((n,)*m,0)
m=8
maxsz=5
intervals=[tuple(range(a,b+1)) for a in range(1,m+1) for b in range(a,m+1) if (b-a+1)<=maxsz and (b-a+1)>=2]
print(f"{len(intervals)} intervals size 2..{maxsz}; combos C(.,8)", file=sys.stderr)
hits=[]
tot=0
for combo in combinations(intervals,8):
    # each variable must be covered; quick coverage check
    cover=[0]*(m+1)
    for w in combo:
        for v in w: cover[v]+=1
    if any(cover[v]==0 for v in range(1,m+1)): continue
    # total tokens must equal 8n exactly = sum sizes... need sum of sizes >= ? diagonal balances at 8n; each window gives n tokens; total 8n; need each var reach n
    tot+=1
    if J([set(w) for w in combo],m,1)!=61: continue
    if J([set(w) for w in combo],m,2)!=52921: continue
    if J([set(w) for w in combo],m,3)!=94357501: continue
    hits.append(combo)
    print("HIT", [list(w) for w in combo], flush=True)
print(f"checked {tot} coverage-valid combos; {len(hits)} full hits", file=sys.stderr)
