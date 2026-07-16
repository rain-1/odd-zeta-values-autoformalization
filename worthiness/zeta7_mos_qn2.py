"""Fast integer bucket elimination for q_n = [x1^n..x8^n] prod W_i^n.
State: partial row-sums s_i of active windows. Coefficient integer via
telescoping multinomials: multinomial(n;a) = prod_step C(cumsum, a_step)."""
from math import comb
import sys, time
W=[{2,3},{2,3,4,5},{3,4,5},{3,4,5,6,7},{5,6,7},{7,8},set(range(1,9)),{1,2,3}]
rng=[(min(w),max(w)) for w in W]
def qn(n):
    if n==0: return 1
    # active windows tracked as dict window_index->s_i ; represent state as tuple sorted by win idx
    from collections import defaultdict
    # precompute compositions of n into k parts as lists
    compcache={}
    def comps(total,parts):
        key=(total,parts)
        if key in compcache: return compcache[key]
        if parts==1: res=[(total,)]
        else:
            res=[]
            for a in range(total+1):
                for r in comps(total-a,parts-1): res.append((a,)+r)
        compcache[key]=res; return res
    state={():1}   # keys: tuple of (win,s) for active windows
    active=[]
    for j in range(1,9):
        entering=[i for i in range(8) if rng[i][0]==j]
        wins=[i for i in range(8) if rng[i][0]<=j<=rng[i][1]]
        finishing=set(i for i in range(8) if rng[i][1]==j)
        dl=comps(n,len(wins))
        ns=defaultdict(int)
        for st,c in state.items():
            sd=dict(st)  # win->s
            for i in entering: sd[i]=0
            for dd in dl:
                cc=c; ok=True; news={}
                for i,a in zip(wins,dd):
                    si=sd.get(i,0)
                    ns_i=si+a
                    if ns_i>n: ok=False; break
                    cc*=comb(ns_i,a)   # telescoping multinomial
                    news[i]=ns_i
                if not ok: continue
                # build new state: keep windows not yet finished, drop finishing (require ==n)
                good=True; key=[]
                for i in range(8):
                    if rng[i][0]<=j:   # started
                        val=news.get(i, sd.get(i,0))
                        if i in finishing:
                            if val!=n: good=False; break
                        elif rng[i][1]>j:  # still active
                            key.append((i,val))
                if not good: continue
                ns[tuple(key)]+=cc
        state=dict(ns)
    return state.get((),0)
vals=[int(a) for a in sys.argv[1:]]
t0=time.time()
for n in vals:
    print(f"q_{n} = {qn(n)}   [{time.time()-t0:.1f}s]",flush=True)
