import sympy as sp,sys,time
from collections import Counter,defaultdict
t=sp.symbols('t1:8',positive=True); x=sp.symbols('x1:8',positive=True); xset=set(x)
def sigma(T):
    t1=T[0]; return [1-t1/T[1],1-t1/T[2],1-t1/T[3],1-t1/T[4],1-t1/T[5],1-t1/T[6],1-t1]
def tau(T):
    t1=T[0]; return [t1,t1/T[6],t1/T[5],t1/T[4],t1/T[3],t1/T[2],t1/T[1]]
def Dfacs(g):
    g1,g2,g3,g4,g5,g6,g7=g; return [g3-g1,g3,g5,g5-g2,g7-g2,g7-g4,1-g4,1-g6]
def Jsig_at(p): return -p[0]**6/(p[1]**2*p[2]**2*p[3]**2*p[4]**2*p[5]**2*p[6]**2)
cub=dict(zip(t,[sp.prod(x[j] for j in range(i,7)) for i in range(7)]))
def add(cnt,expr,weight):
    num,den=sp.fraction(sp.cancel(expr.subs(cub)))
    for part,w in ((num,weight),(den,-weight)):
        for f,e in sp.factor_list(part)[1]:
            if f.free_symbols & xset: cnt[sp.factor(f)] += w*e
label=sys.argv[1]; k=int(sys.argv[2]); useT=(sys.argv[3]=='T')
cur=list(t); Jp=[]
if useT:
    gt=tau(list(t)); Jt=sp.cancel(sp.Matrix([[sp.diff(gt[i],t[j]) for j in range(7)] for i in range(7)]).det())
    cur=[sp.cancel(e) for e in gt]; Jp=[Jt]
for _ in range(k):
    Jp=Jp+[Jsig_at(cur)]; cur=[sp.cancel(sp.together(e)) for e in sigma(cur)]
t0=time.time()
cnt=defaultdict(int)
for p in Jp: add(cnt,p,-1)
for f in Dfacs(cur): add(cnt,f,+1)
cf=[f for f,m in cnt.items() if m>0 and len(f.free_symbols&xset)>=2]
supp=sorted(tuple(sorted(int(str(v)[1:]) for v in (f.free_symbols&xset))) for f in cf)
cc=Counter(v for s in supp for v in s); leaves=sorted(v for v in cc if cc[v]==1)
lo=[v for v in leaves if v<=2]; hi=[v for v in leaves if v>=6]
print(f"{label} #cpl={len(supp)} sizes={sorted(len(s) for s in supp)} leaves={leaves} lo={lo} hi={hi} {'BOTH' if lo and hi else ''} supp={supp} [{time.time()-t0:.0f}s]")
