import sympy as sp
t=sp.symbols('t1:8',positive=True)
def sigma(T):
    t1=T[0]
    return [1-t1/T[1],1-t1/T[2],1-t1/T[3],1-t1/T[4],1-t1/T[5],1-t1/T[6],1-t1]
def tau(T):
    t1=T[0]
    return [t1,t1/T[6],t1/T[5],t1/T[4],t1/T[3],t1/T[2],t1/T[1]]
# order check numerically
import mpmath as mp
pt=[0.1,0.2,0.35,0.5,0.62,0.77,0.9]
def apply_num(f,p): 
    return [float(sp.N(e.subs(dict(zip(t,p))))) if hasattr(e,'subs') else e for e in f]
# build sigma^k symbolic with cancel
cur=list(t)
orbit=[cur]
for k in range(1,11):
    cur=[sp.cancel(sp.together(e)) for e in sigma(cur)]
    orbit.append(cur)
print("sigma^10 == identity? ", [sp.simplify(orbit[10][i]-t[i])==0 for i in range(7)])
# sizes
for k in [1,2,3,5]:
    print(f"sigma^{k} leaf0 sample:", sp.simplify(orbit[k][0]))
