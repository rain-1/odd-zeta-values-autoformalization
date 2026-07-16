import mpmath as mp
from math import comb
mp.mp.dps=20
def J3(p0,p1,p2,p3,q1,q2,q3):
    def f(y1,y2,y3):
        return (y1**p1*(1-y1)**q1*y2**p2*(1-y2)**q2*y3**p3*(1-y3)**q3
                /(1-y3*(1-y1*y2))**(p0+1))
    return mp.quad(lambda y1: mp.quad(lambda y2: mp.quad(lambda y3: f(y1,y2,y3),[0,1]),[0,1]),[0,1])
def Idd(n):
    tot=mp.mpf(0)
    for k in range(n, 2*n+1):
        c=comb(k,n)*comb(n,k-n)**2
        if c==0: continue
        tot+= (-1)**k * c * J3(n,n,n,2*n-k,n,n,k)
    return (-1)**(3*n)*tot
n=1
val=Idd(n)
target=21*mp.zeta(3)-mp.mpf(101)/4
print(f"n=1: I3-sum={val}  target={target}  diff={abs(val-target)}")
