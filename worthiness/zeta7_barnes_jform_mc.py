import numpy as np, mpmath as mp
mp.mp.dps=30
I0=float(mp.mpf(75)/4*mp.zeta(7)-9*mp.zeta(5)*mp.zeta(2))
rng=np.random.default_rng(1); tot=0.0;tot2=0.0;N=0
for _ in range(400):
    Y=rng.random((500000,7)); y1,y2,y3,y4,y5,y6,y7=[Y[:,i] for i in range(7)]
    a=1-y1*y2; c=1-y6*y7
    P2=1-y3*y4*a; P3=1-y3*y4*y5*a*c; P4=1-y4*y5*c; P5=1-y4*y5*(1-y7)
    f=y4/(P2*P3*P4*P5)
    tot+=f.sum();tot2+=(f*f).sum();N+=len(f)
m=tot/N; se=((tot2/N-m*m)/N)**0.5
print(f"J-form MC I0 = {m:.5f} +- {se:.5f}   exact={I0:.5f}")
