import mpmath as mp
mp.mp.dps = 40

def Phi_gamma(n, s, t):
    G = mp.gamma
    Gs = G(n+1+s)**3 * G(-s) / G(2*n+2+s)**2
    Gt = G(n+1+t)**3 * G(-t) / G(2*n+2+t)**2
    return Gs*Gt*G(2*n+2+s+t)*G(-n-1-s-t)

def Phi_sine(n, s, t):
    def r(x):
        num = mp.mpf(1)
        for i in range(1,n+1): num*= (x+i)
        den = mp.mpf(1)
        for j in range(n+1,2*n+2): den*=(x+j)
        return num/den**2
    C = mp.mpf(1)
    for l in range(n+2,2*n+2): C*=(s+t+l)
    R = r(s)*r(t)*C
    pi = mp.pi
    return (-1)**n * pi**3 * R/(mp.sin(pi*s)*mp.sin(pi*t)*mp.sin(pi*(s+t)))

for n in [1,2,3]:
    s = mp.mpf('0.3') + mp.mpf('0.17')*1j
    t = mp.mpf('-0.41') + mp.mpf('0.23')*1j
    a = Phi_gamma(n,s,t); b = Phi_sine(n,s,t)
    print(f"n={n}: |gamma-sine|/|gamma| = {abs(a-b)/abs(a)}")
