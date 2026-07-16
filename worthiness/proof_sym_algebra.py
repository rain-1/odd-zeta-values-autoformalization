import sympy as sp

s, t = sp.symbols('s t')

def check_reduction(n):
    G = sp.gamma
    # Gamma-form rational part R(s,t)
    R_gamma = (G(n+1+s)**3 * G(n+1+t)**3 * G(2*n+2+s+t)
               / (G(2*n+2+s)**2 * G(2*n+2+t)**2 * G(1+s)*G(1+t)*G(n+2+s+t)))
    # Claimed factorization r(s) r(t) C(s,t)
    def r(x):
        num = sp.prod([x+i for i in range(1, n+1)])
        den = sp.prod([x+j for j in range(n+1, 2*n+2)])**2
        return num/den
    C = sp.prod([s+t+l for l in range(n+2, 2*n+2)])
    R_claim = r(s)*r(t)*C
    diff = sp.simplify(R_gamma/R_claim)
    return diff

for n in range(1,5):
    print(f"n={n}: R_gamma/R_claim =", check_reduction(n))
