"""proof_sym_v2_closedforms.py -- audit of SS4 (partial fractions) and the
Zudilin/Rhin-Viola integrality lemmas used in SS5 (v2).

(A) Lemma 4.1 closed forms for A_j, B_j of r(s), exact, n=1..8.
(B) Corollary 4.2:  n! B_j in Z  and  n! d_{2n} A_j in Z, n=1..8.
(C) Zudilin Lemma 1 (partial-fraction integrality) sanity check on a sample
    rational function 1/prod (t+k_j)^{s_j}, k_j distinct in {0..N}:
    d_N^{s-i} b_{i,j} in Z,  s = sum s_j.
(D) Harmonic clearing:  d_n^i * sum_{l=1}^k 1/l^i  in Z  for i>=1, k<=n.
"""
import sympy as sp
from math import comb, factorial, gcd

s = sp.symbols('s')

def H(m):
    return sum(sp.Rational(1, i) for i in range(1, m + 1))

def d_lcm(N):
    r = 1
    for k in range(2, N + 1):
        r = r * k // gcd(r, k)
    return r

# (A)+(B)
print("(A) Lemma 4.1 closed forms + (B) Cor 4.2 integrality, n=1..8:")
allA = True
for n in range(1, 9):
    num = sp.prod([s + i for i in range(1, n + 1)])
    den = sp.prod([(s + j) ** 2 for j in range(n + 1, 2 * n + 2)])
    r = num / den
    okcf = True; okcor = True
    for j in range(n + 1, 2 * n + 2):
        a = j - (n + 1)
        g = sp.cancel((s + j) ** 2 * r)
        Bj = sp.Rational(g.subs(s, -j))
        Aj = sp.Rational(sp.diff(g, s).subs(s, -j))
        Bf = sp.Integer((-1) ** n) * comb(n + a, a) * comb(n, a) ** 2 / sp.Integer(factorial(n))
        Af = Bf * (3 * H(a) - H(n + a) - 2 * H(n - a))
        if sp.simplify(Bj - Bf) != 0 or sp.simplify(Aj - Af) != 0:
            okcf = False
        # Cor 4.2
        if (factorial(n) * Bj).q != 1:
            okcor = False
        if (factorial(n) * d_lcm(2 * n) * Aj).q != 1:
            okcor = False
    allA &= okcf and okcor
    print(f"    n={n}: closed forms {'OK' if okcf else 'FAIL'}; "
          f"n!B, n!d_2n A in Z: {'OK' if okcor else 'FAIL'}")
print("  => SS4:", "PASS" if allA else "FAIL")

# (C) Zudilin Lemma 1 on samples
print("\n(C) Zudilin Lemma 1  d_N^{s-i} b_{i,j} in Z:")
t = sp.symbols('t')
def check_zud(ks, ss, N):
    denom = sp.prod([(t + k) ** e for k, e in zip(ks, ss)])
    S = 1 / denom
    stot = sum(ss)
    apart = sp.apart(S, t)
    ok = True
    dN = d_lcm(N)
    for k, e in zip(ks, ss):
        g = sp.cancel(S * (t + k) ** e)
        for i in range(1, e + 1):
            # b_{i,k} = 1/(e-i)! * d^{e-i}/dt^{e-i} g |_{t=-k}
            m = e - i
            bik = sp.Rational(sp.diff(g, t, m).subs(t, -k) / factorial(m))
            if (dN ** (stot - i) * bik).q != 1:
                ok = False
    return ok
samples = [([0, 2, 3], [2, 1, 2], 5), ([1, 4, 6], [1, 3, 1], 6), ([0, 1, 5], [2, 2, 1], 5)]
for ks, ss, N in samples:
    print(f"    k={ks} s={ss} N={N}: {'OK' if check_zud(ks, ss, N) else 'FAIL'}")

# (D) harmonic clearing
print("\n(D) d_n^i * sum_{l<=k} 1/l^i in Z (i=1..5, n=1..8, k<=n):")
okh = True
for n in range(1, 9):
    dn = d_lcm(n)
    for i in range(1, 6):
        for k in range(0, n + 1):
            val = sum((sp.Rational(1, l ** i) for l in range(1, k + 1)), sp.Integer(0))
            if sp.Rational(dn ** i * val).q != 1:
                okh = False
print("    ", "PASS" if okh else "FAIL")
