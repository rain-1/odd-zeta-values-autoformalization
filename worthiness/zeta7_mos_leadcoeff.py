"""
McCarthy-Osburn-Straub (arXiv:1705.05586) leading-coefficient construction for
the BZ zeta(7) cellular integral, sigma=(10,2,4,1,6,3,8,5,9,7), N=10.
A_sigma(n) = J_sigma(n) = [(x1..x8)^n] (prod W_i)^n  (diagonal coeff of prod of
linear window-sums), derived by the paper's residue method (Sec 3.2).
Windows (variable index sets), derived from the standard consecutive differences
z_j - z_{j+1} in the sigma-gap coordinates x_1..x_8 (x_8=1 homogenizer):
"""
from itertools import product as iproduct
from math import comb
# window variable-sets (1-indexed vars 1..8)
W = [ {2,3}, {2,3,4,5}, {3,4,5}, {3,4,5,6,7}, {5,6,7}, {7,8}, {1,2,3,4,5,6,7,8}, {1,2,3} ]

def J(n):
    # diagonal coeff of prod_i (sum_{j in W_i} x_j)^n  = coeff of x1^n..x8^n
    # dynamic programming over exponent vector, capping each at n.
    from collections import defaultdict
    state = defaultdict(int); state[(0,)*8] = 1
    from math import factorial
    for Wi in W:
        idx = sorted(Wi)  # variables in this window
        ns = defaultdict(int)
        # multinomial distributions of n tokens over the vars in Wi
        # enumerate compositions of n into len(idx) parts
        def comps(total, parts):
            if parts==1: yield (total,); return
            for a in range(total+1):
                for rest in comps(total-a, parts-1):
                    yield (a,)+rest
        # precompute multinomial coeffs
        for e,coef in list(state.items()):
            for dist in comps(n, len(idx)):
                mult = factorial(n)
                ok=True
                ne=list(e)
                for v,a in zip(idx,dist):
                    from math import factorial as f
                    ne[v-1]+=a
                    if ne[v-1]>n: ok=False; break
                if not ok: continue
                # multinomial n!/prod a!
                m=factorial(n)
                for a in dist: m//=factorial(a)
                ns[tuple(ne)] += coef*m
        state=ns
    return state.get((n,)*8, 0)

for n in range(4):
    print(f"A_sigma({n}) = {J(n)}")
print("target q_n = 1, 61, 52921  (BZ n=0,1,2)")
