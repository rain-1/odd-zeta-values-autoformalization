#!/usr/bin/env python3
"""
h2_divisors.py  --  [PROVEN combinatorics]
Identify the divisors A (polar locus of the integrand) and B (boundary of the
domain simplex) for the totally-symmetric Brown-Zudilin cellular integral on
Mbar_{0,8}, translate them to boundary divisors delta_S, and enumerate the
codimension-2 strata inside A that can carry the weight-4 piece gr^W_4 M = Q(-2).

Marked-point labelling (standard cellular chart, points on the real line in
cyclic order 1..8 around the octagon):
      1 |-> 0 ,  2 |-> t1 , 3 |-> t2 , 4 |-> t3 , 5 |-> t4 , 6 |-> t5 , 7 |-> 1 , 8 |-> oo
so that  t_i - t_j  <-> collision of the two marked points carrying t_i and t_j.

Boundary divisor delta_S of Mbar_{0,n}:  S subset of {1..n}, 2<=|S|<=n-2, with
delta_S = delta_{S^c}.  delta_S, delta_T meet (codim-2 stratum) iff {S,T} are
COMPATIBLE (non-crossing): S<=T, T<=S, S∩T=∅, or S∪T={1..n}.  (Keel.)
"""
from itertools import combinations

n = 8
U = frozenset(range(1, n+1))

def canon(S):
    S = frozenset(S)
    Sc = U - S
    return min((tuple(sorted(S)), tuple(sorted(Sc))), key=lambda t:(len(t), t))

def all_divisors():
    seen = set()
    for k in range(2, n-1):
        for S in combinations(range(1,n+1), k):
            seen.add(canon(S))
    return sorted(seen, key=lambda t:(len(t), t))

def compatible(S, T):
    S, T = frozenset(S), frozenset(T)
    return S<=T or T<=S or (S&T==frozenset()) or (S|T==U)

divs = all_divisors()
print(f"Mbar_0,{n}:  #boundary divisors = {len(divs)}   (formula (2^{n}-2-2*{n})/2 = "
      f"{(2**n-2-2*n)//2})")

# ---- point<->variable dictionary ----
pt = {'0':1, 't1':2, 't2':3, 't3':4, 't4':5, 't5':6, '1':7, 'oo':8}
def dv(a, b):  # divisor from difference of two points given by variable names
    return canon({pt[a], pt[b]})

# ---- A: polar factors from the dt-line denominator (t3-t1) t3 (1-t4)(t4-t2)(t5-t2)
A_factors = {
    '(t3-t1)': ('t3','t1'),   # z4 - z2  -> delta_{2,4}
    't3'     : ('t3','0'),    # z4 - z1  -> delta_{1,4}
    '(1-t4)' : ('1','t4'),    # z7 - z5  -> delta_{5,7}
    '(t4-t2)': ('t4','t2'),   # z5 - z3  -> delta_{3,5}
    '(t5-t2)': ('t5','t2'),   # z6 - z3  -> delta_{3,6}
}
A = []
print("\nA (polar divisor of omega), from denominator factors of I(a):")
for f,(u,v) in A_factors.items():
    d = dv(u,v); A.append(d)
    print(f"   {f:9s} -> z-collision {u},{v} -> delta_{{{','.join(map(str,d))}}}")
A = [canon(s) for s in A]
# cross-check against the b_ij subscripts in eq (I1)/(b-param): b_24,b_14,b_57,b_35,b_36
b_subscripts = [(2,4),(1,4),(5,7),(3,5),(3,6)]
A_from_b = sorted(canon(s) for s in b_subscripts)
print("   b_ij subscripts in (I1):", b_subscripts)
print("   MATCH A == {delta_ij : ij in b-subscripts}? ", sorted(A)==A_from_b)

# ---- B: facets of the associahedron = consecutive intervals in cyclic order 1..8
def consecutive_intervals():
    out=set()
    seq=list(range(1,n+1))
    for k in range(2,n-1):
        for start in range(n):
            S=[seq[(start+j)%n] for j in range(k)]
            out.add(canon(S))
    return sorted(out, key=lambda t:(len(t),t))
B = consecutive_intervals()
print(f"\nB (Zariski closure of boundary of the domain simplex) = associahedron facets")
print(f"   #B = {len(B)}   (chords of the octagon = n(n-3)/2 = {n*(n-3)//2})")
# the 6 affine facets t1=0,t1=t2,...,t5=1 are the length-2 consecutive pairs among these:
affine = [dv('t1','0') if False else canon({1,2})]  # placeholder, list them explicitly
affine = [canon({1,2}),canon({2,3}),canon({3,4}),canon({4,5}),canon({5,6}),canon({6,7})]
print("   6 affine facets (t1=0,t1=t2,t2=t3,t3=t4,t4=t5,t5=1):",
      [''.join(map(str,d)) for d in affine])

# A ∩ B ?
AB = [d for d in A if d in set(B)]
print("\nA ∩ B (polar divisors that are also domain facets):",
      [''.join(map(str,d)) for d in AB] or "none  (A is disjoint from the domain facets)")

# ---- codim-2 strata inside A: pairs of COMPATIBLE (meeting) A-divisors ----
print("\nCodim-2 strata A∩A  (compatible pairs of polar divisors -> Q(-2) candidates):")
strata=[]
for S,T in combinations(A,2):
    if compatible(S,T):
        strata.append((S,T))
        # the deeper set they cut out
        s,t=frozenset(S),frozenset(T)
        print(f"   delta_{{{''.join(map(str,S))}}} ∩ delta_{{{''.join(map(str,T))}}}"
              f"   (disjoint pairs -> transverse crossing)")
print(f"   => {len(strata)} codim-2 A∩A strata carrying candidate Q(-2) classes")
print(f"   (gr^W_4 M has rank 1, so relations cut these {len(strata)} down to a single")
print(f"    primitive generator gamma_2; its 2-divisibility is the H2 index question.)")

# incompatible (crossing) A-pairs, for the record
cross=[(S,T) for S,T in combinations(A,2) if not compatible(S,T)]
print("   crossing (non-meeting) A-pairs:",
      [f"{''.join(map(str,S))}|{''.join(map(str,T))}" for S,T in cross])
