#!/usr/bin/env python3
"""
h2_symmetry.py  --  [COMPUTED]
Two facts about the order-2 motivic involution i_1 at the symmetric point:

 (I)  i_1 is NOT a marked-point permutation: among the 16 octagon dihedral
      symmetries of the domain (cyclic order 1..8), only the identity preserves
      the polar divisor A={d24,d14,d57,d35,d36}.  So the p=2 refinement, if real,
      is NOT a cheap S_8-orbit artifact.

 (II) i_1 IS visible in the cubical chart (I-a) as x_j -> x_{6-j} (x1<->x5,
      x2<->x4, x3 fixed), where it PAIRS the polar denominator factors
      {1-x1x2, 1-x2x3, 1-x3x4, 1-x4x5} in two 2-cycles.  Since i_1 fixes the
      integrand omega (hence the de Rham class omega_2) and the domain gamma_1,
      the natural period-carrying weight-4 Betti class is the i_1-invariant sum
      T + i_1 T of a torus in a size-2 orbit.  If T and i_1 T project to the
      same rank-1 gr^W_4 generator g, then that class = 2g, i.e. g = gamma_2/2:
      index 2 at p=2, and -- i_1 having order 2 -- NOTHING at p=3.
"""
from itertools import combinations

# ---------- (I) marked-point octagon symmetries (recap of the negative result) ----------
n=8; U=frozenset(range(1,n+1))
def canon(S):
    S=frozenset(S); Sc=U-S
    return min((tuple(sorted(S)),tuple(sorted(Sc))),key=lambda t:(len(t),t))
A={canon(p) for p in [(2,4),(1,4),(5,7),(3,5),(3,6)]}
def rot(k): return {i:(((i-1)+k)%n)+1 for i in range(1,n+1)}
def ref(k): return {i:(((k-(i-1))%n)+1) for i in range(1,n+1)}
group=[('r%d'%k,rot(k)) for k in range(n)]+[('s%d'%k,ref(k)) for k in range(n)]
def ap(p,S): return canon({p[x] for x in S})
keep=[nm for nm,p in group if {ap(p,S) for S in A}==A]
print("(I) octagon dihedral symmetries (order 16) preserving A:", keep,
      "-> order", len(keep), "(only identity: i_1 is NOT a point permutation)\n")

# ---------- (II) cubical chart: i_1 = (x1 x5)(x2 x4), x3 fixed ----------
# polar factors of omega in (I-a): P_k = {1 - x_k x_{k+1} = 0}, k=1..4
factors = {1:('x1','x2'), 2:('x2','x3'), 3:('x3','x4'), 4:('x4','x5')}
i1 = {'x1':'x5','x2':'x4','x3':'x3','x4':'x2','x5':'x1'}
def act_factor(k):
    a,b=factors[k]; ia,ib=i1[a],i1[b]
    for kk,(c,d) in factors.items():
        if {ia,ib}=={c,d}: return kk
    return None
print("(II) i_1 = (x1 x5)(x2 x4) on the 4 polar factors P_k = {1-x_k x_{k+1}}:")
orb=[]; seen=set()
for k in factors:
    j=act_factor(k)
    print(f"     P{k}={{1-{factors[k][0]}{factors[k][1]}}}  ->  P{j}={{1-{factors[j][0]}{factors[j][1]}}}")
for k in factors:
    if k in seen: continue
    j=act_factor(k); o={k,j}; seen|=o; orb.append(sorted(o))
print("     orbits on polar factors:", orb, " (two 2-cycles: P1<->P4, P2<->P3)\n")

# codim-2 strata in the cubical chart = transverse pairs (disjoint variable sets)
def vars_of(k): return set(factors[k])
strata=[(a,b) for a,b in combinations(factors,2) if not (vars_of(a)&vars_of(b))]
print("     transverse codim-2 strata P_a ∩ P_b (disjoint variable pairs):")
strata_set={frozenset(s) for s in strata}
seen=set(); sizes=[]
for a,b in strata:
    ia,ib=act_factor(a),act_factor(b)
    img=frozenset([ia,ib])
    print(f"        {{P{a},P{b}}} -> {{P{sorted(img)[0]}, P{sorted(img)[1]}}}"
          f"{'' if img in strata_set else '  [out]'}")
for s in strata:
    fs=frozenset(s)
    if fs in seen: continue
    a,b=s; img=frozenset([act_factor(a),act_factor(b)])
    o={fs};
    while img not in o and img in strata_set:
        o.add(img); x,y=sorted(img); img=frozenset([act_factor(x),act_factor(y)])
    seen|=o; sizes.append(len(o))
print("     orbit sizes on codim-2 strata:", sorted(sizes,reverse=True))
print("     => a size-2 orbit exists.  i_1-invariant torus class T+i_1T = 2*(primitive)")
print("        forces gamma_2/2 in L: index 2 at p=2, none at p=3 (order-2 group).")
