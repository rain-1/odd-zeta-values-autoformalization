#!/usr/bin/env python3
"""
h2_signs_strata.py  --  [COMBINATORICS, exact — Keel intersection poset]

Groundwork for the B-relative cellular boundary-sign computation (CR-4 of
H2_LATTICE.md).  For the bi-arrangement (A,B) on Mbar_{0,8}:

  A = {d24, d14, d57, d35, d36}          (polar divisors of omega, color lambda)
  B = 20 associahedron facets            (domain boundary, color mu)

the weight-4 (Tate twist -2) piece gr^W_4 H^5(Mbar_{0,8} \\ A, B) is built,
per Dupont's OS-bicomplex (arXiv:1410.6348, Thm 1.3:
gr^W_{2k}H^r = H_{2k-r}(^{(k)}A_.)(-k)) with k=2, from strata containing EXACTLY
TWO A-divisors -- i.e. the 7 transverse codim-2 strata Z = d_S ∩ d_T -- decorated
by any compatible set of B-divisors.

Each such Z ≅ Mbar_{0,6}.  This script produces, for each of the 7 strata, the
UNAMBIGUOUS combinatorial data:
  * the 6 special points of the Mbar_{0,6} (4 surviving markings + 2 nodes),
  * the induced cyclic order on those 6 points (needed to know the associahedron
    'domain' cell and its B-facets),
  * which B-divisors of Mbar_{0,8} restrict to boundary divisors of Z,
  * which remaining A-divisors still meet Z (the codim-3 links / residual polar
    arrangement on Z),
  * the two codim-3 triples and which strata they link.
All from Keel's rule: d_S, d_T meet iff S,T are nested, disjoint, or complementary.
"""
from itertools import combinations

n = 8
U = frozenset(range(1, n+1))
CYCLE = list(range(1, n+1))  # octagon cyclic order 1,2,...,8

def canon(S):
    S = frozenset(S)
    Sc = U - S
    return min((tuple(sorted(S)), tuple(sorted(Sc))), key=lambda t: (len(t), t))

def compatible(S, T):
    S, T = frozenset(S), frozenset(T)
    return S <= T or T <= S or (S & T == frozenset()) or (S | T == U)

# ---- A and B ----------------------------------------------------------------
A = [canon(s) for s in [(2,4),(1,4),(5,7),(3,5),(3,6)]]
Alabel = {canon((2,4)):'d24', canon((1,4)):'d14', canon((5,7)):'d57',
          canon((3,5)):'d35', canon((3,6)):'d36'}

def consecutive_intervals():
    out = set()
    for k in range(2, n-1):
        for start in range(n):
            S = [CYCLE[(start+j) % n] for j in range(k)]
            out.add(canon(S))
    return sorted(out, key=lambda t: (len(t), t))
B = consecutive_intervals()
Bset = set(B)
print("A =", [Alabel[a] for a in A])
print("#B =", len(B))

# ---- the 7 transverse codim-2 strata ----------------------------------------
pairs = []
for S, T in combinations(A, 2):
    if compatible(S, T):
        pairs.append((S, T))
print("\n# transverse codim-2 strata (Mbar_0,6 each):", len(pairs))

def stratum_points(S, T):
    """
    Z = d_S ∩ d_T with S,T disjoint 2-element sets.  Two bubbles carry S and T;
    on the main (Mbar_0,6) component the special points are:
      the 4 surviving markings (U \\ (S∪T)) and 2 nodes n_S, n_T.
    The induced CYCLIC ORDER on the main component: walk the octagon 1..8; each
    bubble collapses its two points to a single node inserted at their position.
    Since S,T are 2-element and we go round the octagon, replace the block of
    each pair by its node label, preserving cyclic order of everything else.
    Returns (points_list_in_cyclic_order, node_of).
    """
    S = tuple(sorted(S)); T = tuple(sorted(T))
    nodeS = 'nS'; nodeT = 'nT'
    # map each octagon position to a token; a pair's two points -> its node,
    # but only ONE node token appears (at the location of the pair's members).
    # Build cyclic sequence, replacing members of S by nodeS (dedup consecutive
    # in cyclic sense is not required: the node sits where the bubble attaches).
    seq = []
    usedS = usedT = False
    for p in CYCLE:
        if p in S:
            if not usedS:
                seq.append(nodeS); usedS = True
            # second member of S contributes nothing new (same node)
        elif p in T:
            if not usedT:
                seq.append(nodeT); usedT = True
        else:
            seq.append(p)
    return seq, {nodeS: S, nodeT: T}

def restrict_divisor_to_stratum(D, S, T, pts):
    """
    A boundary divisor d_D of Mbar_0,8 (D a subset) that is compatible with both
    d_S and d_T and distinct from them restricts to a boundary divisor of the
    Mbar_0,6 component, provided D 'lives on' the main component.  Compute the
    induced subset on the 6-point set {surviving markings + nodes nS,nT}:
      a marking p in D  -> p ;   S ⊆ D -> node nS ;  T ⊆ D -> node nT.
    Return the induced subset (as a frozenset of point-tokens) if D restricts to
    a genuine boundary divisor of the Mbar_0,6 (i.e. 2 <= |induced| <= 4), else None.
    """
    Sset, Tset = frozenset(S), frozenset(T)
    Dset = frozenset(D)
    # D must be compatible with S and T (nested/disjoint/complementary)
    if not (compatible(Dset, Sset) and compatible(Dset, Tset)):
        return None
    # induced subset on the 6 special points
    ind = set()
    # handle S: if S ⊆ D put nS; if S ∩ D = ∅ nothing; if crossing -> not on main
    for pr, node in ((Sset, 'nS'), (Tset, 'nT')):
        if pr <= Dset:
            ind.add(node)
        elif pr & Dset == frozenset():
            pass
        else:
            return None  # partial -> the divisor passes through the bubble, not a main-component facet
    for p in Dset:
        if p not in Sset and p not in Tset:
            ind.add(p)
    tokens = set(pts)
    ind = frozenset(ind)
    indc = frozenset(tokens - ind)
    # boundary divisor of Mbar_0,6 needs 2 <= |ind| <= 4 (n'=6, 2<=k<=4), and canonize
    k = min(len(ind), len(indc))
    if k < 2:
        return None
    # canonical (smaller side)
    return frozenset(min((ind, indc), key=lambda x: (len(x), tuple(sorted(map(str, x))))))

print("\n" + "="*78)
for idx, (S, T) in enumerate(pairs, 1):
    lab = Alabel[S] + "∩" + Alabel[T]
    pts, nodes = stratum_points(S, T)
    print(f"\n[Z{idx}] {lab:12s}  Mbar_0,6 points (cyclic): {pts}")
    print(f"        nodes: nS={nodes['nS']}, nT={nodes['nT']}")
    # remaining A-divisors meeting Z (codim-3 links)
    remA = []
    for D in A:
        if D == S or D == T:
            continue
        r = restrict_divisor_to_stratum(D, S, T, pts)
        if r is not None:
            remA.append((Alabel[D], tuple(sorted(map(str, r)))))
    print(f"        residual A-divisors meeting Z (codim-3 links): {remA}")
    # B-divisors restricting to Mbar_0,6 boundary facets
    Bres = []
    for D in B:
        r = restrict_divisor_to_stratum(D, S, T, pts)
        if r is not None:
            Bres.append(tuple(sorted(map(str, r))))
    Bres_u = sorted(set(Bres), key=lambda x: (len(x), x))
    print(f"        # distinct B-facets on Z = {len(Bres_u)}")
    for b in Bres_u:
        print(f"            {b}")

# ---- the 2 codim-3 triples and the strata they link -------------------------
print("\n" + "="*78)
print("Codim-3 triples (compatible A-triples) and the 3 codim-2 strata each links:")
triples = []
for a, b, c in combinations(A, 3):
    if compatible(a, b) and compatible(a, c) and compatible(b, c):
        triples.append((a, b, c))
for tr in triples:
    labs = [Alabel[x] for x in tr]
    subpairs = [tuple(sorted((Alabel[x], Alabel[y]))) for x, y in combinations(tr, 2)]
    print(f"  triple {labs}: links strata {subpairs}")
print(f"\n# codim-3 triples = {len(triples)}")
