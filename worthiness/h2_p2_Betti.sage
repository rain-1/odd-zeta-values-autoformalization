# h2_p2_Betti.sage  --  [COMPUTED, exact integer SNF]
# Computation A of the p=2 resolution: the Betti-side torus 2-divisibility.
#
# The weight-4 piece gr^W_4 M (rank 1) is carried by the 7 transverse codim-2
# strata inside A.  Their incidence structure (the "nested-set" / nerve complex
# of the polar arrangement A) is an honest integer chain complex; the integral
# Betti relations among the 7 torus classes are governed by the Gysin/boundary
# maps of this complex together with the B-relative corrections.  We assemble
# the explicit integer boundary matrices in the boundary-divisor basis and read
# the 2-divisibility off the Smith normal forms.
#
# Arrangement data (from h2_divisors.py):
#   5 codim-1 A-divisors : f1=d24, f2=d14, f3=d57, f4=d35, f5=d36
#   7 codim-2 strata (compatible=transverse pairs):
#       s1=f1f3, s2=f1f4, s3=f1f5, s4=f2f3, s5=f2f4, s6=f2f5, s7=f3f5
#   2 codim-3 strata (compatible triples):
#       T1=f1f3f5, T2=f2f3f5
# [CONVENTION-RISK] simplicial orientation: faces ordered by index; boundary
#   with the standard alternating sign.  The 2-divisibility (SNF elementary
#   divisors) is orientation-independent.

vertices = ['f1','f2','f3','f4','f5']
edges = [('f1','f3'),('f1','f4'),('f1','f5'),('f2','f3'),('f2','f4'),('f2','f5'),('f3','f5')]
tris  = [('f1','f3','f5'),('f2','f3','f5')]

vi = {v:i for i,v in enumerate(vertices)}
ei = {e:i for i,e in enumerate(edges)}

# boundary d1: C1(edges) -> C0(vertices)
d1 = matrix(ZZ, len(vertices), len(edges))
for j,(a,b) in enumerate(edges):
    d1[vi[b],j] += 1
    d1[vi[a],j] -= 1

# boundary d2: C2(tris) -> C1(edges)
d2 = matrix(ZZ, len(edges), len(tris))
for j,(a,b,c) in enumerate(tris):
    # d(abc) = (bc) - (ac) + (ab)
    for face,sign in [((b,c),1),((a,c),-1),((a,b),1)]:
        d2[ei[face],j] += sign

print("Incidence chain complex of the polar arrangement A:")
print("  C0=%d vertices, C1=%d edges, C2=%d triangles" % (len(vertices),len(edges),len(tris)))
print("  Euler char =", len(vertices)-len(edges)+len(tris))

print("\nd1 (edges->vertices):\n", d1)
print("\nd2 (triangles->edges):\n", d2)

# integral simplicial homology via Smith normal form
def homology(dk, dkp1, name):
    # H_k = ker(dk)/im(dk+1)
    if dk is None:
        ker_rank = dkp1.nrows()  # top: C0, dk=0
        Z = ZZ**dkp1.nrows()
        rk_ker = dkp1.nrows()
    return None

# Use Sage's built-in chain complex homology (with torsion)
C = ChainComplex({1:d1, 2:d2}, degree=-1)
print("\nIntegral homology of the A-nerve complex:")
for k in (0,1,2):
    H = C.homology(k)
    print("  H_%d =" % k, H)

print("\nSmith normal forms (elementary divisors):")
print("  SNF(d1) diag:", d1.smith_form()[0].diagonal())
print("  SNF(d2) diag:", d2.smith_form()[0].diagonal())

# ---- the Gysin/relation matrix for the rank-1 gr^W_4 collapse ----
# The 7 tori map to rank-1 gr^W_4.  The relations visible from the arrangement:
# each codim-3 triple T=(a,b,c) links its three codim-2 sub-strata; the transverse
# local model 𝔾_m^3 gives NO Orlik-Solomon relation (the three 2-tori are
# independent in H_2((S^1)^3)=Z^3).  So the pure A-arrangement imposes only the
# nerve boundary d2 as candidate relations.  Print the cokernel of d2^T acting on
# the 7-dim torus space (the "naive" relation lattice from triples):
R = d2.transpose()   # 2 x 7  : each triple gives one alternating relation
print("\nRelation matrix from the 2 codim-3 triples (alternating torus sums):")
print(R)
M7 = R
S = M7.smith_form()[0]
print("SNF of the triple-relation matrix diag:", [S[i,i] for i in range(min(S.nrows(),S.ncols()))])
coker = (ZZ**7 / M7.transpose().image()) if False else None
print("cokernel Z^7 / (rows of R):",
      "elementary divisors", [d for d in M7.elementary_divisors() if d!=1])
