#!/usr/bin/env python3
"""
h2_signs_complex.py  --  [COMPUTED, exact integer SNF + parity]

The B-relative cellular boundary-sign computation for the p=2 lattice index
(residual CR-4 of H2_LATTICE.md).

SETUP (all from h2_signs_strata.py, exact Keel combinatorics):
  bi-arrangement (A,B) on Mbar_{0,8}, A = {d24,d14,d57,d35,d36} (color lambda),
  B = 20 associahedron facets (color mu).  The weight-4 = Q(-2) piece gr^W_4 is
  the k=2 truncation of Dupont's OS bicomplex (arXiv:1410.6348): it is assembled
  from the 7 transverse codim-2 A-strata Z (each ~ Mbar_{0,6}), glued along the
  2 codim-3 A-triples, with the B-columns doing the intra-Mbar_{0,6} reduction.

THE INDEX, REFRAMED (the clean rigorous handle -- see H2_SIGNS.md sec.3):
  The exact de Rham double residues (H2_LATTICE sec.5.5-B) are all +-1 (2-adic
  UNITS).  So a *single* normal torus T_Z pairs with the integral de Rham
  generator omega_2 to a unit.  Hence:
      index 1  <=>  some single torus T_Z is itself an integral relative cycle;
      index 2  <=>  no single T_Z is a relative cycle, and every integral
                    relative cycle sum_Z c_Z T_Z has  f(c) := sum_Z eps_Z c_Z  EVEN,
  where eps_Z in {+1,-1} are exactly the de Rham residue signs.  The index is
  [ Z : f(L) ] with L = lattice of integral relative cycles.

This script:
  (1) fixes the strata/triples/residue-signs data;
  (2) builds the A-incidence boundary d: C2(7 strata) -> C1(2 triples) under an
      EXPLICIT orientation convention [CONVENTION-RISK, tagged], computes SNF and
      the cycle lattice L0 = ker(d), and the residue-functional image f(L0);
  (3) repeats for the abstract-simplicial sign convention, to expose convention
      dependence;
  (4) p=3 discharge: shows every elementary divisor is a power of 2 (no 3 can
      appear) -- DERIVED, matching the measured index-1-at-3;
  (5) reports what is and is NOT pinned, feeding the obstruction map.
"""
import numpy as np
from sympy import Matrix, ZZ

# --- strata (order fixed) ----------------------------------------------------
# Z1=(24,57) Z2=(24,35) Z3=(24,36) Z4=(14,57) Z5=(14,35) Z6=(14,36) Z7=(57,36)
strata = ['24^57','24^35','24^36','14^57','14^35','14^36','57^36']
# de Rham residue signs eps_Z (H2_LATTICE sec.5.5-B table), same stratum order:
eps = {  '24^57':+1, '24^35':+1, '24^36':+1,
         '14^57':-1, '14^35':+1, '14^36':+1, '57^36':+1 }
eps_vec = np.array([eps[s] for s in strata])

# codim-3 triples and the 3 strata each links (from h2_signs_strata.py):
# T1 = {24,57,36} links Z1(24,57),Z3(24,36),Z7(57,36)
# T2 = {14,57,36} links Z4(14,57),Z6(14,36),Z7(57,36)
triples = {
  'T1={24,57,36}': ['24^57','24^36','57^36'],
  'T2={14,57,36}': ['14^57','14^36','57^36'],
}

idx = {s:i for i,s in enumerate(strata)}

def boundary_matrix(sign_rule):
    """
    d : C2 (7 strata) -> C1 (2 triples).  Entry d[t, Z] = orientation sign of the
    codim-3 face T inside the boundary of the cell of stratum Z, or 0 if T not a
    face of Z.  sign_rule(triple_label, members, Z) -> +-1.
    """
    d = np.zeros((len(triples), len(strata)), dtype=int)
    for ti,(tlab, members) in enumerate(triples.items()):
        for Z in members:
            d[ti, idx[Z]] = sign_rule(tlab, members, Z)
    return d

def snf_diag(M):
    """Smith normal form diagonal (elementary divisors) over Z via sympy."""
    if M.size == 0:
        return []
    S = Matrix(M.tolist())
    from sympy.matrices.normalforms import smith_normal_form
    D = smith_normal_form(S, domain=ZZ)
    diag = [D[i,i] for i in range(min(D.shape))]
    return [int(x) for x in diag]

def integer_kernel(M):
    """Basis (rows) of the integral kernel of the map c |-> M c  (M: r x n)."""
    if M.shape[0]==0:
        return np.eye(M.shape[1], dtype=int)
    S = Matrix(M.tolist())
    ns = S.nullspace()
    if not ns:
        return np.zeros((0, M.shape[1]), dtype=int)
    # clear denominators to integer primitive vectors
    from sympy import lcm, Rational
    rows=[]
    for v in ns:
        den = 1
        for x in v:
            den = np.lcm(den, Rational(x).q)
        w = [int(Rational(x*den)) for x in v]
        g = np.gcd.reduce([abs(x) for x in w if x!=0]) or 1
        rows.append([x//g for x in w])
    return np.array(rows, dtype=int)

def functional_image(kernel_rows, fvec):
    """Image f(L) subgroup of Z = gcd of f on a kernel basis -> the index [Z:f(L)]."""
    if kernel_rows.shape[0]==0:
        return 0
    vals = [int(np.dot(r, fvec)) for r in kernel_rows]
    vals = [v for v in vals if v!=0]
    if not vals:
        return 0
    return int(np.gcd.reduce([abs(v) for v in vals]))

print("="*74)
print("STRATA:", strata)
print("de Rham residue signs eps_Z:", [eps[s] for s in strata])
print("triples:", {k:v for k,v in triples.items()})
print("="*74)

# --- Convention I: abstract simplicial (as in h2_p2_Betti.sage) --------------
# order the 3 members of each triple; boundary sign = (-1)^position, the standard
# alternating simplicial boundary of the 2-simplex [Z_a,Z_b,Z_c].
def sign_simplicial(tlab, members, Z):
    pos = members.index(Z)
    return (-1)**pos
dI = boundary_matrix(sign_simplicial)
print("\n[CONVENTION I: abstract simplicial alternating signs]")
print("d (2 triples x 7 strata):\n", dI)
print("SNF(d):", snf_diag(dI))
kerI = integer_kernel(dI)
print("rank ker(d) =", kerI.shape[0], " (integral cycle lattice L0 rank)")
print("residue-functional image f(L0) = %d*Z  => index at this level = %d"
      % (functional_image(kerI, eps_vec), functional_image(kerI, eps_vec)))

# --- Convention II: all-+1 (coherent orientation of the shared facet) --------
# every stratum induces the SAME orientation on the shared codim-3 facet.
def sign_plus(tlab, members, Z):
    return +1
dII = boundary_matrix(sign_plus)
print("\n[CONVENTION II: coherent (all +1) facet orientation]")
print("d:\n", dII)
print("SNF(d):", snf_diag(dII))
kerII = integer_kernel(dII)
print("rank ker(d) =", kerII.shape[0])
print("residue-functional image f(L0) = %d*Z  => index = %d"
      % (functional_image(kerII, eps_vec), functional_image(kerII, eps_vec)))

# --- p = 3 discharge ----------------------------------------------------------
print("\n" + "="*74)
print("p=3 DISCHARGE (DERIVED):")
alldiag = snf_diag(dI) + snf_diag(dII)
print("  every incidence entry is in {0,+-1}; boundary maps have entries +-1,")
print("  so all Smith elementary divisors are products of the SAME primes as the")
print("  2x2 minors, which are in {0,+-1,+-2}.  Observed elementary divisors:",
      sorted(set(abs(x) for x in alldiag)))
print("  => no factor of 3 can occur at ANY sign convention: 3-index is 1. [matches measurement]")

# --- the decisive sub-question: do Z2,Z5 (no codim-3 link) carry cycles? -----
print("\n" + "="*74)
print("DECISIVE STRUCTURAL POINT (feeds the obstruction map):")
print("  Z2=(24,35), Z5=(14,35) have NO residual A-divisor -> they are ISOLATED")
print("  in the A-incidence: e_{Z2}, e_{Z5} lie in ker(d) automatically.")
print("  f(e_Z2)=eps=%+d, f(e_Z5)=eps=%+d  -> both ODD." % (eps['24^35'], eps['14^35']))
print("  Hence IF the isolated tori T_Z2,T_Z5 are genuine INTEGRAL RELATIVE")
print("  CYCLES, the residue functional hits 1 and the index is 1, NOT 2.")
print("  The measured index 2 therefore REQUIRES that T_Z2,T_Z5 are NOT relative")
print("  cycles by themselves: their torus-over-cell has boundary on the")
print("  UNCOLORED generic facets C (facets of the Mbar_0,6 cell that are boundary")
print("  divisors of Mbar_0,8 lying in neither A nor B).  Closing them up mod B")
print("  forces gluing to OTHER codim-2 strata across the C-facets -> pulls in the")
print("  full Mbar_0,8 codim-2 stratification.  THIS is the precise obstruction.")
