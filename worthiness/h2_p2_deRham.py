#!/usr/bin/env python3
"""
h2_p2_deRham.py  --  [COMPUTED, exact - sympy]
Computation B of the p=2 resolution.

Iterated (double) residue of the symmetric integrand log-form
    omega = dt1^dt2^dt3^dt4^dt5 / ( f1 f2 f3 f4 f5 ),
    f1=t3-t1 (d24), f2=t3 (d14), f3=1-t4 (d57), f4=t4-t2 (d35), f5=t5-t2 (d36),
along each of the 7 transverse codim-2 strata (compatible pairs of A-divisors).

Each double residue is Res_{fb=0} Res_{fa=0} omega, a 3-form on the 3-dim
stratum.  We record its EXACT rational normalization relative to the standard
cellular 3-form on that stratum (the product of the three surviving linear
factors in the denominator).  The 2-adic valuation of these rationals is the
de Rham contribution to the p=2 factor:
  * all rationals 2-adic UNITS  => de Rham class is 2-integral => the measured
    factor 2 must live on the BETTI side (H2a, index 2).
  * some rational = (odd)/2      => the 2 lives on the DE RHAM side (H1), and
    H2's Betti index is 1.

Residue convention [CONVENTION-RISK, stated]:
  orientation dt1^dt2^dt3^dt4^dt5 (increasing index).  For a simple pole f=0,
  write f = c*(v - phi) with v the eliminated variable (lowest-index variable
  occurring in f); then Res_{f=0}[ (dv^rest)/f ] = (1/c) * rest|_{v=phi}, after
  moving dv to the front (sign = parity of its position).  We track the sign but
  the VERDICT depends only on the 2-adic valuation |.|_2 of the coefficient,
  which is sign-independent.
"""
import sympy as sp

t1,t2,t3,t4,t5 = sp.symbols('t1 t2 t3 t4 t5')
V = [t1,t2,t3,t4,t5]
# polar factors  (name -> (divisor label, linear expression))
F = {
 'f1': ('d24', t3 - t1),
 'f2': ('d14', t3),
 'f3': ('d57', 1 - t4),
 'f4': ('d35', t4 - t2),
 'f5': ('d36', t5 - t2),
}
# the 7 compatible (transverse) pairs, from h2_divisors.py
pairs = [('f1','f3'),('f1','f4'),('f1','f5'),('f2','f3'),('f2','f4'),('f2','f5'),('f3','f5')]

def residue(coeff, wedge_vars, denom_factors, f):
    """
    Res of  coeff * (wedge of wedge_vars, in that order) / prod(denom_factors)
    along f=0.  Returns (new_coeff, new_wedge_vars, new_denom_factors).
    f must be linear; eliminate the lowest-index variable it contains.
    """
    fvars = [v for v in wedge_vars if f.has(v)]
    if not fvars:
        raise ValueError("f does not involve any wedge variable: cannot take residue")
    v = fvars[0]                              # eliminate this variable
    c = sp.diff(f, v)                         # f = c*v + (rest);  c = +-1 here
    phi = sp.solve(sp.Eq(f,0), v)[0]          # v = phi
    pos = wedge_vars.index(v)                 # position of dv in the wedge
    sign = (-1)**pos                          # cost of moving dv to the front
    new_wedge = [w for w in wedge_vars if w != v]
    new_coeff = sp.simplify(coeff * sign / c)
    # restrict remaining data to v = phi
    new_coeff = sp.simplify(new_coeff.subs(v, phi))
    new_denoms = [sp.simplify(g.subs(v, phi)) for g in denom_factors]
    return new_coeff, new_wedge, new_denoms

print("Double residues of omega along the 7 transverse strata:\n")
results = {}
for a,b in pairs:
    lab = F[a][0]+"^"+F[b][0]
    denom = [F['f1'][1],F['f2'][1],F['f3'][1],F['f4'][1],F['f5'][1]]
    # remove the two factors we residue along; keep the other three
    keep = [F[k][1] for k in F if k not in (a,b)]
    # Res along fa then fb, starting from coeff 1 / (product of the OTHER three)
    coeff = sp.Integer(1)
    wedge = list(V)
    # residue along fa
    coeff, wedge, keep = residue(coeff, wedge, keep, F[a][1])
    # residue along fb
    coeff, wedge, keep = residue(coeff, wedge, keep, F[b][1])
    coeff = sp.nsimplify(sp.simplify(coeff))
    # the surviving 3-form: coeff * (wedge of `wedge`) / prod(keep)
    denom_str = "*".join("("+str(sp.factor(g))+")" for g in keep)
    wedge_str = "^".join(str(w) for w in wedge)
    # normalization relative to the cellular form d(wedge)/prod(keep):
    # coeff should be a rational; record it and its 2-adic valuation
    rat = sp.Rational(coeff) if coeff.is_rational else coeff
    results[lab] = rat
    v2 = sp.factorint(sp.Rational(rat)).get(2,0) if rat!=0 and rat.is_rational else None
    print(f"  {lab:10s}: Res = ({rat}) * [ d{wedge_str} / {denom_str} ]   "
          f"v2(coeff)={v2}")

print("\n2-adic valuations of the 7 de Rham residue coefficients:")
vals = {k:(sp.factorint(sp.Rational(v)).get(2,0) if v!=0 else None) for k,v in results.items()}
print("  ", {k:vals[k] for k in results})
allunit = all((v==0) for v in vals.values() if v is not None)
print(f"\n  all coefficients are 2-adic units (v2=0)? {allunit}")
if allunit:
    print("  => DE RHAM SIDE CARRIES NO FACTOR 2.  By the measured product (=2),")
    print("     the factor 2 lives on the BETTI side: H2a, integral Betti index 2 at p=2.")
else:
    print("  => a residue coefficient has v2!=0: the factor 2 (partly) de Rham; see values.")
