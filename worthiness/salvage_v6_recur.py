"""V6(a,b): recover the common third-order recurrence for (q_n,p_n,p̃_n) and the
normalized (Q_n,P_n,P̂_n), by exact-fit (route ii).

Method: an order-3 recurrence  Σ_{i=0}^3 c_i(n) X_{n+i} = 0  with c_i polynomials
of degree ≤ D.  Homogeneous linear in the {c_{i,d}}.  We (1) find the minimal D
and the nullspace mod a large prime using ALL THREE sequences simultaneously
(this pins the operator: 3 independent solutions), (2) reconstruct the rational
coefficients by CRT + rational reconstruction over several primes, (3) VERIFY the
reconstructed recurrence annihilates all three exact ladders at every offset.

Usage: python3 salvage_v6_recur.py
"""

from fractions import Fraction
import sympy as sp
from salvage_data import triple, get_all

PRIMES = [2 ** 61 - 1, (1 << 61) - 99, 2305843009213693921,
          2305843009213693967, 2305843009213693669]


def frac_mod(fr, p):
    return (fr.numerator % p) * pow(fr.denominator % p, -1, p) % p


def build_rows_modp(seqs, D, nlo, nhi, p):
    """Rows of the homogeneous system mod p. Unknowns: c[i][d], i=0..3,d=0..D."""
    ncols = 4 * (D + 1)
    rows = []
    for X in seqs:            # each X: dict n->Fraction
        for n in range(nlo, nhi + 1):
            if any((n + i) not in X for i in range(4)):
                continue
            xr = [frac_mod(X[n + i], p) for i in range(4)]
            row = [0] * ncols
            npow = [pow(n % p, d, p) for d in range(D + 1)]
            for i in range(4):
                for d in range(D + 1):
                    row[i * (D + 1) + d] = xr[i] * npow[d] % p
            rows.append(row)
    return rows, ncols


def nullspace_modp(rows, ncols, p):
    """Return list of basis nullvectors (each length ncols) mod p."""
    M = [r[:] for r in rows]
    nr = len(M)
    pivcol = {}
    r = 0
    for c in range(ncols):
        piv = None
        for rr in range(r, nr):
            if M[rr][c] % p != 0:
                piv = rr
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], -1, p)
        M[r] = [(x * inv) % p for x in M[r]]
        for rr in range(nr):
            if rr != r and M[rr][c] % p != 0:
                f = M[rr][c]
                M[rr] = [(a - f * b) % p for a, b in zip(M[rr], M[r])]
        pivcol[c] = r
        r += 1
        if r == nr:
            break
    free = [c for c in range(ncols) if c not in pivcol]
    basis = []
    for fc in free:
        vec = [0] * ncols
        vec[fc] = 1
        for c, rr in pivcol.items():
            vec[c] = (-M[rr][fc]) % p
        basis.append(vec)
    return basis


def find_min_degree(seqs, nlo, nhi, p=PRIMES[0], Dmax=14):
    for D in range(3, Dmax + 1):
        rows, ncols = build_rows_modp(seqs, D, nlo, nhi, p)
        if len(rows) < ncols + 3:
            continue
        basis = nullspace_modp(rows, ncols, p)
        if basis:
            return D, len(basis), ncols
    return None, 0, 0


def rational_reconstruct(a, m):
    """Wang's rational reconstruction of a mod m."""
    if a == 0:
        return Fraction(0)
    r0, r1 = m, a % m
    s0, s1 = 0, 1
    bound = int((m // 2) ** 0.5)
    while r1 > bound:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        s0, s1 = s1, s0 - q * s1
    if s1 == 0 or abs(s1) > bound:
        return None
    return Fraction(r1, s1)


def reconstruct_solution(seqs, D, nlo, nhi):
    """CRT + rational reconstruction of the (assumed 1-dim) nullspace."""
    # pick a normalization column: the highest-degree coeff of c_3 (i=3)
    norm_col = 3 * (D + 1) + D
    residues = {}          # col -> list of (value mod p)
    mods = []
    for p in PRIMES:
        rows, ncols = build_rows_modp(seqs, D, nlo, nhi, p)
        basis = nullspace_modp(rows, ncols, p)
        if len(basis) != 1:
            return None, len(basis)
        vec = basis[0]
        if vec[norm_col] % p == 0:
            # renormalize to first nonzero
            nz = next(i for i in range(ncols) if vec[i] % p != 0)
            norm_col2 = nz
        else:
            norm_col2 = norm_col
        inv = pow(vec[norm_col2], -1, p)
        nvec = [(x * inv) % p for x in vec]
        for c in range(ncols):
            residues.setdefault(c, []).append(nvec[c])
        mods.append(p)
    # CRT each column then rational reconstruct
    M = 1
    for p in mods:
        M *= p
    coeffs = {}
    for c in range(ncols):
        # CRT
        x = 0
        for p, res in zip(mods, residues[c]):
            Mi = M // p
            x = (x + res * Mi * pow(Mi, -1, p)) % M
        fr = rational_reconstruct(x, M)
        coeffs[c] = fr
    return coeffs, 1


def poly_from_coeffs(coeffs, i, D):
    n = sp.Symbol('n')
    return sum(sp.nsimplify(coeffs[i * (D + 1) + d]) * n ** d
               for d in range(D + 1))


def verify_exact(seqs, cpolys, D, nlo, nhi, label):
    n = sp.Symbol('n')
    fns = [sp.lambdify(n, cp, 'sympy') for cp in cpolys]
    fails = 0
    checks = 0
    for X in seqs:
        for m in range(nlo, nhi + 1):
            if any((m + i) not in X for i in range(4)):
                continue
            s = sum(sp.Rational(fns[i](m)) * sp.Rational(X[m + i].numerator,
                    X[m + i].denominator) for i in range(4))
            checks += 1
            if s != 0:
                fails += 1
    print(f"  [{label}] exact annihilation: {checks} checks, {fails} failures "
          f"-> {'PASS' if fails == 0 else 'FAIL'}")
    return fails == 0


def run(kind, keymap, nlo, nhi):
    get_all(0, nhi + 4)
    seqs = []
    for key in keymap:
        seqs.append({n: triple(n)[key] for n in range(0, nhi + 5)})
    print(f"\n=== fitting order-3 recurrence for {kind} = {keymap} ===")
    D, dim, ncols = find_min_degree(seqs, nlo, nhi)
    if D is None:
        print("  no recurrence found up to Dmax")
        return
    print(f"  minimal poly-degree D = {D}, nullspace dim (mod p) = {dim}")
    coeffs, dimc = reconstruct_solution(seqs, D, nlo, nhi)
    if coeffs is None:
        print(f"  nullspace not 1-dim ({dimc}); try higher nlo/nhi window")
        return
    n = sp.Symbol('n')
    cpolys = []
    for i in range(4):
        cp = sum(coeffs[i * (D + 1) + d] and
                 sp.Rational(coeffs[i * (D + 1) + d].numerator,
                             coeffs[i * (D + 1) + d].denominator) * n ** d or 0
                 for d in range(D + 1))
        cpolys.append(sp.expand(cp))
    # clear denominators to get primitive integer polynomials
    dens = []
    for cp in cpolys:
        for co in sp.Poly(cp, n).all_coeffs():
            dens.append(sp.Rational(co).q)
    from sympy import ilcm
    L = 1
    for dd in dens:
        L = ilcm(L, dd)
    cpolys = [sp.expand(cp * L) for cp in cpolys]
    # remove common integer content
    allco = []
    for cp in cpolys:
        allco += [int(c) for c in sp.Poly(cp, n).all_coeffs()]
    from math import gcd as igcd
    g = 0
    for c in allco:
        g = igcd(g, c)
    if g:
        cpolys = [sp.expand(cp / g) for cp in cpolys]
    labels = ["c0 (X_{n})", "c1 (X_{n+1})", "c2 (X_{n+2})", "c3 (X_{n+3})"]
    for lab, cp in zip(labels, cpolys):
        print(f"  {lab} = {sp.factor(cp)}")
    verify_exact(seqs, cpolys, D, 0, nhi, kind)
    return cpolys


if __name__ == "__main__":
    run("raw (q,p,p̃)", ["q", "p", "pt"], 6, 40)
    run("normalized (Q,P,P̂)", ["Q", "P", "Ph"], 6, 40)
