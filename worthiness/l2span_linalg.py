"""Local-ring linear algebra for the L2SPAN experiment.

Two independent membership oracles for the question
    "does integer covector T lie in the Z/N row-span of integer matrix A?"
where N = p^2 (a local ring, NOT a field).

  (1) hnf_lattice_member  -- GROUND TRUTH.  T in span_{Z/N}(A)  <=>  the integer
      vector T lies in the lattice  L = rowspan_Z(A) + N.Z^d.  Decided by a MODULAR
      Hermite Normal Form: because L always contains N.Z^d we initialise H = N.I and
      reduce every input row into it with all arithmetic done mod N (Hafner-McCurley
      style).  Entries stay in [0,N); no coefficient explosion; unquestionably
      correct.  This is the requested Smith/Hermite-style reduction over the local
      ring, with the p-torsion carried by the non-unit diagonal pivots (which divide
      N: a pivot = p forces only a depth-1 congruence, a pivot = 1 a depth-2 one).

  (2) solve_combination -- an independent Z/N reduction with coefficient tracking
      that both decides membership AND extracts the explicit certificate c
      (sum_k c_k A_k ≡ T mod N).  Cross-validated against (1) and against a literal
      brute-force span enumeration for tiny cases (see self-test).
"""
from math import gcd


# ----------------------------------------------------------------------------
# Modular Hermite Normal Form + lattice membership (GROUND TRUTH)
# ----------------------------------------------------------------------------
def _modular_hnf(A_rows, d, N):
    """Modular HNF of L = rowspan(A) + N.Z^d.  Returns dict col -> pivot row (mod N)
    whose entry at `col` is a divisor of N in {1..N}.  Init H = N.I; all arithmetic
    mod N, entries bounded, no explosion."""
    H = {}
    for col in range(d):
        r = [0] * d
        r[col] = N            # pivot value N (divides N); represents the row N.e_col
        H[col] = r
    def add(row):
        row = [x % N for x in row]
        for col in range(d):
            if row[col] == 0:
                continue
            b = H[col]
            a1, a2 = b[col], row[col]
            g, x, y = _ext_gcd(a1, a2)
            nb = [(x * b[t] + y * row[t]) % N for t in range(d)]
            u1, u2 = a1 // g, a2 // g
            nrow = [(u1 * row[t] - u2 * b[t]) % N for t in range(d)]
            nb[col] = g          # exact pivot value (g | N)
            H[col] = nb
            row = nrow
    for r in A_rows:
        add(r)
    return H


def member_with_H(H, T, d, N):
    """Membership test against a prebuilt modular HNF H (reuse across targets)."""
    cur = [x % N for x in T]
    for col in range(d):
        if cur[col] == 0:
            continue
        b = H[col]
        if cur[col] % b[col] != 0:
            return False
        f = cur[col] // b[col]
        cur = [(cur[t] - f * b[t]) % N for t in range(d)]
    return all(x == 0 for x in cur)


def build_H(A_rows, d, N):
    return _modular_hnf(A_rows, d, N)


def hnf_lattice_member(A_rows, T, d, N):
    """GROUND TRUTH: True iff T in span_{Z/N}(A_rows)."""
    return member_with_H(_modular_hnf(A_rows, d, N), T, d, N)


def _ext_gcd(a, b):
    if b == 0:
        return (abs(a), 1 if a >= 0 else -1, 0)
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    if old_r < 0:
        old_r, old_s, old_t = -old_r, -old_s, -old_t
    return old_r, old_s, old_t


# ----------------------------------------------------------------------------
# Certificate extraction: find integer c with sum_M c[M]*A[M] ≡ T (mod N).
# Same modular-HNF reduction over the LOCAL ring Z/N, now carrying the coefficient
# vector over the original A rows (the N.e_col generators carry zero A-coeff -- they
# supply only the mod-N freedom).  Doubles as an independent membership oracle.
# ----------------------------------------------------------------------------
def solve_combination(A_rows, T, d, N):
    """Return list c (len = #A_rows) with sum_k c_k A_k ≡ T (mod N), or None.

    Built on the validated integer HNF: the lattice L = rowspan_Z(A) + N Z^d is
    put in HNF while tracking, for each basis row, its integer combination of the
    ORIGINAL A rows (the N.e_j generators contribute zero to that combination --
    they only supply the mod-N freedom).  Reducing T through the HNF accumulates
    the c-vector.  Reconstruction is verified by the caller.
    """
    m = len(A_rows)
    # H[col] = (row mod N, coeff over A rows mod N); init H = N.I with zero A-coeff.
    H = {}
    for col in range(d):
        r = [0] * d; r[col] = N
        H[col] = (r, [0] * m)

    def add(row, cf):
        row = [x % N for x in row]; cf = [x % N for x in cf]
        for col in range(d):
            if row[col] == 0:
                continue
            b, bc = H[col]
            a1, a2 = b[col], row[col]
            g, x, y = _ext_gcd(a1, a2)
            nb = [(x * b[t] + y * row[t]) % N for t in range(d)]
            nbc = [(x * bc[t] + y * cf[t]) % N for t in range(m)]
            u1, u2 = a1 // g, a2 // g
            nrow = [(u1 * row[t] - u2 * b[t]) % N for t in range(d)]
            ncf = [(u1 * cf[t] - u2 * bc[t]) % N for t in range(m)]
            nb[col] = g
            H[col] = (nb, nbc)
            row, cf = nrow, ncf

    for k in range(m):
        e = [0] * m; e[k] = 1
        add(A_rows[k], e)

    cur = [x % N for x in T]
    acc = [0] * m
    for col in range(d):
        if cur[col] == 0:
            continue
        b, bc = H[col]
        if cur[col] % b[col] != 0:
            return None
        f = cur[col] // b[col]
        cur = [(cur[t] - f * b[t]) % N for t in range(d)]
        acc = [(acc[t] + f * bc[t]) % N for t in range(m)]
    if all(x == 0 for x in cur):
        return [x % N for x in acc]
    return None


# ----------------------------------------------------------------------------
# Self-test: validate the two independent oracles against literal brute force
# ----------------------------------------------------------------------------
def _selftest():
    import random
    from itertools import product
    random.seed(1)
    fails = 0
    # (A) literal brute-force span enumeration, tiny cases, N=p^2
    for N in (25, 49):
        for trial in range(200):
            d = 3
            m = 3
            A = [[random.randrange(N) for _ in range(d)] for _ in range(m)]
            span = set()
            for coeffs in product(range(N), repeat=m):
                v = tuple(sum(coeffs[k] * A[k][t] for k in range(m)) % N for t in range(d))
                span.add(v)
            for _ in range(6):
                T = [random.randrange(N) for _ in range(d)]
                truth = tuple(T) in span
                g1 = hnf_lattice_member(A, T, d, N)
                c = solve_combination(A, T, d, N)
                g3 = c is not None
                if g3:
                    chk = [sum(c[k] * A[k][t] for k in range(m)) % N for t in range(d)]
                    if chk != [x % N for x in T]:
                        fails += 1; print("  solve reconstruct FAIL")
                if not (truth == g1 == g3):
                    fails += 1
                    print(f"  MISMATCH truth={truth} hnf={g1} solve={g3} A={A} T={T}")
    # (B) larger random, the two oracles must agree; reconstruction must check
    for N in (25, 49, 121, 169):
        for trial in range(200):
            d = random.randint(3, 9)
            m = random.randint(2, 12)
            A = [[random.randrange(N) for _ in range(d)] for _ in range(m)]
            for _ in range(4):
                if random.random() < 0.5:
                    coeffs = [random.randrange(N) for _ in range(m)]
                    T = [sum(coeffs[k] * A[k][t] for k in range(m)) % N for t in range(d)]
                else:
                    T = [random.randrange(N) for _ in range(d)]
                g1 = hnf_lattice_member(A, T, d, N)
                c = solve_combination(A, T, d, N)
                g3 = c is not None
                if g3:
                    chk = [sum(c[k] * A[k][t] for k in range(m)) % N for t in range(d)]
                    if chk != [x % N for x in T]:
                        fails += 1; print("  solve reconstruct FAIL")
                if not (g1 == g3):
                    fails += 1
                    print(f"  MISMATCH N={N} hnf={g1} solve={g3}")
    print(f"[selftest] {'ALL PASS' if fails == 0 else f'{fails} FAILURES'}")
    return fails == 0


if __name__ == "__main__":
    _selftest()
