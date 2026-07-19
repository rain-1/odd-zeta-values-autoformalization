"""Phi/Bell symbolic assembly of Q_HW with togglable structural ingredients,
GATE against the exact oracle, and P6 ingredient-deletion (Sol memo eq 1-13).

Usage:
    python3 dwork_assembly.py [gate|p6|symbolic|all] [primes csv]

Exact Fraction arithmetic. HONESTY: finite exact checks on a stated grid.

MODEL (Sol eq 9-10, exact -- no truncation):
  a_{6,j} = B_j(0),  B_j(y) = y^6 R_n(y-j),
  D_t(j)  = (-1)^{t-1}(t-1)! [ (n/2-j)^{-t} + sum_{m=1}^n (-j-m)^{-t}
              + sum_{m=1}^n (n+m-j)^{-t} - 6 sum_{m=0,m!=j}^n (m-j)^{-t} ],   (eq 9)
  a_{6-m,j} = a_{6,j} * Y_m(D_1..D_m)/m!,   Y_m = complete Bell polynomial.     (eq 10)
This reconstructs every pole layer exactly; GATE = equality with base_coefficients.

ATOM DECOMPOSITION of the (m-j)-block harmonic that carries the full-block content:
  sum_{m=0,m!=j}^n (m-j)^{-t} = H_{n-j}^{(t)} + (-1)^t H_j^{(t)},               (eq A)
and for j<=r<p,  H_{n-j}^{(t)} = H_{p-1+(r-j+1)}^{(t)} exposes the full block
H_{p-1}^{(t)} via the tail shift (eq 11).  The full-block atoms H_{p-1}^{(t)} are
the objects the reversal identity (eq 13) / Wolstenholme inputs (eq 12) govern.
"""
import sys
from fractions import Fraction
from math import comb, factorial
sys.path.insert(0, '/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from lemma_cb_explore import (all_data, base_coefficients, ord_p_fraction as op,
                              harmonic)

RHO1 = Fraction(29, 28)
SIG1 = Fraction(101, 84)

# ---- complete Bell polynomials Y_0..Y_5 (Sol eq, exact) -------------------
def bell(D):
    """Y_m for m=0..5 given D=[_,D1,D2,D3,D4,D5] (1-indexed)."""
    D1, D2, D3, D4, D5 = D[1], D[2], D[3], D[4], D[5]
    return [Fraction(1),
            D1,
            D1**2 + D2,
            D1**3 + 3*D1*D2 + D3,
            D1**4 + 6*D1**2*D2 + 3*D2**2 + 4*D1*D3 + D4,
            D1**5 + 10*D1**3*D2 + 15*D1*D2**2 + 10*D1**2*D3
              + 10*D2*D3 + 5*D1*D4 + D5]

# ---- D_t(j) exact (eq 9), with an atom-aware harmonic option --------------
def Dt_exact(n, j, tmax=5):
    """returns D[1..tmax] exactly (eq 9)."""
    D = [None]*(tmax+1)
    for t in range(1, tmax+1):
        s = Fraction(n, 2) - j
        term = s**(-t)
        for m in range(1, n+1):
            term += Fraction(-j-m)**(-t)
        for m in range(1, n+1):
            term += Fraction(n+m-j)**(-t)
        acc = Fraction(0)
        for m in range(0, n+1):
            if m != j:
                acc += Fraction(m-j)**(-t)
        term -= 6*acc
        D[t] = Fraction((-1)**(t-1) * factorial(t-1)) * term
    return D

def a6_exact(n, j):
    """B_j(0) = (n!)^4 (n/2-j) prod_{m=1}^n (-j-m)(n+m-j) / prod_{m!=j}(m-j)^6."""
    val = Fraction(factorial(n))**4 * (Fraction(n, 2) - j)
    for m in range(1, n+1):
        val *= Fraction(-j-m) * Fraction(n+m-j)
    for m in range(0, n+1):
        if m != j:
            val /= Fraction(m-j)**6
    return val

def a_layers_from_bell(n, j):
    """a_{i,j} for i=1..6 via Bell reconstruction (eq 10). a[i] indexed 1..6."""
    a6 = a6_exact(n, j)
    D = Dt_exact(n, j, 5)
    Y = bell(D)
    a = {}
    for m in range(0, 6):     # a_{6-m,j} = a6 * Y_m / m!
        a[6-m] = a6 * Y[m] / factorial(m)
    return a

# ==========================================================================
def gate(primes):
    print("="*78)
    print("GATE: Bell/D_t reconstruction (eq 9-10) == exact base_coefficients ?")
    print("="*78)
    bad = 0; checked = 0
    for p in primes:
        for r in range((p+1)//2, p):
            n = p + r
            aex = base_coefficients(n)
            for j in range(0, r+1):          # head window suffices for Sing
                arec = a_layers_from_bell(n, j)
                for i in range(1, 7):
                    checked += 1
                    if arec[i] != aex[i, j]:
                        bad += 1
                        if bad <= 5:
                            print(f"  MISMATCH n={n} p={p} j={j} i={i}: {arec[i]} != {aex[i,j]}")
    print(f"  checked {checked} (i,j) entries over head windows; mismatches = {bad}")
    print(f"  GATE (head-window a_ij): {'PASS' if bad==0 else 'FAIL'}")
    return bad == 0

def gate_QHW(primes):
    """Full gate: assembled Q_HW (Bell a_ij for head + exact full u,w) == oracle."""
    print("\n" + "="*78)
    print("GATE-Q: assembled Q_HW (Bell head-window Sing + exact u,w) == oracle Q_HW")
    print("="*78)
    bad = 0
    for p in primes:
        for r in range((p+1)//2, p):
            n = p + r
            d = all_data(n)
            u, w = d["u"], d["w"]
            aex = d["a"]
            # oracle Sing
            def S_or(i): return sum((aex[i, j] for j in range(r+1)), Fraction(0))
            Sing_or = sum((Fraction((-1)**(i+1), p**i)*S_or(i) for i in range(1, 7)), Fraction(0))
            Q_or = Fraction(p)**5*Sing_or - RHO1*u - SIG1*Fraction(p)**2*w
            # assembled Sing (Bell)
            def S_as(i): return sum((a_layers_from_bell(n, j)[i] for j in range(r+1)), Fraction(0))
            Sing_as = sum((Fraction((-1)**(i+1), p**i)*S_as(i) for i in range(1, 7)), Fraction(0))
            Q_as = Fraction(p)**5*Sing_as - RHO1*u - SIG1*Fraction(p)**2*w
            if Q_or != Q_as:
                bad += 1
                print(f"  Q MISMATCH n={n} p={p}: ord(diff)={op(Q_or-Q_as,p) if Q_or!=Q_as else 'oo'}")
    print(f"  GATE-Q through ord 6: {'PASS (assembled == oracle exactly)' if bad==0 else f'{bad} FAIL'}")
    return bad == 0


# ==========================================================================
# ATOM assembly: D_t(j) -> a_{i,j} -> Q_HW as an explicit function of the
# full-block atoms Hp[t]=H_{p-1}^{(t)} (togglable) + p-integral interval sums.
# ==========================================================================
_PH_DELTA = None   # (weight, s, delta) test hook: adds delta to H_c^{(weight)}

def partial_H(c, t):
    val = sum((Fraction(1, b ** t) for b in range(1, c + 1)), Fraction(0))
    if _PH_DELTA is not None and _PH_DELTA[0] == t:
        val = val + _PH_DELTA[2]
    return val

def harm_atom(M, t, p, Hp, prec=8):
    """H_M^{(t)} mod p^prec via atoms Hp[weight] and p-integral partial sums."""
    K = M // p; c = M - K * p
    val = Fraction(0)
    for k in range(1, K + 1):                       # multiples kp (p-poles)
        val += Fraction(1, (k * p) ** t)
    for k in range(0, K):                            # shifted non-multiple blocks
        for h in range(0, prec + 1):
            val += Fraction((-1) ** h * comb(t + h - 1, h)) * Fraction(k * p) ** h * Hp[t + h]
    for h in range(0, prec + 1):                     # final partial block
        val += Fraction((-1) ** h * comb(t + h - 1, h)) * Fraction(K * p) ** h * partial_H(c, t + h)
    return val

def Dt_atom(n, j, p, Hp, tmax=5, prec=8):
    D = [None] * (tmax + 1)
    for t in range(1, tmax + 1):
        Hj  = harm_atom(j,       t, p, Hp, prec)
        Hjn = harm_atom(j + n,   t, p, Hp, prec)
        Hnj = harm_atom(n - j,   t, p, Hp, prec)
        H2nj= harm_atom(2 * n - j, t, p, Hp, prec)
        br = (Fraction(n, 2) - j) ** (-t) \
             + Fraction((-1) ** t) * (Hjn - Hj) \
             + (H2nj - Hnj) \
             - 6 * (Fraction((-1) ** t) * Hj + Hnj)
        D[t] = Fraction((-1) ** (t - 1) * factorial(t - 1)) * br
    return D

def a_atom(n, j, p, Hp, prec=8):
    a6 = a6_exact(n, j)
    D = Dt_atom(n, j, p, Hp, 5, prec)
    Y = bell(D)
    return {6 - m: a6 * Y[m] / factorial(m) for m in range(0, 6)}

def true_Hp(p, wmax=16):
    return [None] + [harmonic(p - 1, t) for t in range(1, wmax + 1)]

def Q_atom(n, p, r, Hp, prec=8):
    """assembled Q_HW using atom-Hp; u,w still exact full sums (they are p-units,
    not the object under test -- the mechanism lives in Sing's head window)."""
    d = all_data(n)
    u, w = d["u"], d["w"]
    Sing = Fraction(0)
    for i in range(1, 7):
        Si = sum((a_atom(n, j, p, Hp, prec)[i] for j in range(r + 1)), Fraction(0))
        Sing += Fraction((-1) ** (i + 1), p ** i) * Si
    return Fraction(p) ** 5 * Sing - RHO1 * u - SIG1 * Fraction(p) ** 2 * w

def gate_atom(primes):
    print("\n" + "=" * 78)
    print("GATE-ATOM: atom assembly (Hp=true H_{p-1}) == oracle Q_HW  mod p^6 ?")
    print("=" * 78)
    ok = True
    for p in primes:
        Hp = true_Hp(p)
        worst = 99
        for r in range((p + 1) // 2, p):
            n = p + r
            d = all_data(n)
            aex = d["a"]
            Sing_or = sum((Fraction((-1) ** (i + 1), p ** i) * sum((aex[i, j] for j in range(r + 1)), Fraction(0))
                           for i in range(1, 7)), Fraction(0))
            Q_or = Fraction(p) ** 5 * Sing_or - RHO1 * d["u"] - SIG1 * Fraction(p) ** 2 * d["w"]
            Q_as = Q_atom(n, p, r, Hp)
            dd = op(Q_or - Q_as, p) if Q_or != Q_as else 99
            worst = min(worst, dd)
        print(f"  p={p}: min ord(Q_oracle - Q_atom) over band = {worst}  "
              f"({'PASS mod p^6' if worst >= 6 else 'FAIL'})")
        ok &= worst >= 6
    return ok


def p6_perturb(primes):
    print("\n" + "=" * 78)
    print("P6: perturb full-block atom Hp[t] -> Hp[t] + p^{s}; report ord(Q_atom)")
    print("    (true ord(Q_HW)=5). A drop pinpoints which weight-t Wolstenholme input")
    print("    owns which digit. e_t = eq-12 valuation floor (2,1,2,1,2).")
    print("=" * 78)
    e = {1: 2, 2: 1, 3: 2, 4: 1, 5: 2}
    for p in primes:
        r = p - 1
        n = p + r
        base = op(Q_atom(n, p, r, true_Hp(p)), p)
        print(f"  p={p} r={r}: baseline ord(Q_atom)={base}  (perturb from s=0; '*'=below eq12 floor)")
        for t in range(1, 6):
            row = []
            for s in range(0, e[t] + 3):
                Hp = true_Hp(p)
                Hp[t] = Hp[t] + Fraction(p) ** s
                o = op(Q_atom(n, p, r, Hp), p)
                mark = "*" if s < e[t] else " "
                row.append(f"{mark}p^{s}:ord{o}")
            print(f"    Hp[{t}] (floor e_{t}={e[t]}): " + " ".join(row))
        print(f"    => c1,c2 broken by: " + ", ".join(
            f"Hp[{t}]@p^{s}" for t in range(1, 6) for s in range(0, e[t])
            if (lambda H: op(Q_atom(n, p, r, H), p))(
                [true_Hp(p)[k] if k != t else true_Hp(p)[k] + Fraction(p) ** s
                 for k in range(len(true_Hp(p)))]) < 3))


def weight_shift_law(primes):
    print("\n" + "=" * 78)
    print("WEIGHT-SHIFT LAW (all band r): perturbing Hp[t] at digit s -> ord(Q)=s+t")
    print("  => Q-digit c_k depends on Hp[t] digit (k-t).  c1<-Hp1_0; c2<-Hp1_1,Hp2_0.")
    print("  Confirm unit response (ord exactly s+t) for t=1,2,3 across the whole band.")
    print("=" * 78)
    ok = True
    for p in primes:
        viol = 0; ntest = 0
        for r in range((p + 1) // 2, p):
            n = p + r
            for t in (1, 2, 3):
                for s in (0, 1):
                    Hp = true_Hp(p)
                    Hp[t] = Hp[t] + Fraction(p) ** s
                    o = op(Q_atom(n, p, r, Hp), p)
                    ntest += 1
                    if o != s + t:
                        viol += 1
        print(f"  p={p}: weight-shift ord=s+t violations = {viol}/{ntest}")
        ok &= viol == 0
    return ok


def C_residue(primes):
    print("\n" + "=" * 78)
    print("C-RESIDUE test: does c1,c2 depend on the r-dependent interval sums H_b?")
    print("  Perturb an interval-sum atom (partial_H used inside harm_atom) via a global")
    print("  offset injected into the FINAL-partial block; report ord(Q).")
    print("  (Isolates the non-Hp part C of c1,c2: a6 block-binomial + interval sums.)")
    print("=" * 78)
    # We test by perturbing partial_H outputs through a monkey-patch-free wrapper:
    # rebuild Q with an additive delta on H_c^{(t)} for the smallest weights.
    global _PH_DELTA
    for p in primes:
        r = p - 1
        n = p + r
        base = op(Q_atom(n, p, r, true_Hp(p)), p)
        print(f"  p={p} r={r}: baseline ord={base}")
        for t in (1, 2):
            for s in (0, 1):
                _PH_DELTA = (t, s, Fraction(p) ** s)
                o = op(Q_atom(n, p, r, true_Hp(p)), p)
                _PH_DELTA = None
                print(f"    perturb interval-sum H_.^({t}) at p^{s}: ord(Q)={o} "
                      f"({'AFFECTS c'+str(o)+' ' if o<5 else 'inert'})")
    _PH_DELTA = None


def p4_revised(primes):
    """Sol PHASE2_HW_FROM_SOL T2: c(r) in ideal (x, h2, h4), x=2r+1-p,
    h_t=H_r^{(t)} mod p.  Tests: (i) c(p-1-r)+c(r) generically !=0 (old antisym dead);
    (ii) c(centre)=0; (iii) variety check: where x!=0 but h2==h4==0, is c==0?
    (iv) linear-fit c = x*A + h2*B + h4*C with A,B,C constants -- solvable?"""
    from fractions import Fraction as F
    import sys as _s
    sys_path = '/home/ubuntu/fable-episode-2/zeta-math/worthiness'
    if sys_path not in _s.path:
        _s.path.insert(0, sys_path)
    from lemma_cb_explore import all_data as AD, harmonic as H
    print("\n" + "=" * 78)
    print("P4-REVISED (Sol T2): c(r) in ideal (x, h2, h4)?  x=2r+1-p, h_t=H_r^{(t)} mod p")
    print("=" * 78)
    _m = {}
    def Mi(nn):
        if nn not in _m:
            d = AD(nn); u,ut,w,wt,v,vt = d["u"],d["ut"],d["w"],d["wt"],d["v"],d["vt"]
            _m[nn] = (u*wt-ut*w, wt*v-w*vt, u*vt-ut*v)
        return _m[nn]
    def cdig(p, r):
        n = p + r; q, pn, pt = Mi(n)
        D = F(p)**5*(pn/q) - RHO1
        kap = 1 if 2*r >= p else 0
        x = D*F(p)**(-(3-kap))
        if x.denominator % p == 0: return None
        return (x.numerator % p)*pow(x.denominator % p, -1, p) % p
    for p in primes:
        c = {r: cdig(p, r) for r in range(0, p)}
        h2 = {r: (H(r,2).numerator % p)*pow(H(r,2).denominator % p,-1,p) % p if r>0 else 0 for r in range(p)}
        h4 = {r: (H(r,4).numerator % p)*pow(H(r,4).denominator % p,-1,p) % p if r>0 else 0 for r in range(p)}
        rc = (p-1)//2
        sum_nz = sum(1 for r in range(p) if c[r] is not None and c.get(p-1-r) is not None
                     and (c[r]+c[p-1-r]) % p != 0)
        # TRUE variety of ideal (x,h2,h4): x==0 AND h2==0 AND h4==0
        variety = [r for r in range(p) if (2*r+1-p) % p == 0 and h2[r]==0 and h4[r]==0]
        vio = [r for r in variety if c[r] not in (0, None)]
        # degree-bounded fit c = x*A(r)+h2*B(r)+h4*C(r), A,B,C deg<=D (structural test)
        rows = [r for r in range(p) if c[r] is not None]
        fits = {}
        for Deg in (0, 1, 2):
            M = []
            for r in rows:
                basis = [r**k % p for k in range(Deg+1)]
                M.append([((2*r+1-p) % p)*b % p for b in basis]
                         + [h2[r]*b % p for b in basis] + [h4[r]*b % p for b in basis])
            fits[Deg] = _solvable_modp(M, [c[r] for r in rows], p)
        print(f"  p={p}: c(centre r={rc})={c[rc]} (0:{c[rc]==0}); "
              f"antisym-sum nonzero {sum_nz}/{p} (old antisym DEAD); "
              f"true-variety(x=h2=h4=0)={variety} viol={vio}; "
              f"fit c=xA+h2B+h4C degA,B,C: deg0={fits[0]} deg1={fits[1]} deg2={fits[2]}")


def _solvable_modp(M, y, p):
    """is there v with M v = y over F_p? (Gaussian elimination; consistency)."""
    A = [row[:] + [y[i]] for i, row in enumerate(M)]
    ncol = len(M[0])
    pr = 0
    for col in range(ncol):
        piv = next((i for i in range(pr, len(A)) if A[i][col] % p != 0), None)
        if piv is None:
            continue
        A[pr], A[piv] = A[piv], A[pr]
        inv = pow(A[pr][col] % p, -1, p)
        A[pr] = [(x*inv) % p for x in A[pr]]
        for i in range(len(A)):
            if i != pr and A[i][col] % p != 0:
                f = A[i][col]
                A[i] = [(A[i][k]-f*A[pr][k]) % p for k in range(ncol+1)]
        pr += 1
    for row in A:
        if all(v % p == 0 for v in row[:ncol]) and row[ncol] % p != 0:
            return False
    return True


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "all"
    primes = [int(x) for x in sys.argv[2].split(",")] if len(sys.argv) > 2 else [13, 17]
    if mode in ("gate", "all"):
        gate(primes)
        gate_QHW(primes)
        gate_atom(primes)
    if mode in ("p6", "all"):
        p6_perturb(primes)
    if mode in ("shift", "all"):
        weight_shift_law(primes)
        C_residue(primes)
    if mode in ("p4", "all"):
        p4_revised(primes if max(primes) <= 41 else [13, 17, 23, 29, 31, 37, 41])
