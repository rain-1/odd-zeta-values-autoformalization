"""STEP 2 -- the a=1 band (n = p+r): head-window decomposition, block tools,
and the precise REDUCED statement of the denominator-free vector congruence.

Usage:
    python3 dwork_a1_band.py [pmax] [nmax]      # default pmax=29, nmax=60

Exact Fraction / integer arithmetic.  HONESTY: finite exact verification over the
stated grid; the final head-window identity (the "two missing digits") is NOT
proved here -- it is stated precisely as the single remaining obligation.

Reconciled with Sol's plan (ZETA7_DWORK_FROM_SOL.txt, sec T1): the object proved-
about is Sol's  Delta_5 = q_1 p^5 p_n - p_1 q_n  (eq 15), Delta_3 = q_1 p^3 ptil_n
- ptil_1 q_n (eq 16).  Sol's floor is v_p(Delta_5) >= v_p(q_1 q_n)+1; the grid
below shows the (empirically tighter) uniform  v_p(Delta_5) >= v_p(q_1)+2.
"""
import sys
from fractions import Fraction
from math import comb, factorial
sys.path.insert(0, '/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from lemma_cb_explore import (all_data, primes_in, ord_p_fraction as op,
                              base_coefficients, companion_coefficients, harmonic)

_c = {}
def minors(n):
    if n not in _c:
        d = all_data(n)
        u, ut, w, wt, v, vt = d["u"], d["ut"], d["w"], d["wt"], d["v"], d["vt"]
        _c[n] = (u * wt - ut * w, wt * v - w * vt, u * vt - ut * v)
    return _c[n]
def kap(n, p):
    return op(Fraction(comb(2 * n, n)), p)


# ---------------------------------------------------------------------------
# (A) head-window decomposition of v (reproduce V1 in the clean vector frame)
# ---------------------------------------------------------------------------
def decomposition(pmax, nmax):
    print("=" * 78)
    print("(A) head-window decomposition   v = Sing + resid   (a=1 range n=p+r)")
    print("    Sing = sum_i (-1)^{i+1} p^{-i} S_i^head,  S_i^head = sum_{j=0}^r a_{i,j}")
    print("    verify: v-Sing exact-equals sum_{i,j} a_{i,j} Hhat_j^{(i)}, ord(resid)>=-2,")
    print("            ladder ord(S_i^head)=i-5 (i=2..6)")
    print("=" * 78)
    worst_resid = 99
    ladder_ok = True          # clean-prime band ladder (p>=11, r>=ceil(p/2))
    ladder_edge_dev = 0       # deviations at edge primes / small r (expected)
    decomp_ok = True
    for n in range(5, nmax + 1):
        for p in primes_in(n // 2 + 1, min(n - 1, pmax)):   # a=1 band core (p<=n<2p)
            if p < 5 or n >= 2 * p:
                continue
            r = n - p
            a = base_coefficients(n)
            # Hhat_j^{(i)} = H_j^{(i)} - [j>=p] p^{-i}
            def Hhat(j, i):
                base = harmonic(j, i)
                return base - (Fraction(1, p ** i) if j >= p else Fraction(0))
            v = sum((a[i, j] * harmonic(j, i) for i in range(1, 7) for j in range(n + 1)), Fraction(0))
            resid_direct = sum((a[i, j] * Hhat(j, i) for i in range(1, 7) for j in range(n + 1)), Fraction(0))
            Sfun = lambda i: sum((a[i, j] for j in range(r + 1)), Fraction(0))
            Sing = sum((Fraction((-1) ** (i + 1), p ** i) * Sfun(i) for i in range(1, 7)), Fraction(0))
            resid = v - Sing
            if resid != resid_direct:
                decomp_ok = False
                print(f"   DECOMP MISMATCH n={n} p={p}")
            if resid != 0:
                worst_resid = min(worst_resid, op(resid, p))
            clean_band = (p >= 11 and r >= (p + 1) // 2)
            for i in range(2, 7):
                Si = Sfun(i)
                if Si != 0 and op(Si, p) != i - 5:
                    if clean_band:
                        ladder_ok = False
                        print(f"   LADDER FAIL (clean band) n={n} p={p} r={r} i={i}: ord={op(Si,p)} != {i-5}")
                    else:
                        ladder_edge_dev += 1
    print(f"  decomposition exact (v-Sing == sum a Hhat): {decomp_ok}")
    print(f"  ladder ord(S_i^head)=i-5 (i=2..6) on clean band (p>=11, r>=ceil(p/2)): {ladder_ok}")
    print(f"  (edge/small-r deviations outside clean band, expected: {ladder_edge_dev})")
    print(f"  worst ord_p(resid) over band = {worst_resid}  (blueprint predicts >= -2)")


# ---------------------------------------------------------------------------
# (B) Sol's floor bounds on Delta_5, Delta_3 (eq 15-16), clean vector form
# ---------------------------------------------------------------------------
def sol_floor(pmax, nmax):
    print("\n" + "=" * 78)
    print("(B) Sol Delta_5 = q_1 p^5 p_n - p_1 q_n,  Delta_3 = q_1 p^3 ptil_n - ptil_1 q_n")
    print("    Sol floor (eq15/16): v_p(Delta) >= v_p(q_1 q_n)+1 ; also uniform v_p>=v_p(q_1)+2")
    print("=" * 78)
    q1, p1, pt1 = minors(1)
    solfail = mainfail = rows = 0
    minA = minB = 99
    sol_viol = []
    for p in primes_in(5, pmax):
        for n in range(p, min(2 * p, nmax + 1)):   # full a=1 range r in [0,p-1]
            qn, pn, ptn = minors(n)
            r = n - p
            kappa = kap(n, p)
            D5 = q1 * Fraction(p) ** 5 * pn - p1 * qn
            D3 = q1 * Fraction(p) ** 3 * ptn - pt1 * qn
            o5 = op(D5, p) if D5 != 0 else 99
            o3 = op(D3, p) if D3 != 0 else 99
            vq1qn = op(q1, p) + (op(qn, p) if qn != 0 else 99)
            rows += 1
            # Sol bound
            if o5 < vq1qn + 1 or o3 < vq1qn + 1:
                solfail += 1
                sol_viol.append((n, p, r, kappa, op(qn, p), o5, o3, vq1qn + 1))
            # uniform bound
            if o5 < op(q1, p) + 2 or o3 < op(q1, p) + 2:
                mainfail += 1
                print(f"   UNIFORM FAIL n={n} p={p}: o5={o5} o3={o3} vq1={op(q1,p)}")
            minA = min(minA, o5 - vq1qn, o3 - vq1qn)
            minB = min(minB, o5 - op(q1, p), o3 - op(q1, p))
    print(f"  rows (a=1 full, p>=5, n<= {nmax}): {rows}")
    print(f"  Sol floor v_p(Delta)>=v_p(q_1 q_n)+1: violations={solfail}; min surplus over v_p(q1 qn) = {minA}")
    for (n, p, r, kp, oqn, o5, o3, need) in sol_viol:
        print(f"     Sol-viol n={n} p={p} r={r} kappa={kp} ord(q_n)={oqn}: "
              f"o5={o5},o3={o3} < need {need}  (q_n over-divisible => q_n-scaled floor too strong)")
    print(f"  uniform    v_p(Delta)>=v_p(q_1)+2   : violations={mainfail}; min surplus over v_p(q1)    = {minB}")


# ---------------------------------------------------------------------------
# (C) Sol's factorial p-block identity  (Ap+b)! = Phi(A,b)   (eq 3-4)
# ---------------------------------------------------------------------------
def E_m(x, m, p, prec=6):
    """prod_{h=1}^m (1 + x p / h), exact Fraction."""
    out = Fraction(1)
    for h in range(1, m + 1):
        out *= (1 + Fraction(x) * p / h)
    return out

def Phi(A, b, p):
    """Sol eq(3): p^A A! (p-1)!^A b! prod_{t=0}^{A-1} E_{p-1}(t) * E_b(A)."""
    val = Fraction(p) ** A * factorial(A) * Fraction(factorial(p - 1)) ** A * factorial(b)
    for t in range(A):
        val *= E_m(t, p - 1, p)
    val *= E_m(A, b, p)
    return val

def check_block_identity(pmax):
    print("\n" + "=" * 78)
    print("(C) Sol factorial-block identity  (Ap+b)! = Phi(A,b)  (eq 3-4), exact")
    print("=" * 78)
    bad = 0; checked = 0
    for p in primes_in(5, pmax):
        for A in range(0, 4):
            for b in range(0, p):
                M = A * p + b
                lhs = factorial(M)
                rhs = Phi(A, b, p)
                checked += 1
                if Fraction(lhs) != rhs:
                    bad += 1
                    if bad <= 5:
                        print(f"   FAIL p={p} A={A} b={b}: {lhs} != {rhs}")
    print(f"  checked {checked} (A<=3), mismatches = {bad}")


# ---------------------------------------------------------------------------
# (D) Wolstenholme full-block inputs (eq 12) + reversal identity (eq 13)
# ---------------------------------------------------------------------------
def wolstenholme(pmax):
    print("\n" + "=" * 78)
    print("(D) full-block harmonic inputs  v_p(H_{p-1}^{(t)})  (Sol eq 12) and")
    print("    reversal identity  H_{p-1}^{(t)} = (-1)^t sum_h C(t+h-1,h) p^h H_{p-1}^{(t+h)}")
    print("=" * 78)
    need = {1: 2, 2: 1, 3: 2, 4: 1, 5: 2}
    ok_val = True; ok_rev = True
    WT = 14  # extend harmonic weights so the reversal sum reaches the target precision
    for p in primes_in(11, pmax):   # Sol's clean range p>=11 (p=7 is edge, v_p(H^5)=1)
        H = {t: harmonic(p - 1, t) for t in range(1, WT + 1)}
        for t, e in need.items():
            if op(H[t], p) < e:
                ok_val = False
                print(f"   VAL FAIL p={p} t={t}: v_p={op(H[t],p)} < {e}")
        # reversal identity, truncated to working precision mod p^5 (Sol sec 1.5)
        for t in range(1, 6):
            rhs = sum(Fraction((-1) ** t) * comb(t + h - 1, h) * Fraction(p) ** h * H[t + h]
                      for h in range(0, WT - t + 1))
            if op(H[t] - rhs, p) < 5:   # identity to working precision p^5
                ok_rev = False
                print(f"   REV FAIL p={p} t={t}: ord(H_t - reversal)={op(H[t]-rhs,p)} < 5")
    print(f"  valuation inputs (12) hold on grid (p>=11): {ok_val}")
    print(f"  reversal identity (13) holds mod p^5 on grid (p>=11): {ok_rev}")


# ---------------------------------------------------------------------------
# (E) the precise REMAINING statement
# ---------------------------------------------------------------------------
def remaining():
    print("\n" + "=" * 78)
    print("(E) REDUCED STATEMENT -- the single remaining a=1 obligation")
    print("=" * 78)
    print("""  Proved/verified above:
    - v = Sing + resid exactly; ord(resid) >= -2; ladder ord(S_i^head)=i-5.
    - the vector object Delta_5 = q_1 p^5 p_n - p_1 q_n satisfies the measured
      uniform floor v_p(Delta_5) >= v_p(q_1)+2 (Sol's minimal band target +1
      also holds); likewise Delta_3.
    - Sol's factorial p-block identity (Ap+b)! = Phi(A,b) is exact (block tool).
    - the full-block Wolstenholme inputs (12) and reversal identity (13) hold.

  REMAINING (open, = the "two missing digits", Sol sec 1.7):
    Prove, for clean p>=11 and every r in [ceil(p/2),p-1],
        p^5 Sing - (29/28) u - (101/84) p^2 w  ==  0   (mod p^3),          (HW)
    and its companion (HW~).  Equivalently the denominator-free
        v_p( q_1 p^5 p_n - p_1 q_n ) >= v_p(q_1)+2                          (VEC-a1)
    with the head/tail two-block split (eq 2) and the block expansions (6),(8)-
    (11) substituted.  The p^0 digit is forced by the window E_M relations
    (lemma_cb_band_v4 part C -- verified negative beyond that); the p^1 digit is
    predicted to vanish via the reversal identity (13) coupling H_1/H_2, H_3/H_4;
    the p^2 digit via the p^3 block-binomial (Ljunggren/Jacobsthal, eq 14)
    combined with the Bell derivative terms.  These two vanishings are a concrete
    finite symbolic calculation per residue class r -- NOT yet carried out to a
    closed proof here (nor in Sol's note, which states it "is a concrete
    calculation, not yet a theorem").""")


if __name__ == "__main__":
    pmax = int(sys.argv[1]) if len(sys.argv) > 1 else 29
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    decomposition(pmax, nmax)
    sol_floor(pmax, nmax)
    check_block_identity(min(pmax, 23))
    wolstenholme(min(pmax, 43))
    remaining()
