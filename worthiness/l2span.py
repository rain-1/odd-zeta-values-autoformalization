"""L2SPAN -- the depth-2 iterated-certificate experiment (Phase 2, primes p <= n).

Spec: worthiness/PHASE2_CERT_FROM_FABLE.md  §3.
Companion writeup: worthiness/PHASE2_L2SPAN.md.

WHAT THIS TESTS.  Level 1 (n < p <= 2n, cb_certificate.tex) proved  w_n ≡ 0 (mod p)
by showing the target covector  w = sum_j a_{3,j}  lies in the F_p-span of the exact
decay relations  E_M(a) = 0  (M = 1..4n+4).  Because there  every a_{i,j} is
p-INTEGRAL, "T in span mod p" forces ord_p(T(a)) >= 1.  This script asks whether the
same mechanism, iterated to depth 2 (span over the LOCAL RING Z/p^2), forces the
extra Kummer digit(s) when p <= n and the poles j=0..n collide mod p.

THE FORCING LEMMA (sound; the honest depth-2 statement).
Let  m_a := min_{i,j} ord_p(a_{i,j})  (<= 0 for p <= n -- the a are NOT p-integral).
If an integer covector T lies in the Z/p^s row-span of {E_M}, i.e. there are
integers c_M with  T ≡ sum_M c_M E_M (mod p^s)  coordinatewise, then writing
T = sum c_M E_M + p^s U (U an integer covector) and using E_M(a)=0 exactly,
        T(a) = p^s U(a),      so     ord_p(T(a)) >= s + m_a .
At level 1 m_a=0, so span mod p gives ord >= 1 (the classical result).  At p<=n the
denominators make m_a negative, and THAT is the whole question: does s outrun m_a?

Usage:
    python3 l2span.py                 # full run: gates + grid + verdict
    python3 l2span.py 8 5             # single (n,p) detailed dump
"""
import sys
from fractions import Fraction
from math import comb

from lemma_cb_explore import all_data, ord_p_fraction, primes_in
from l2span_linalg import (hnf_lattice_member, solve_combination,
                           build_H, member_with_H)


# ----------------------------------------------------------------------------
# coordinates and the exact decay relations E_M (integer covectors)
# ----------------------------------------------------------------------------
def Cneg(i, r):
    """C(-i, r) = (-1)^r C(i+r-1, r), an integer."""
    v = Fraction(1)
    for x in range(r):
        v *= Fraction(-i - x, x + 1)
    return int(v)


def coords(n):
    N = n + 1
    idx = lambda i, j: (i - 1) * N + j
    return N, 6 * N, idx


def E_rows_mod(n, p, s):
    """E_M covectors (M=1..4n+4) reduced mod p^s.  Coordinates (i,j)."""
    mod = p ** s
    N, dim, idx = coords(n)
    rows = []
    for M in range(1, 4 * n + 5):
        row = [0] * dim
        for i in range(1, min(6, M) + 1):
            r = M - i
            c = Cneg(i, r) % mod
            if c == 0:
                continue
            for j in range(N):
                jr = 1 if r == 0 else pow(j, r, mod)
                row[idx(i, j)] = (row[idx(i, j)] + c * jr) % mod
        rows.append(row)
    return rows, dim, idx


def E_relations_exactQ_zero(a, n):
    """Soundness: all E_M vanish exactly over Q."""
    for M in range(1, 4 * n + 5):
        s = Fraction(0)
        for i in range(1, min(6, M) + 1):
            r = M - i
            c = Cneg(i, r)
            s += c * sum(a[i, j] * Fraction(j) ** r for j in range(n + 1))
        if s != 0:
            return False
    return True


# ----------------------------------------------------------------------------
# target covectors  (integer functionals on the (i,j) grid)
# ----------------------------------------------------------------------------
def tgt_w(n, idx, dim):
    v = [0] * dim
    for j in range(n + 1):
        v[idx(3, j)] += 1
    return v


def tgt_u(n, idx, dim):  # zeta(5) coeff, the unit soundness control
    v = [0] * dim
    for j in range(n + 1):
        v[idx(5, j)] += 1
    return v


def tgt_wt(n, idx, dim, mod):  # atilde_{3,j} = j(n-j)a_3 + (2j-n)a_4 - a_5
    v = [0] * dim
    for j in range(n + 1):
        v[idx(3, j)] = (v[idx(3, j)] + j * (n - j)) % mod
        v[idx(4, j)] = (v[idx(4, j)] + (2 * j - n)) % mod
        v[idx(5, j)] = (v[idx(5, j)] - 1) % mod
    return v


def tgt_class_sum(n, idx, dim, i, c, p):
    """S_{i,c} = sum_{j ≡ c (p)} a_{i,j}."""
    v = [0] * dim
    for j in range(n + 1):
        if j % p == c:
            v[idx(i, j)] += 1
    return v


def tgt_class_digit(n, idx, dim, i, c, p):
    """T_{i,c} = sum_{j ≡ c (p)} ((j-c)/p) a_{i,j}  (the depth-1 refinement)."""
    v = [0] * dim
    for j in range(n + 1):
        if j % p == c:
            v[idx(i, j)] += (j - c) // p
    return v


# ----------------------------------------------------------------------------
# measured valuations and forcing
# ----------------------------------------------------------------------------
def covector_apply(v, a, n):
    """exact rational value of integer covector v on the a-vector."""
    N, dim, idx = coords(n)
    s = Fraction(0)
    for i in range(1, 7):
        for j in range(n + 1):
            c = v[idx(i, j)]
            if c:
                s += c * a[i, j]
    return s


def min_ord_a(a, n, p):
    m = 0
    for i in range(1, 7):
        for j in range(n + 1):
            if a[i, j] != 0:
                o = ord_p_fraction(a[i, j], p)
                if o < m:
                    m = o
    return m


def max_span_depth(H_by_s, T, dim, p, smax):
    """largest s in 1..smax with T in the Z/p^s row-span of E_M (prebuilt HNFs)."""
    best = 0
    for s in range(1, smax + 1):
        N = p ** s
        if member_with_H(H_by_s[s], [x % N for x in T], dim, N):
            best = s
        else:
            break
    return best


# ----------------------------------------------------------------------------
# regression anchor + soundness gates
# ----------------------------------------------------------------------------
def regression_anchor(n=8, p=11):
    """Level-1 anchor: for n<p<=2n, w must be forced mod p, u must NOT be,
    and the classical three-term certificate (c_3,c_{p+2},c_{2p+1})=(1,-2,1)
    must reproduce w mod p."""
    d = all_data(n)
    a = d["a"]
    N, dim, idx = coords(n)
    rows1, _, _ = E_rows_mod(n, p, 1)
    w = tgt_w(n, idx, dim)
    u = tgt_u(n, idx, dim)
    ok = True
    forced_w = hnf_lattice_member(rows1, w, dim, p)
    forced_u = hnf_lattice_member(rows1, u, dim, p)
    ok &= forced_w and not forced_u
    # verify the explicit (1,-2,1) certificate at M=3,p+2,2p+1
    combo = [0] * dim
    for (M, cM) in [(3, 1), (p + 2, -2), (2 * p + 1, 1)]:
        r = M - 1  # rows1[r] is E_M
        combo = [(combo[t] + cM * rows1[r][t]) % p for t in range(dim)]
    three_term_ok = all((combo[t] - w[t]) % p == 0 for t in range(dim))
    ok &= three_term_ok
    return {"forced_w": forced_w, "forced_u_spurious": forced_u,
            "three_term_ok": three_term_ok, "pass": bool(ok)}


# ----------------------------------------------------------------------------
# budget arithmetic (level-2 degree count)
# ----------------------------------------------------------------------------
def budget(n, p):
    """Degree budget for a depth-2 Frobenius certificate.
    Level 1: deg phi = 2p, top functional index M = 2p+1 <= 4n+4  <=>  p <= 2n+1.
    Depth-2 candidates ((k^{p^2}-k^p)^2, (k^p-k)^{2p}) have degree 2p^2, giving top
    index M = 2p^2+1, which must be <= available 4n+4.  Also the pole-separating
    depth-2 form needs decay 2p^2 <= 4n+3 (for Q=1)."""
    lvl1_top = 2 * p + 1
    lvl2_top = 2 * p * p + 1
    avail = 4 * n + 4
    return {
        "lvl1_top_M": lvl1_top, "lvl2_top_M": lvl2_top, "avail_M": avail,
        "lvl1_fits": lvl1_top <= avail,
        "lvl2_fits": lvl2_top <= avail,
        "n_needed_for_lvl2": (2 * p * p + 1 - 4 + 3) // 4,  # smallest n with 2p^2+1<=4n+4
    }


def kappa(n, p):
    return ord_p_fraction(Fraction(comb(2 * n, n)), p)


def Lval(n, p):
    """L = ord_p(d_n) = floor(log_p n): the number of base-p digit positions."""
    L, pk = 0, p
    while pk <= n:
        L += 1; pk *= p
    return L


# ----------------------------------------------------------------------------
# per-(n,p) analysis
# ----------------------------------------------------------------------------
def analyze(n, p, smax=3, verbose=False):
    d = all_data(n)
    a = d["a"]
    N, dim, idx = coords(n)
    H_by_s = {s: build_H(E_rows_mod(n, p, s)[0], dim, p ** s)
              for s in range(1, smax + 1)}
    m_a = min_ord_a(a, n, p)
    kap = kappa(n, p)

    exactQ = E_relations_exactQ_zero(a, n)

    # battery of targets
    targets = {}
    targets["w"] = tgt_w(n, idx, dim)
    targets["wt"] = tgt_wt(n, idx, dim, p ** smax)
    targets["u(unit ctrl)"] = tgt_u(n, idx, dim)
    for i in (3, 4):
        for c in range(p):
            targets[f"S[{i},{c}]"] = tgt_class_sum(n, idx, dim, i, c, p)
            targets[f"T[{i},{c}]"] = tgt_class_digit(n, idx, dim, i, c, p)

    results = {}
    for name, T in targets.items():
        val = covector_apply(T, a, n)
        meas = ord_p_fraction(val, p) if val != 0 else None
        s = max_span_depth(H_by_s, T, dim, p, smax)
        guaranteed = (s + m_a) if s > 0 else None
        results[name] = {"meas_ord": meas, "span_depth": s,
                         "guaranteed_ord": guaranteed}

    L = Lval(n, p)
    return {"a": a, "d": d, "m_a": m_a, "kappa": kap, "exactQ": exactQ,
            "results": results, "dim": dim, "L": L, "req_pn": kap - 5 * L,
            "ord_pn": ord_p_fraction(d["p_n"], p),
            "ord_qn": ord_p_fraction(d["q_n"], p) if d["q_n"] != 0 else None}


def print_single(n, p):
    A = analyze(n, p, verbose=True)
    print(f"\n===== (n,p)=({n},{p})  kappa={A['kappa']}  m_a={A['m_a']}  L=ord_p(d_n)={A['L']}  "
          f"ord_p(p_n)={A['ord_pn']}  ord_p(q_n)={A['ord_qn']}  "
          f"E_M exact/Q: {A['exactQ']} =====")
    print(f"  crude p_n floor = -5L = {-5*A['L']};  "
          f"required ord_p(p_n) >= kappa-5L = {A['req_pn']};  "
          f"measured = {A['ord_pn']}")
    print(f"  {'target':12s} {'meas_ord':>9} {'span_depth s':>13} "
          f"{'guaranteed s+m_a':>17} {'gain?':>6}")
    for name, r in A["results"].items():
        s = r["span_depth"]; g = r["guaranteed_ord"]; mo = r["meas_ord"]
        gain = ""
        if g is not None and mo is not None:
            if g > mo:
                gain = "VIOL"   # would be unsound -- must never happen
            elif s >= 2:
                gain = "d2"
        print(f"  {name:12s} {str(mo):>9} {s:>13} {str(g):>17} {gain:>6}")


# ----------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------
def main():
    if len(sys.argv) == 3:
        print_single(int(sys.argv[1]), int(sys.argv[2]))
        return

    print("=" * 78)
    print("L2SPAN  --  depth-2 iterated-certificate experiment (Phase 2, p <= n)")
    print("=" * 78)

    print("\n--- SOUNDNESS GATE 0: linear-algebra self-test ---")
    import l2span_linalg
    l2span_linalg._selftest()

    print("\n--- SOUNDNESS GATE 1: regression anchor (n,p)=(8,11), level 1 ---")
    anc = regression_anchor(8, 11)
    print(f"  w forced mod p:            {anc['forced_w']}")
    print(f"  u NOT forced (spurious?):  {anc['forced_u_spurious']}")
    print(f"  three-term (1,-2,1) at M=(3,13,23) reproduces w mod p: {anc['three_term_ok']}")
    print(f"  ANCHOR: {'PASS' if anc['pass'] else 'FAIL'}")
    # extra anchors across the level-1 band
    band_fail = 0
    for (nn, pp) in [(3, 5), (4, 7), (5, 7), (6, 11), (8, 13), (10, 19), (12, 23)]:
        aa = regression_anchor(nn, pp)
        if not aa["pass"]:
            band_fail += 1
            print(f"  band anchor FAIL (n,p)=({nn},{pp}): {aa}")
    print(f"  additional level-1 band anchors: {'all PASS' if band_fail==0 else f'{band_fail} FAIL'}")

    grid = [(8, 5), (9, 5), (13, 7), (14, 7),      # kappa=1 collisions
            (18, 5), (19, 5), (23, 5), (38, 7),     # kappa=2
            (24, 5), (28, 5)]                        # more kappa
    print("\n--- VERDICT GRID ---")
    print(f"  {'(n,p)':>9} {'kap':>3} {'L':>2} {'m_a':>4} {'ord(p_n)':>8} {'req=k-5L':>8} "
          f"{'w:s/meas/gtd':>14} {'wt:s/meas/gtd':>14} {'2nd digit?':>11}")
    verdicts = []
    for (n, p) in grid:
        A = analyze(n, p)
        rw = A["results"]["w"]; rwt = A["results"]["wt"]
        # gate (a): unit control never over-forced beyond truth
        ru = A["results"]["u(unit ctrl)"]
        u_meas = ru["meas_ord"]; u_g = ru["guaranteed_ord"]
        u_viol = (u_g is not None and u_meas is not None and u_g > u_meas)
        # gate (b): no covector forced to a bound above its measured value
        viol = [nm for nm, r in A["results"].items()
                if r["guaranteed_ord"] is not None and r["meas_ord"] is not None
                and r["guaranteed_ord"] > r["meas_ord"]]
        # 2nd digit forced anywhere among w-layer/class functionals?
        d2 = [nm for nm, r in A["results"].items() if r["span_depth"] >= 2]
        req = A["req_pn"]
        wcell = f"{rw['span_depth']}/{rw['meas_ord']}/{rw['guaranteed_ord']}"
        wtcell = f"{rwt['span_depth']}/{rwt['meas_ord']}/{rwt['guaranteed_ord']}"
        print(f"  ({n:>2},{p:>2})   {A['kappa']:>3} {A['L']:>2} {A['m_a']:>4} {A['ord_pn']:>8} "
              f"{req:>8} {wcell:>14} {wtcell:>14} {str(len(d2))+' fns':>11}")
        verdicts.append((n, p, A, viol, u_viol, d2))

    print("\n--- SOUNDNESS SUMMARY ---")
    any_viol = any(v[3] for v in verdicts) or any(v[4] for v in verdicts)
    print(f"  Gate (b) unsound-forcing violations (guaranteed > measured): "
          f"{'NONE' if not any_viol else 'SOME -- BUG'}")
    for (n, p, A, viol, u_viol, d2) in verdicts:
        if viol:
            print(f"    (n,p)=({n},{p}) VIOLATIONS: {viol}")

    print("\n--- BUDGET ARITHMETIC (level-2 degree count) ---")
    print(f"  {'(n,p)':>9} {'kap':>3} {'lvl1_topM':>9} {'lvl2_topM':>9} "
          f"{'availM=4n+4':>11} {'lvl2_fits?':>10} {'n for lvl2':>10}")
    for (n, p) in grid:
        b = budget(n, p)
        print(f"  ({n:>2},{p:>2})   {kappa(n,p):>3} {b['lvl1_top_M']:>9} "
              f"{b['lvl2_top_M']:>9} {b['avail_M']:>11} {str(b['lvl2_fits']):>10} "
              f"{b['n_needed_for_lvl2']:>10}")


if __name__ == "__main__":
    main()
