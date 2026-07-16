"""Worthiness exponent gamma(a) for the Brown-Zudilin zeta(5) construction.

Implements the quantity

    gamma(a) = (C1 - C0) / (C1 + C2)

from Brown & Zudilin, "On cellular rational approximations to zeta(5)"
(arXiv:2210.03391), for an arbitrary admissible integer parameter vector
a = (a1,...,a8).  gamma(a) > 1 would imply zeta(5) is irrational.
The paper's record is gamma = 0.86597135... at a = (8,16,10,15,12,16,18,13).

Components (notation of the paper, Sections 2, 4, 8, 10):
  * C0 = lim log|Q_n zeta(5) - P_n| / n = log|lambda_2|,
    C1 = lim log Q_n / n = log|lambda_3|,
    where lambda_1,2,3 are the three saddle-point values attached to the
    cubic factor of the resultant F(x) = Res_y(F1, F2) (Section 4).
  * C2 = (m1+...+m5) - lim log Phi_n / n, where m1>=...>=m5 are the five
    largest entries of the 28-element multiset h(a), and Phi_n is the
    arithmetic (prime factorial) gain from the group G ~ S7 acting on the
    symmetric parameters s1..s7 (Sections 8-10).

Everything is exact integer / rational arithmetic up to the final root
finding (mpmath) and the digamma integral (scipy).
"""

from fractions import Fraction
from itertools import permutations

import numpy as np
from mpmath import mp, polyroots
from scipy.special import digamma

mp.dps = 40

# --------------------------------------------------------------------------
# The 28 linear forms h_i (eq. (eq:h) of the paper), rows = coeffs of a1..a8.
H_MATRIX = np.array([
    [1, 0, 0, 0, 0, 0, 0, 0],    # h1  = a1
    [0, 1, 0, 0, 0, 0, 0, 0],    # h2  = a2
    [0, 0, 1, 0, 0, 0, 0, 0],    # h3  = a3
    [0, 0, 0, 1, 0, 0, 0, 0],    # h4  = a4
    [0, 0, 0, 0, 1, 0, 0, 0],    # h5  = a5
    [0, 0, 0, 0, 0, 1, 0, 0],    # h6  = a6
    [0, 0, 0, 0, 0, 0, 1, 0],    # h7  = a7
    [0, 0, 0, 0, 0, 0, 0, 1],    # h8  = a8
    [1, 1, 0, -1, 0, 0, 0, 0],   # h9  = a1+a2-a4
    [1, 0, -1, 0, 1, 0, 0, 0],   # h10 = a1+a5-a3
    [1, 0, -1, 0, 0, 0, 0, 1],   # h11 = a1+a8-a3
    [0, 1, 1, 0, -1, 0, 0, 0],   # h12 = a2+a3-a5
    [0, 1, 1, 0, 0, 0, 0, -1],   # h13 = a2+a3-a8
    [0, 0, 1, 0, 0, 1, 0, -1],   # h14 = a3+a6-a8
    [-1, 0, 1, 1, 0, 0, 0, 0],   # h15 = a3+a4-a1
    [0, -1, 0, 1, 1, 0, 0, 0],   # h16 = a4+a5-a2
    [0, 0, 0, 1, 0, -1, 0, 1],   # h17 = a4+a8-a6
    [0, -1, 0, 1, 0, 0, 0, 1],   # h18 = a4+a8-a2
    [0, 0, 0, 0, 1, 1, 0, -1],   # h19 = a5+a6-a8
    [0, 0, 0, 0, 0, -1, 1, 1],   # h20 = a7+a8-a6
    [1, 1, 0, -1, 0, 1, 0, -1],  # h21 = a1+a2+a6-a4-a8
    [1, 0, -1, 0, 0, -1, 1, 1],  # h22 = a1+a7+a8-a3-a6
    [0, 1, 1, -1, 0, 1, 0, -1],  # h23 = a2+a3+a6-a4-a8
    [0, 1, 1, 0, 0, 1, -1, -1],  # h24 = a2+a3+a6-a7-a8
    [0, -1, -1, 1, 1, 0, 0, 1],  # h25 = a4+a5+a8-a2-a3
    [0, -1, 0, 1, 0, -1, 1, 1],  # h26 = a4+a7+a8-a2-a6
    [0, -1, -1, 1, 0, -1, 1, 2], # h27 = a4+a7+2a8-a2-a3-a6
    [0, -1, -1, 1, 1, -1, 1, 1], # h28 = a4+a5+a7+a8-a2-a3-a6
], dtype=np.int64)

# 17-element index set F (eq. (F17)), 0-based.
F_IDX = [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 13, 15, 17, 19, 22, 26, 27]

# F expressed in the symmetric parameters s0..s7 (Section "Symmetric
# parameters"): 15 pair forms s_i+s_j and 2 single forms s0-s_i.
# Verified against H_MATRIX in _self_test().
F_PAIRS = [(1, 2), (2, 3), (3, 4), (5, 6), (6, 7), (1, 3), (1, 4), (1, 5),
           (2, 6), (2, 4), (2, 5), (3, 7), (3, 6), (5, 7), (4, 7)]
F_SINGLES = [2, 3]

# All 5040 permutations of positions 1..7, as a (5040, 7) index array.
PERMS = np.array(list(permutations(range(1, 8))), dtype=np.int64)


def h_values(a):
    """The 28-element multiset h(a)."""
    return H_MATRIX @ np.asarray(a, dtype=np.int64)


def a_to_t(a):
    """Doubled symmetric parameters t_i = 2 s_i, i = 0..7 (all integers)."""
    a1, a2, a3, a4, a5, a6, a7, a8 = (int(x) for x in a)
    return np.array([
        a2 + a3 + a4,                      # 2 s0
        2 * a1 + a2 - a3 - a4,             # 2 s1
        a3 + a4 - a2,                      # 2 s2
        a2 + a3 - a4,                      # 2 s3
        2 * a5 + a4 - a2 - a3,             # 2 s4
        2 * a8 + a4 - a2 - a3,             # 2 s5
        2 * (a6 - a8) + a2 + a3 - a4,      # 2 s6
        2 * (a7 + a8 - a6) + a4 - a2 - a3, # 2 s7
    ], dtype=np.int64)


def t_to_a(t):
    """Inverse of a_to_t; entries of t may be any integers of equal parity."""
    t0, t1, t2, t3, t4, t5, t6, t7 = (int(x) for x in t)
    a2 = (t0 - t2) // 2
    return np.array([
        (t1 + t2) // 2, (t0 - t2) // 2, (t2 + t3) // 2, (t0 - t3) // 2,
        (t3 + t4) // 2, (t5 + t6) // 2, (t6 + t7) // 2, (t3 + t5) // 2,
    ], dtype=np.int64)


def is_admissible(a):
    """All 28 forms non-negative (convergence of I(g a) across the orbit)."""
    return bool(np.all(h_values(a) >= 0))


# --------------------------------------------------------------------------
# Exact univariate polynomial helpers (ascending integer coefficient lists).

def _pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, pi in enumerate(p):
        if pi:
            for j, qj in enumerate(q):
                r[i + j] += pi * qj
    return r


def _padd(*ps):
    n = max(len(p) for p in ps)
    r = [0] * n
    for p in ps:
        for i, pi in enumerate(p):
            r[i] += pi
    return r


def _pscale(p, c):
    return [c * pi for pi in p]


def _ptrim(p):
    while len(p) > 1 and p[-1] == 0:
        p = p[:-1]
    return p


def _pdiv_linear(p, r):
    """Divide p by (x - r) exactly; return quotient or None if not exact."""
    p = _ptrim(p)
    q = [0] * (len(p) - 1)
    rem = 0
    for i in range(len(p) - 1, -1, -1):
        cur = p[i] + rem
        if i == 0:
            return _ptrim(q) if cur == 0 else None
        q[i - 1] = cur
        rem = cur * r
    return None


def _peval(p, x):
    v = 0
    for c in reversed(p):
        v = v * x + c
    return v


def _pq_params(a):
    """Map a -> (p0..p6, q1..q5) of Section 3."""
    a1, a2, a3, a4, a5, a6, a7, a8 = (int(x) for x in a)
    p = (a5 + a6 - a8, a2 + a3 + a6 - a4 - a8, a6, a2 + a3 + a6 - a8,
         a7, a3 + a6 - a8, a1 + a2 + a6 - a4 - a8)
    q = (a4, a5, a1 + a5 - a3, a1, a2)
    return p, q


def asymptotics(a):
    """Return sorted [log|lambda_1|, log|lambda_2|, log|lambda_3|].

    Saddle-point recipe of Section 4: eliminate y from F1 = F2 = 0 (F1 is
    linear in y), strip the trivial roots x = 0 and x = p3 from the
    resultant, take the three remaining roots, and evaluate the explicit
    exponential expression at each solution (x, y(x)).
    """
    (p0, p1, p2, p3, p4, p5, p6), (q1, q2, q3, q4, q5) = _pq_params(a)

    S1, S2 = p1 + q1, p2 + q2
    e = q3 - p0 - p6
    A = [0, S1 * S2, -(S1 + S2), 1]                      # x(S1-x)(S2-x)
    B = [-p0 * p1 * p2, p0 * p1 + p0 * p2 + p1 * p2,     # (x-p0)(x-p1)(x-p2)
         -(p0 + p1 + p2), 1]
    c1 = _ptrim(_padd(A, _pscale(B, -1)))                # coeff of y in F1
    c0 = _padd(_pmul(c1, [0, 1]), _pscale(A, e), _pscale(B, p3))

    # F2 = sum_j b_j(x) y^j  (quartic terms cancel).
    T4, T5 = p4 + q4, p5 + q5
    s45, prod45 = T4 + T5, T4 * T5
    sig1 = p4 + p5 + p6
    sig2 = p4 * p5 + p4 * p6 + p5 * p6
    sig3 = p4 * p5 * p6
    b3 = [e - s45 + p3 + sig1]
    b2 = [prod45 - e * s45 - sig2 - p3 * sig1, -s45 + sig1]
    b1 = [e * prod45 + p3 * sig2 + sig3, prod45 - sig2]
    b0 = [-p3 * sig3, sig3]

    # Res_y(F1, F2) = sum_j b_j (-c0)^j c1^(3-j).
    negc0 = _pscale(c0, -1)
    c1_2 = _pmul(c1, c1)
    res = _padd(
        _pmul(b0, _pmul(c1_2, c1)),
        _pmul(b1, _pmul(negc0, c1_2)),
        _pmul(b2, _pmul(_pmul(negc0, negc0), c1)),
        _pmul(b3, _pmul(_pmul(negc0, negc0), negc0)),
    )
    res = _ptrim(res)

    # Strip trivial roots x = 0 and x = p3 (once each), then any repeats.
    for root in (0, p3):
        nxt = _pdiv_linear(res, root)
        if nxt is None:
            raise ArithmeticError(f"expected root x={root} absent, a={a}")
        res = nxt
    while True:
        for root in (0, p3):
            nxt = _pdiv_linear(res, root)
            if nxt is not None:
                res = nxt
                break
        else:
            break

    roots = polyroots([mp.mpf(c) for c in reversed(res)],
                      maxsteps=200, extraprec=80)

    def logE(x):
        cval = _peval(c1, x)
        if abs(cval) < mp.mpf(10) ** (-mp.dps + 10):
            return None  # y blows up: spurious resultant root
        u = -(e * _peval(A, x) + p3 * _peval(B, x)) / cval  # u = x + y
        y = u - x

        def term(base, expo):
            if expo == 0:
                return mp.mpf(0)
            ab = abs(base)
            if ab == 0:
                return None
            return expo * mp.log(ab)

        parts = [
            term(x - p0, p0), term(x - p1, p1), term(x - p2, p2),
            term(u - p3, p3), term(y - p4, p4), term(y - p5, p5),
            term(y - p6, p6),
            term(S1 - x, -S1), term(S2 - x, -S2),
            term(u + e, -(p0 + p6 - q3)),
            term(T4 - y, -T4), term(T5 - y, -T5),
            term(q1, q1), term(q2, q2), term(q4, q4), term(q5, q5),
            term(p0, -p0), term(p3 + q3 - p0 - p6, -(p3 + q3 - p0 - p6)),
            term(p6, -p6),
        ]
        if any(p is None for p in parts):
            return None
        return float(sum(parts))

    vals = [v for v in (logE(x) for x in roots) if v is not None]
    if len(vals) != 3:
        raise ArithmeticError(
            f"expected 3 asymptotic values, got {len(vals)} for a={a}")
    return sorted(vals)


# --------------------------------------------------------------------------
# Arithmetic gain lim log(Phi_n)/n from the S7 action.

def orbit_value_multisets(a):
    """Distinct 17-value multisets {h_i(g a) : i in F} over g in G ~ S7."""
    t = a_to_t(a)
    cols = []
    for (i, j) in F_PAIRS:
        cols.append((t[PERMS[:, i - 1]] + t[PERMS[:, j - 1]]) // 2)
    for i in F_SINGLES:
        cols.append((t[0] - t[PERMS[:, i - 1]]) // 2)
    V = np.stack(cols, axis=1)
    V.sort(axis=1)
    return np.unique(V, axis=0)


def phi_limit(a):
    """lim_n log(Phi_n)/n = integral_0^1 phi(x) d psi(x)  (psi = digamma)."""
    hv = h_values(a)
    base_vals = np.sort(hv[F_IDX])
    orbit = orbit_value_multisets(a)
    assert not (orbit.sum(axis=1) != base_vals.sum()).any(), \
        "F-multiset degree not G-invariant"

    distinct = np.unique(orbit[orbit > 0])
    if distinct.size == 0:
        return 0.0
    breaks = np.unique(np.concatenate(
        [np.arange(1, v + 1) / v for v in distinct]))
    mids = np.concatenate([[breaks[0] / 2], (breaks[:-1] + breaks[1:]) / 2])
    # Interval k is (prev break, breaks[k]); phi vanishes on the first one.
    T = np.floor(np.outer(mids, distinct) + 1e-9).astype(np.int64)

    counts = np.zeros((orbit.shape[0], distinct.size), dtype=np.int64)
    idx = np.searchsorted(distinct, orbit)
    valid = (orbit > 0)
    rows = np.repeat(np.arange(orbit.shape[0]), orbit.shape[1])
    np.add.at(counts, (rows[valid.ravel()], idx.ravel()[valid.ravel()]), 1)

    base_counts = np.zeros(distinct.size, dtype=np.int64)
    bidx = np.searchsorted(distinct, base_vals[base_vals > 0])
    np.add.at(base_counts, bidx, 1)

    phi = T @ base_counts - (T @ counts.T).min(axis=1)
    assert (phi >= 0).all()

    lefts = np.concatenate([[np.nan], breaks[:-1]])
    weights = np.empty_like(breaks)
    weights[1:] = digamma(breaks[1:]) - digamma(breaks[:-1])
    weights[0] = 0.0  # phi = 0 on (0, first break)
    assert phi[0] == 0
    return float((phi * weights).sum())


# --------------------------------------------------------------------------

def gamma(a, full=False):
    """Worthiness exponent gamma(a); -inf if a is inadmissible.

    With full=True returns a dict of all intermediate quantities.
    """
    a = np.asarray(a, dtype=np.int64)
    hv = h_values(a)
    if not np.all(hv >= 0):
        return {"gamma": -np.inf, "admissible": False} if full else -np.inf

    l1, l2, l3 = asymptotics(a)
    C0, C1 = l2, l3
    m = np.sort(hv)[-5:][::-1]
    phil = phi_limit(a)
    C2 = float(m.sum()) - phil
    g = (C1 - C0) / (C1 + C2)
    if not full:
        return g
    return {
        "gamma": g, "admissible": True,
        "C0": C0, "C1": C1, "C2": C2,
        "log_lambda1": l1, "m": m.tolist(), "phi_limit": phil,
        "lambda1_lt_lambda2": l1 < l2 - 1e-12,
    }


# --------------------------------------------------------------------------

def _self_test():
    rng = np.random.default_rng(0)
    # F expressed via s-parameters must match H_MATRIX on random vectors.
    for _ in range(50):
        a = rng.integers(0, 40, size=8)
        t = a_to_t(a)
        assert np.array_equal(t_to_a(t), a)
        from_forms = np.sort(h_values(a)[F_IDX])
        pair_vals = sorted(
            [(t[i] + t[j]) // 2 for (i, j) in F_PAIRS]
            + [(t[0] - t[i]) // 2 for i in F_SINGLES])
        assert list(from_forms) == pair_vals, (a, from_forms, pair_vals)
    print("self-test: F-multiset s-parametrisation OK")


def _validate():
    _self_test()

    print("\n[1] Totally symmetric case a = (1,...,1)")
    d = gamma([1] * 8, full=True)
    print(f"    log lambda_1 = {d['log_lambda1']:.8f}   (paper: -5.29756135)")
    print(f"    C0 = log lambda_2 = {d['C0']:.8f}   (paper: -2.47237372)")
    print(f"    C1 = log lambda_3 = {d['C1']:.8f}   (paper:  6.38364071)")
    print(f"    m = {d['m']}, phi_limit = {d['phi_limit']:.8f} (paper: m=1^5, 0)")
    print(f"    gamma = {d['gamma']:.8f}   (paper: 0.77795976)")

    print("\n[2] Main example a = (8,16,10,15,12,16,18,13)")
    d = gamma([8, 16, 10, 15, 12, 16, 18, 13], full=True)
    print(f"    log lambda_1 = {d['log_lambda1']:.8f}   (paper: -66.05784567)")
    print(f"    C0 = {d['C0']:.8f}   (paper: -31.55296934)")
    print(f"    C1 = {d['C1']:.8f}   (paper:  85.08768883)")
    print(f"    m = {d['m']}   (paper: [18,17,17,16,16])")
    print(f"    phi_limit = {d['phi_limit']:.8f}   (paper: 34.39425186)")
    print(f"    gamma = {d['gamma']:.8f}   (paper: 0.86597135)")

    print("\n[3] Second example a = (15,20,16,14,18,17,16,20)")
    d = gamma([15, 20, 16, 14, 18, 17, 16, 20], full=True)
    print(f"    gamma = {d['gamma']:.8f}   (paper: 0.85163139)")


if __name__ == "__main__":
    _validate()
