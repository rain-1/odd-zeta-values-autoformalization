"""Exact-denominator audit of Brown-Zudilin linear forms I'(a*n) = Q_n z5 - P_n.

Pipeline per (a, n):
  1. Q_n exactly, via the double binomial sum (sumQ) of the paper.
  2. J(a*n) = I(a*n) numerically to `dps` digits, via the paper's reduction
     (eq. 3F2J) to a 1-dim integral of a product of two 3F2's.
  3. From I = 2Q(z5 + 2 z3 z2) - 4 Phat z2 - 2P, recover the rationals
     P, Phat by integer relation (PSLQ) on x = (2Q z5 + 4Q z3 z2 - J)/2
     against the basis {1, z2}.
  4. Factor den(P), den(Phat); compare with the predicted denominator
     D_n = (prod_i d_{m_i n}) / Phi_n for the proven m-selection (top 5 of
     the 28-multiset h) and each conjectural refined selection ell = 1..5
     (top ell of h', top 5-ell of h'').

Validation anchors (run `python3 audit.py validate`):
  * totally symmetric a = (1,...,1):  Q_1 = 21, P_1 = 87/4, Phat_1 = 101/4;
    Q_2 = 2989, P_2 = 1190161/384, Phat_2 = 344923/96  (paper, Section 2).
  * record point a = (8,16,10,15,12,16,18,13): paper reports *no* arithmetic
    losses, i.e. den(P_n) should match the proven prediction's constraints.
"""

import sys
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import gcd, isqrt

import numpy as np
from mpmath import mp, mpf, binomial, hyp3f2, pslq, quad, zeta

import gamma as G

# --------------------------------------------------------------------------
# 1. Exact Q via (sumQ).

def q_exact(a, n):
    """Q(p*n; q*n) as an exact integer."""
    (p0, p1, p2, p3, p4, p5, p6), (q1, q2, q3, q4, q5) = G._pq_params(a)
    p0, p1, p2, p3, p4, p5, p6 = (x * n for x in (p0, p1, p2, p3, p4, p5, p6))
    q1, q2, q3, q4, q5 = (x * n for x in (q1, q2, q3, q4, q5))

    from math import comb
    total = 0
    # binom(q1, k1-p1) etc. force p1 <= k1 <= p1+q1 and p2 <= k1 <= p2+q2.
    for k1 in range(max(p1, p2), min(p1 + q1, p2 + q2) + 1):
        f1 = comb(k1, p0) * comb(q1, k1 - p1) * comb(q2, k1 - p2)
        if f1 == 0:
            continue
        for k2 in range(max(p4, p5), min(p4 + q4, p5 + q5) + 1):
            f2 = comb(k2, p6) * comb(q4, k2 - p4) * comb(q5, k2 - p5)
            if f2 == 0:
                continue
            total += f1 * f2 * comb(k1 + k2 + q3 - p0 - p6,
                                    p3 + q3 - p0 - p6)
    sign = (-1) ** (p0 + p1 + p2 + p3 + p4 + p5 + p6)
    return sign * total


# --------------------------------------------------------------------------
# 2. High-precision J via the 3F2-product integral (eq. 3F2J with z = y/(1-y)
#    undone, i.e. the y3-integral form directly before that substitution).

def j_numeric(a, n, dps):
    (p0, p1, p2, p3, p4, p5, p6), (q1, q2, q3, q4, q5) = G._pq_params(a)
    p0, p1, p2, p3, p4, p5, p6 = (x * n for x in (p0, p1, p2, p3, p4, p5, p6))
    q1, q2, q3, q4, q5 = (x * n for x in (q1, q2, q3, q4, q5))

    mp.dps = dps
    pref = (mpf(1)
            * mp.factorial(p1) * mp.factorial(q1) / mp.factorial(p1 + q1 + 1)
            * mp.factorial(p2) * mp.factorial(q2) / mp.factorial(p2 + q2 + 1)
            * mp.factorial(p4) * mp.factorial(q4) / mp.factorial(p4 + q4 + 1)
            * mp.factorial(p5) * mp.factorial(q5) / mp.factorial(p5 + q5 + 1))

    symmetric = (p0, p1, p2, q1, q2) == (p6, p5, p4, q5, q4)

    def integrand(y):
        z = -y / (1 - y)
        f1 = hyp3f2(p0 + 1, p1 + 1, p2 + 1, p1 + q1 + 2, p2 + q2 + 2, z)
        f2 = f1 if symmetric else \
            hyp3f2(p4 + 1, p5 + 1, p6 + 1, p4 + q4 + 2, p5 + q5 + 2, z)
        return f1 * f2 * y ** (p3 + 1) * (1 - y) ** (q3 - p0 - p6 - 2)

    val, err = quad(integrand, [0, mpf(1) / 2, 1], error=True, maxdegree=10)
    if err > abs(val) * mpf(10) ** (-dps + 25) + mpf(10) ** (-dps + 25):
        raise ArithmeticError(f"quadrature error too large: {err}")
    return pref * val


# --------------------------------------------------------------------------
# 3. Recover P, Phat by integer relation.

def recover_p(a, n, dps=None, maxcoeff_digits=None):
    """Return (Q, P, Phat) with P, Phat as Fractions, or raise."""
    Q = q_exact(a, n)
    # Height heuristic: den(P) divides prod_i d_{m_i n} ~ e^{n sum(m)}, and
    # numerators are comparable; PSLQ needs ~ 2x the total coefficient
    # digits across the basis, so ~ 4x one coefficient's digits + slack.
    hv = G.h_values(np.asarray(a, dtype=np.int64))
    msum = int(np.sort(hv)[-5:].sum())
    height_digits = int(n * msum / 2.302585) + 10
    if dps is None:
        dps = 4 * height_digits + 80
    if maxcoeff_digits is None:
        maxcoeff_digits = 2 * height_digits + 20
    mp.dps = dps
    try:
        from fast_eval import fast_j
        J = fast_j(a, n, dps)
    except ImportError:
        J = j_numeric(a, n, dps)
    z2, z3, z5 = zeta(2), zeta(3), zeta(5)
    x = (2 * Q * z5 + 4 * Q * z3 * z2 - J) / 2   # = P + 2 Phat z2
    rel = pslq([x, mpf(1), z2], maxcoeff=10 ** (maxcoeff_digits or dps // 3),
               maxsteps=200000)
    if rel is None:
        raise ArithmeticError(f"PSLQ failed at a={a}, n={n}, dps={dps}")
    c0, c1, c2 = rel
    if c0 == 0:
        raise ArithmeticError(f"degenerate PSLQ relation {rel}")
    P = Fraction(-c1, c0)
    Phat = Fraction(-c2, 2 * c0)
    # Certify: residual must vanish to working precision.
    res = abs(c0 * x + c1 + c2 * z2)
    if res > mpf(10) ** (-dps // 2):
        raise ArithmeticError(f"PSLQ residual too large: {res}")
    return Q, P, Phat


# --------------------------------------------------------------------------
# 4. Predicted denominators.

def d_lcm(N):
    """lcm(1..N) as an int."""
    result = 1
    for k in range(2, N + 1):
        result = result * k // gcd(result, k)
    return result


def phi_exact(a, n):
    """Phi_n = prod_{p > sqrt(m1 n)} p^{nu_p}, nu_p from the S7 action."""
    hv = G.h_values(np.asarray(a, dtype=np.int64))
    m1 = int(np.sort(hv)[-1])
    orbit = G.orbit_value_multisets(np.asarray(a, dtype=np.int64))
    base = np.sort(hv[G.F_IDX])

    def ord_fact(N, p):  # Legendre
        s, q = 0, p
        while q <= N:
            s += N // q
            q *= p
        return s

    limit = m1 * n
    sieve = np.ones(limit + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, isqrt(limit) + 1):
        if sieve[i]:
            sieve[i * i:: i] = False
    primes = np.nonzero(sieve)[0]
    primes = primes[primes * primes > m1 * n]

    phi = 1
    for p in primes:
        p = int(p)
        base_ord = sum(ord_fact(int(v) * n, p) for v in base)
        best = 0
        for row in orbit:
            o = base_ord - sum(ord_fact(int(v) * n, p) for v in row)
            best = max(best, o)
        if best > 0:
            phi *= p ** best
    return phi


def predicted_denominators(a, n):
    """{'proven': D, 1: D, ..., 5: D} — the Phi-sharpened predictions."""
    hv = G.h_values(np.asarray(a, dtype=np.int64))
    phi = phi_exact(a, n)
    out = {}
    top5 = sorted((int(v) for v in hv), reverse=True)[:5]
    D = 1
    for m in top5:
        D *= d_lcm(m * n)
    out["proven"] = Fraction(D, phi)
    hp = sorted((int(hv[i]) for i in E_HP_IDX), reverse=True)
    hpp = sorted((int(hv[i]) for i in E_HPP_IDX), reverse=True)
    for ell in range(1, 6):
        D = 1
        for m in hp[:ell] + hpp[:5 - ell]:
            D *= d_lcm(m * n)
        out[ell] = Fraction(D, phi)
    return out


E_HP_IDX = [0, 2, 4, 5, 6, 7, 8, 9, 10, 13, 15, 17, 18, 19, 20, 21, 22, 24,
            25, 26, 27]
E_HPP_IDX = [1, 3, 11, 12, 14, 16, 23]


def factorize(x):
    """Small-prime factorization string of a positive integer."""
    if x == 1:
        return "1"
    parts = []
    for p in range(2, isqrt(x) + 1):
        if x % p == 0:
            e = 0
            while x % p == 0:
                x //= p
                e += 1
            parts.append(f"{p}^{e}" if e > 1 else f"{p}")
    if x > 1:
        parts.append(str(x))
    return "·".join(parts)


def audit_point(a, n_max=3, dps=None):
    a = list(int(x) for x in a)
    print(f"\n=== audit a = {a} ===", flush=True)
    for n in range(1, n_max + 1):
        Q, P, Phat = recover_p(a, n, dps=dps)
        preds = predicted_denominators(a, n)
        denP = P.denominator
        print(f" n={n}: Q has {len(str(abs(Q)))} digits, "
              f"den(P) = {factorize(denP)}, den(Phat) = "
              f"{factorize(Phat.denominator)}", flush=True)
        for key, D in preds.items():
            # Prediction valid iff D * P is an integer (D may be a Fraction).
            ok = (D.numerator * P.numerator) % (D.denominator * denP) == 0
            extra = ""
            if ok:
                slack = Fraction(D.numerator, D.denominator) / denP
                if slack.denominator == 1 and slack.numerator > 1:
                    extra = f"  (slack {factorize(slack.numerator)})"
            print(f"    m-selection {key!s:>6}: "
                  f"{'consistent' if ok else 'VIOLATED'}{extra}", flush=True)


def validate():
    print("[anchor 1] totally symmetric a = (1,...,1)")
    a = [1] * 8
    expect = {1: (21, Fraction(87, 4), Fraction(101, 4)),
              2: (2989, Fraction(1190161, 384), Fraction(344923, 96))}
    for n, (Qe, Pe, Phe) in expect.items():
        Q, P, Phat = recover_p(a, n)
        status = "OK" if (Q, P, Phat) == (Qe, Pe, Phe) else "MISMATCH"
        print(f"  n={n}: Q={Q} P={P} Phat={Phat}  [{status}]", flush=True)

    print("[anchor 2] record point, n=1 (paper: no arithmetic losses)")
    audit_point([8, 16, 10, 15, 12, 16, 18, 13], n_max=1)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "validate":
        validate()
    else:
        a = [int(x) for x in sys.argv[1].split(",")]
        n_max = int(sys.argv[2]) if len(sys.argv) > 2 else 3
        audit_point(a, n_max=n_max)
