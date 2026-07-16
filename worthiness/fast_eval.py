"""Fast arbitrary-precision evaluation of a family of 3F2's and the
Brown-Zudilin J-integral, via exact partial fractions -> polylogarithms.

Background
----------
For POSITIVE INTEGER parameters the series coefficient of

    3F2(a1,a2,a3; b1,b2; z) = sum_{k>=0} R(k) z^k ,
    R(k) = (a1)_k (a2)_k (a3)_k / ((b1)_k (b2)_k k!)

is a RATIONAL FUNCTION of k.  Writing each Pochhammer as a Gamma-ratio,

    R(k) = C * Gamma(a1+k)Gamma(a2+k)Gamma(a3+k)
                / ( Gamma(b1+k)Gamma(b2+k)Gamma(1+k) ),
    C    = (b1-1)!(b2-1)! / ((a1-1)!(a2-1)!(a3-1)!),

and pairing the three "top" shifts {a1,a2,a3} with the three "bottom"
shifts {b1,b2,1} (Gamma(t+k)/Gamma(b+k) is a finite product of linear
factors when t,b are integers), R(k) becomes an explicit ratio of
products of (k+i).  Its exact partial-fraction decomposition over Q,

    R(k) = sum_{j,m} A_{j,m} / (k+j)^m          (poles at k = -j, j>0),

then yields the analytic continuation (valid on C \\ [1, oo), hence for
all real z <= 0)

    3F2(z) = sum_{j,m} A_{j,m} z^{-j} ( Li_m(z) - sum_{i=1}^{j-1} z^i/i^m ).

Each evaluation costs a few polylog calls (m = 1..max multiplicity,
shared over all j) plus rational dot products.  For small |z| we instead
sum the (stable, non-cancelling for this parameter family) power series
directly, which sidesteps the z^{-j} cancellation near z = 0.

Cancellation.  For large |z| the polylog form loses roughly
max_j(j)*log10|z| + log10 max|A_{j,m}| digits.  We evaluate at boosted
working precision; the public `eval_3f2` self-validates by doubling the
guard until two precisions agree to `dps` digits.

Author: fast_eval for the worthiness audit; does not modify existing files.
"""

import math
import time
from collections import Counter
from fractions import Fraction
from functools import lru_cache

import numpy as np
from mpmath import mp, mpf, log, polylog, quad

import gamma as G


# ==========================================================================
# Exact partial-fraction preprocessing.
# ==========================================================================

def _flog10_abs(fr):
    """~log10|fr| for a nonzero Fraction, via bit lengths (never overflows)."""
    if fr == 0:
        return float("-inf")
    n = abs(fr.numerator)
    d = abs(fr.denominator)
    return (n.bit_length() - d.bit_length()) * 0.30102999566398114


def _series_prod(shifts, center, order):
    """Coeffs (Fractions) of prod_{i in shifts} ((i-center) + s) up to s^order."""
    poly = [Fraction(1)]
    for i in shifts:
        a0 = Fraction(i - center)
        new = [Fraction(0)] * min(len(poly) + 1, order + 1)
        for d, c in enumerate(poly):
            if d <= order:
                new[d] += c * a0
            if d + 1 <= order:
                new[d + 1] += c
        poly = new
    if len(poly) < order + 1:
        poly = poly + [Fraction(0)] * (order + 1 - len(poly))
    return poly


def _series_inv(den, order):
    """Reciprocal power series of `den` (den[0] != 0) up to s^order."""
    inv = [Fraction(0)] * (order + 1)
    inv[0] = Fraction(1) / den[0]
    for k in range(1, order + 1):
        acc = Fraction(0)
        for j in range(1, k + 1):
            dj = den[j] if j < len(den) else Fraction(0)
            acc += dj * inv[k - j]
        inv[k] = -acc / den[0]
    return inv


def _series_mul(p, q, order):
    out = [Fraction(0)] * (order + 1)
    for i, pi in enumerate(p):
        if i > order or pi == 0:
            continue
        for j, qj in enumerate(q):
            if i + j > order:
                break
            out[i + j] += pi * qj
    return out


class PF:
    """Cached exact decomposition of one 3F2 series coefficient.

    Attributes
    ----------
    poles : list of (j, [A_{j,1}, ..., A_{j,mj}])   (Fractions)
    M          : max pole multiplicity
    max_pole   : largest j
    maxA_log10 : ~log10 of the largest |A_{j,m}|
    a1..b2     : the raw integer parameters (for the direct-series path)
    """

    def __init__(self, a1, a2, a3, b1, b2, poles, M, max_pole, maxA_log10):
        self.a1, self.a2, self.a3, self.b1, self.b2 = a1, a2, a3, b1, b2
        self.poles = poles
        self.M = M
        self.max_pole = max_pole
        self.maxA_log10 = maxA_log10
        self._mpf_cache = {}

    def mpf_As(self):
        """Poles with A's converted to mpf at the current mp.prec (cached)."""
        key = mp.prec
        c = self._mpf_cache.get(key)
        if c is None:
            c = [(j, [mpf(fr.numerator) / mpf(fr.denominator) for fr in As])
                 for (j, As) in self.poles]
            self._mpf_cache[key] = c
        return c


@lru_cache(maxsize=None)
def pf_3f2(a1, a2, a3, b1, b2):
    """Exact partial-fraction decomposition object for 3F2(a1,a2,a3;b1,b2;.).

    All five arguments must be positive integers with b1, b2 >= 1.
    """
    a1, a2, a3, b1, b2 = int(a1), int(a2), int(a3), int(b1), int(b2)
    for v in (a1, a2, a3, b1, b2):
        if v < 1:
            raise ValueError("parameters must be positive integers")

    tops = sorted((a1, a2, a3))
    bots = sorted((b1, b2, 1))
    num_shifts = []   # (k+i) factors in the numerator
    den_shifts = []   # (k+i) factors in the denominator
    for t, b in zip(tops, bots):
        if t > b:
            num_shifts.extend(range(b, t))       # i = b .. t-1
        elif t < b:
            den_shifts.extend(range(t, b))       # i = t .. b-1

    # Cancel common linear factors.
    nc, dc = Counter(num_shifts), Counter(den_shifts)
    common = nc & dc
    nc -= common
    dc -= common
    num_shifts = list(nc.elements())
    den_shifts = list(dc.elements())

    deg_num, deg_den = len(num_shifts), len(den_shifts)
    if deg_num >= deg_den:
        # Improper: series has a nonzero polynomial part and does NOT converge
        # at z <= -1.  For admissible Brown-Zudilin parameters this never
        # occurs (a6 <= a4 + a8 keeps every shape proper); fail loudly.
        raise NotImplementedError(
            f"improper R(k) for 3F2({a1},{a2},{a3};{b1},{b2}); "
            f"deg_num={deg_num} >= deg_den={deg_den}")

    C = Fraction(math.factorial(b1 - 1) * math.factorial(b2 - 1),
                 math.factorial(a1 - 1) * math.factorial(a2 - 1)
                 * math.factorial(a3 - 1))

    # --- sanity: rational function must reproduce R(k) for small k >= 0 ---
    def R_true(k):
        num = den = Fraction(1)
        for (x, cnt) in ((a1, 1), (a2, 1), (a3, 1)):
            for _ in range(cnt):
                for t in range(k):
                    num *= (x + t)
        for x in (b1, b2, 1):
            for t in range(k):
                den *= (x + t)
        return num / den

    def R_rat(k):
        v = C
        for i in num_shifts:
            v *= Fraction(k + i)
        for i in den_shifts:
            v /= Fraction(k + i)
        return v

    for k in range(4):
        assert R_true(k) == R_rat(k), (a1, a2, a3, b1, b2, k)

    # --- partial fractions via Laurent expansion at each pole ---
    den_c = Counter(den_shifts)
    poles = []
    M = 0
    maxA_log10 = float("-inf")
    for j in sorted(den_c):
        m = den_c[j]
        M = max(M, m)
        rest = list((den_c - Counter({j: m})).elements())   # den without (k+j)^m
        num_ser = _series_prod(num_shifts, j, m - 1)
        rest_ser = _series_prod(rest, j, m - 1)
        g = _series_mul(num_ser, _series_inv(rest_ser, m - 1), m - 1)
        # A_{j, m-t} = C * g[t]
        As = [Fraction(0)] * m
        for t in range(m):
            As[m - 1 - t] = C * g[t]
        poles.append((j, As))
        for A in As:
            maxA_log10 = max(maxA_log10, _flog10_abs(A))

    max_pole = max(den_c)
    return PF(a1, a2, a3, b1, b2, poles, M, max_pole, maxA_log10)


# ==========================================================================
# Core evaluation at the ambient mp precision.
# ==========================================================================

def _direct_series(a1, a2, a3, b1, b2, z):
    """Sum the 3F2 power series directly (stable for |z| <= ~1/2)."""
    tol = mpf(10) ** (-(mp.dps + 8))
    term = mpf(1)
    s = mpf(1)
    k = 0
    while k < 200000:
        term = term * z * (a1 + k) * (a2 + k) * (a3 + k)
        term = term / ((b1 + k) * (b2 + k) * (k + 1))
        s = s + term
        k += 1
        if abs(term) < tol:
            break
    return s


def _eval_core(pf, z):
    """3F2 value at real z <= 0, at the current mp precision."""
    z = mpf(z)
    if abs(z) <= 0.5:
        return _direct_series(pf.a1, pf.a2, pf.a3, pf.b1, pf.b2, z)

    M = pf.M
    maxj = pf.max_pole

    # Polylogs Li_m(z), m = 1..M (real for real z <= 0).
    Li = [None] * (M + 1)
    Li[1] = -log(1 - z)
    for m in range(2, M + 1):
        v = polylog(m, z)
        Li[m] = v.real if hasattr(v, "real") and not isinstance(v, mpf) else v

    # Prefix sums S[m][i] = sum_{t=1}^{i} z^t / t^m, for i = 0 .. maxj-1.
    S = [[mpf(0)] * maxj for _ in range(M + 1)]
    zp = z  # z^1
    for i in range(1, maxj):
        for m in range(1, M + 1):
            S[m][i] = S[m][i - 1] + zp / mpf(i ** m)
        zp = zp * z

    total = mpf(0)
    for (j, As) in pf.mpf_As():
        inv_zj = z ** (-j)
        acc = mpf(0)
        for m in range(1, len(As) + 1):
            acc += As[m - 1] * (Li[m] - S[m][j - 1])
        total += inv_zj * acc
    return total


# ==========================================================================
# Public: self-validating single-point evaluator.
# ==========================================================================

def eval_3f2(pf, z, dps):
    """3F2(pf; z) for real z <= 0, accurate to ~dps digits.

    Doubles the cancellation guard until two working precisions agree.
    """
    z = mpf(z)
    az = float(abs(z))
    G = int(pf.max_pole * math.log10(max(az, 10.0))
            + max(pf.maxA_log10, 0.0)) + 15
    G = max(G, 12)
    prev = None
    for _ in range(10):
        mp.dps = dps + G
        a = _eval_core(pf, z)
        mp.dps = dps + 2 * G
        b = _eval_core(pf, z)
        if abs(a - b) <= mpf(10) ** (-dps) * max(abs(b), mpf(1)):
            mp.dps = dps
            return +b
        prev, G = b, 2 * G
    mp.dps = dps
    return +b


# ==========================================================================
# The Brown-Zudilin J-integral, matching audit.j_numeric mathematically.
# ==========================================================================

def _scaled_params(a, n):
    (p0, p1, p2, p3, p4, p5, p6), (q1, q2, q3, q4, q5) = G._pq_params(a)
    p = tuple(x * n for x in (p0, p1, p2, p3, p4, p5, p6))
    q = tuple(x * n for x in (q1, q2, q3, q4, q5))
    return p, q


def fast_j(a, n, dps):
    """Same value as audit.j_numeric(a, n, dps); certified to rel err < 1e-(dps-25).

    Uses eval_3f2's polylog decomposition for the two 3F2 factors and
    tanh-sinh quadrature on [0, 1/2, 1-delta].
    """
    a = [int(x) for x in a]
    (p0, p1, p2, p3, p4, p5, p6), (q1, q2, q3, q4, q5) = _scaled_params(a, n)

    # 3F2 shapes (parameters as in audit.j_numeric).
    pf1 = pf_3f2(p0 + 1, p1 + 1, p2 + 1, p1 + q1 + 2, p2 + q2 + 2)
    symmetric = (p0, p1, p2, q1, q2) == (p6, p5, p4, q5, q4)
    pf2 = pf1 if symmetric else \
        pf_3f2(p4 + 1, p5 + 1, p6 + 1, p4 + q4 + 2, p5 + q5 + 2)

    max_pole = max(pf1.max_pole, pf2.max_pole)
    Amag = max(pf1.maxA_log10, 0.0) + max(pf2.maxA_log10, 0.0)

    # Leading decay exponent of the integrand as y -> 1 (z -> -oo):
    #   F1 ~ |z|^-(min(a_i of F1)),  F2 ~ |z|^-(min(a_i of F2)),
    #   and (1-y)^(q3-p0-p6-2) contributes |z|^-(q3-p0-p6-2) since 1-y ~ 1/|z|.
    # Hence integrand ~ (1-y)^E with
    alpha1 = min(p0, p1, p2) + 1
    alpha2 = min(p4, p5, p6) + 1
    E = alpha1 + alpha2 + q3 - p0 - p6 - 2
    if E <= -1:
        raise ArithmeticError(f"non-integrable tail exponent E={E}")

    # Truncation delta: tail  int_{1-delta}^1 (1-y)^E dy = delta^(E+1)/(E+1)
    # must be < 10^-dps relative to the O(1) reduced integrand.  Add 20 digits
    # of margin for the O(1) leading constant and log corrections.
    Ep1 = max(E + 1, 0.5)
    delta_exp = (dps + 20) / Ep1                 # = log10(1/delta) = log10(z_max)
    # Cap on the per-node working precision (worst cancellation over the
    # domain: near y -> 1, |z| up to 10^delta_exp, plus the A-coeff size).
    W = dps + int(math.ceil(max_pole * delta_exp + Amag)) + 60

    # Outer quadrature precision.  The tanh-sinh abscissae/weights and the
    # final weighted sum only need ~dps digits (the integrand is O(1) where it
    # matters and ~10^-dps in the tail); the heavy cancellation is handled
    # *inside* the integrand at a per-node boosted precision.  Keeping the
    # outer precision low makes node computation cheap.
    Wq = dps + 40

    exp_y = p3 + 1
    exp_1my = q3 - p0 - p6 - 2

    # Leading large-|z| magnitude of each 3F2:  F_i(z) ~ K_i |z|^-alpha_i.
    # Measure log10|K_i| empirically at a reference point (captures any log
    # factor from repeated exponents); used only to (a) skip negligible tail
    # nodes and (b) size the per-node precision to the digits actually needed.
    exp_ref = max(4.0, min(8.0, delta_exp))
    zref = -mpf(10) ** exp_ref
    wref = int(max_pole * exp_ref + Amag) + 40
    with mp.workdps(wref):
        f1r = _eval_core(pf1, zref)
        logK1 = float(mp.log(abs(f1r)) / mp.log(10)) + alpha1 * exp_ref
        if symmetric:
            logK2 = logK1
        else:
            f2r = _eval_core(pf2, zref)
            logK2 = float(mp.log(abs(f2r)) / mp.log(10)) + alpha2 * exp_ref

    mp.dps = Wq
    delta = mpf(10) ** (-delta_exp)
    pref = (mpf(1)
            * mp.factorial(p1) * mp.factorial(q1) / mp.factorial(p1 + q1 + 1)
            * mp.factorial(p2) * mp.factorial(q2) / mp.factorial(p2 + q2 + 1)
            * mp.factorial(p4) * mp.factorial(q4) / mp.factorial(p4 + q4 + 1)
            * mp.factorial(p5) * mp.factorial(q5) / mp.factorial(p5 + q5 + 1))

    atol_exp = dps + 20          # target per-node absolute error 10^-atol_exp

    def integrand(y):
        omy = 1 - y
        fy = float(y)
        fomy = float(omy)
        l_y = math.log10(fy) if fy > 0.0 else -1e18
        l_omy = (math.log10(fomy) if fomy > 1e-300
                 else float(mp.log(omy) / mp.log(10)))
        l_az = l_y - l_omy

        # log10 of |integrand|.  For |z| <= 0.5, F1 F2 ~ O(1); otherwise use
        # the leading asymptotics.
        if l_az <= math.log10(0.5):
            estF = 0.0
            cancel = 0.0
        else:
            estF = logK1 - alpha1 * l_az + logK2 - alpha2 * l_az
            cancel = max_pole * l_az + Amag
        est = estF + exp_y * l_y + exp_1my * l_omy

        if est < -atol_exp:      # provably negligible: contributes < 10^-atol_exp
            return mpf(0)

        sig = est + atol_exp     # significant digits of the integrand we need
        wneed = int(cancel + sig) + 25
        wneed = min(max(wneed, 30), W)
        with mp.workdps(wneed):
            z = -y / omy
            f1 = _eval_core(pf1, z)
            f2 = f1 if symmetric else _eval_core(pf2, z)
            return f1 * f2 * y ** exp_y * omy ** exp_1my

    val, err = quad(integrand, [0, mpf(1) / 2, 1 - delta],
                    error=True, maxdegree=10)
    tol = abs(val) * mpf(10) ** (-dps + 25) + mpf(10) ** (-dps + 25)
    if err > tol:
        raise ArithmeticError(
            f"quadrature error too large: {err} > {tol} (a={a}, n={n})")
    mp.dps = Wq
    return pref * val


# ==========================================================================
# Validation.
# ==========================================================================

def _validate():
    import mpmath
    from mpmath import hyp3f2, zeta

    passed = []

    def report(name, ok, detail=""):
        passed.append(ok)
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}  {detail}", flush=True)

    # ---- 1. Component test vs mpmath.hyp3f2 -----------------------------
    print("\n[1] Component: eval_3f2 vs mpmath.hyp3f2 (dps=50, 40-digit check)")
    rng = np.random.default_rng(12345)
    cases = []   # (A1,A2,A3,B1,B2)
    tries = 0
    while len(cases) < 30 and tries < 20000:
        tries += 1
        a = rng.integers(3, 11, size=8)
        if not G.is_admissible(a):
            continue
        for n in (1, 2):
            (p0, p1, p2, p3, p4, p5, p6), (q1, q2, q3, q4, q5) = \
                _scaled_params(a, n)
            cases.append((p0 + 1, p1 + 1, p2 + 1, p1 + q1 + 2, p2 + q2 + 2))
            if len(cases) < 30:
                cases.append((p4 + 1, p5 + 1, p6 + 1,
                              p4 + q4 + 2, p5 + q5 + 2))
        cases = cases[:30]
    zs = [mpf("-0.3"), mpf("-2.0"), mpf("-50.0"), mpf("-1e8")]
    worst = mpf(0)
    okcount = 0
    for (A1, A2, A3, B1, B2) in cases:
        pf = pf_3f2(A1, A2, A3, B1, B2)
        for z in zs:
            mp.dps = 50
            got = eval_3f2(pf, z, 50)
            mp.dps = 60
            ref = hyp3f2(A1, A2, A3, B1, B2, z)
            rel = abs(got - ref) / (abs(ref) + mpf(10) ** -60)
            worst = max(worst, rel)
            okcount += int(rel < mpf(10) ** -40)
    total = len(cases) * len(zs)
    report(f"component ({total} evaluations, {len(cases)} shapes)",
           okcount == total, f"worst rel err = {mpmath.nstr(worst, 3)}")

    # ---- 2. End-to-end exact linear forms at a = (1,...,1) --------------
    print("\n[2] End-to-end: symmetric point, exact known J (100-digit check)")
    mp.dps = 140
    z2, z3, z5 = zeta(2), zeta(3), zeta(5)
    base = 2 * z5 + 4 * z3 * z2
    exp1 = 21 * base - 4 * (mpf(101) / 4) * z2 - 2 * (mpf(87) / 4)
    exp2 = (2989 * base - 4 * (mpf(344923) / 96) * z2
            - 2 * (mpf(1190161) / 384))
    for n, exp in ((1, exp1), (2, exp2)):
        got = fast_j([1] * 8, n, 130)
        mp.dps = 140
        rel = abs(got - exp) / abs(exp)
        report(f"symmetric n={n}", rel < mpf(10) ** -100,
               f"rel err = {mpmath.nstr(rel, 3)}")

    # ---- 3. Cross-check vs audit.j_numeric -----------------------------
    print("\n[3] Cross-check: fast_j vs audit.j_numeric (dps=60, 40-digit)")
    import audit
    rec = [8, 16, 10, 15, 12, 16, 18, 13]
    t0 = time.time()
    fj = fast_j(rec, 1, 60)
    tf = time.time() - t0
    mp.dps = 60
    t0 = time.time()
    sj = audit.j_numeric(rec, 1, 60)
    ts = time.time() - t0
    mp.dps = 70
    rel = abs(fj - sj) / abs(sj)
    report("record n=1", rel < mpf(10) ** -40,
           f"rel err = {mpmath.nstr(rel, 3)}  (fast {tf:.1f}s, slow {ts:.1f}s)")

    # ---- 4. Speed at the record point ----------------------------------
    print("\n[4] Speed at record point a = [8,16,10,15,12,16,18,13]")
    t0 = time.time()
    _ = fast_j(rec, 1, 250)
    t1 = time.time() - t0
    print(f"      fast_j(n=1, dps=250): {t1:.1f} s", flush=True)
    t0 = time.time()
    _ = fast_j(rec, 2, 450)
    t2 = time.time() - t0
    print(f"      fast_j(n=2, dps=450): {t2:.1f} s", flush=True)
    report("speed (minutes, not hours)",
           t1 < 600 and t2 < 900, f"n1={t1:.0f}s n2={t2:.0f}s")

    print("\n" + ("ALL PASS" if all(passed) else "SOME FAILED")
          + f"  ({sum(passed)}/{len(passed)})")
    return all(passed)


if __name__ == "__main__":
    _validate()
