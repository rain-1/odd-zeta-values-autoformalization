"""Ground-truth exact data for the Sol-salvage verification campaign (V1-V8).

Extends worthiness/lemma_cb_explore.py's all_data chain to also expose the third
minor p̃_n = u·ṽ − ũ·v and the C(2n,n)-normalized ladders

    Q_n = (-1)^{n+1} q_n / C(2n,n)      (q-version)
    P_n = (-1)^{n+1} p_n / C(2n,n)      (p-version)
    P̂_n = (-1)^{n+1} p̃_n / C(2n,n)     (p̃-version)

with q_n = u·w̃ − ũ·w, p_n = w̃·v − w·ṽ, p̃_n = u·ṽ − ũ·v (task definitions).

All exact Fractions.  Results are cached to salvage_cache.pkl so the (slow)
partial-fraction chain is computed once and reused by every salvage_*.py script.

Usage as module:  from salvage_data import triple, get_all   (triple(n) -> dict)
Standalone:       python3 salvage_data.py 35     (populate cache to n=35)
"""

from fractions import Fraction
from math import comb, factorial, gcd
import os
import pickle
import sys

ORDER = 5
_CACHE_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "salvage_cache.pkl")


def mul_trunc(a, b, order=ORDER):
    out = [Fraction(0) for _ in range(order + 1)]
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            if i + j <= order and bj != 0:
                out[i + j] += ai * bj
    return out


def linear_factor(c):
    return [Fraction(c), Fraction(1)]


def inverse_sixth_factor(c, order=ORDER):
    c = Fraction(c)
    return [Fraction((-1) ** r * comb(5 + r, r), 1) * c ** (-6 - r)
            for r in range(order + 1)]


def base_coefficients(n):
    a = {}
    for j in range(n + 1):
        series = [Fraction(factorial(n) ** 4)]
        series = mul_trunc(series, linear_factor(Fraction(n, 2) - j))
        for m in range(1, n + 1):
            series = mul_trunc(series, linear_factor(-j - m))
            series = mul_trunc(series, linear_factor(n + m - j))
        for m in range(n + 1):
            if m != j:
                series = mul_trunc(series, inverse_sixth_factor(m - j))
        for r in range(6):
            a[6 - r, j] = series[r]
    return a


def companion_coefficients(n, a):
    at = {}
    for i in range(1, 7):
        for j in range(n + 1):
            at[i, j] = (j * (n - j) * a[i, j]
                        + (2 * j - n) * a.get((i + 1, j), 0)
                        - a.get((i + 2, j), 0))
    return at


_H_cache = {}


def harmonic(j, power):
    key = (j, power)
    if key in _H_cache:
        return _H_cache[key]
    val = sum((Fraction(1, k ** power) for k in range(1, j + 1)), Fraction(0))
    _H_cache[key] = val
    return val


def lcm_upto(n):
    ans = 1
    for k in range(2, n + 1):
        ans = ans * k // gcd(ans, k)
    return ans


def _compute(n):
    """Full exact building blocks + the three minors + normalized ladders."""
    a = base_coefficients(n)
    at = companion_coefficients(n, a)
    w = sum(a[3, j] for j in range(n + 1))
    wt = sum(at[3, j] for j in range(n + 1))
    u = sum(a[5, j] for j in range(n + 1))
    ut = sum(at[5, j] for j in range(n + 1))
    v = sum((a[i, j] * harmonic(j, i)
             for i in range(1, 7) for j in range(n + 1)), Fraction(0))
    vt = sum((at[i, j] * harmonic(j, i)
              for i in range(1, 7) for j in range(n + 1)), Fraction(0))
    # task sign conventions
    q_n = u * wt - ut * w          # q = u w̃ − ũ w
    p_n = wt * v - w * vt          # p = w̃ v − w ṽ
    pt_n = u * vt - ut * v         # p̃ = u ṽ − ũ v
    C = comb(2 * n, n)
    sgn = (-1) ** (n + 1)
    Q = Fraction(sgn) * q_n / C
    P = Fraction(sgn) * p_n / C
    Ph = Fraction(sgn) * pt_n / C
    return {
        "n": n,
        "u": u, "w": w, "v": v, "ut": ut, "wt": wt, "vt": vt,
        "q": q_n, "p": p_n, "pt": pt_n,
        "C": C, "Q": Q, "P": P, "Ph": Ph,
    }


_MEM = {}
_DISK = None


def _load_disk():
    global _DISK
    if _DISK is None:
        if os.path.exists(_CACHE_PATH):
            with open(_CACHE_PATH, "rb") as f:
                _DISK = pickle.load(f)
        else:
            _DISK = {}
    return _DISK


def _save_disk():
    with open(_CACHE_PATH, "wb") as f:
        pickle.dump(_DISK, f)


def triple(n):
    """Return the exact data dict for level n (memoized + disk-cached)."""
    if n in _MEM:
        return _MEM[n]
    disk = _load_disk()
    if n in disk:
        _MEM[n] = disk[n]
        return disk[n]
    d = _compute(n)
    _MEM[n] = d
    disk[n] = d
    return d


def get_all(lo, hi, save=True):
    disk = _load_disk()
    changed = False
    out = {}
    for n in range(lo, hi + 1):
        if n not in disk:
            disk[n] = _compute(n)
            changed = True
        out[n] = disk[n]
        _MEM[n] = disk[n]
    if save and changed:
        _save_disk()
    return out


if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 35
    print(f"populating cache n=0..{hi} ...")
    for n in range(0, hi + 1):
        d = triple(n)
        print(f"n={n:>2}  q={d['q']}  Q={d['Q']}  P={d['P']}  Ph={d['Ph']}")
    _save_disk()
    print("cache saved to", _CACHE_PATH)
