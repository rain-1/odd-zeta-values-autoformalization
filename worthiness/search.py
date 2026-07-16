"""Search for sup gamma(a) over the Brown-Zudilin parameter cone.

Works in the doubled symmetric parameters t = (t0; t1..t7) = 2(s0; s1..s7):
gamma is invariant under permutations of t1..t7 (the group G ~ S7) and under
scaling, so points are canonicalised by sorting t1..t7 and dividing out the
common structure only via a height cap.  Admissibility (all 28 forms of the
multiset h non-negative) becomes: t1 + t2 >= 0 and t0 >= t7 for sorted t,
with all entries of equal parity.

Usage:
  python3 search.py bz            # steepest-ascent from the BZ record point
  python3 search.py random N      # N random multi-starts (first-improvement)
  python3 search.py basin K       # K basin-hopping rounds around best known
"""

import json
import sys
import time
from pathlib import Path

import numpy as np

from gamma import gamma, t_to_a, a_to_t

BZ_A = (8, 16, 10, 15, 12, 16, 18, 13)
HEIGHT_CAP = 260          # max |t_i|; keeps a single eval well under a second
RESULTS = Path(__file__).with_name("search_results.jsonl")

_cache = {}


def canonical(t):
    t = list(int(x) for x in t)
    return (t[0],) + tuple(sorted(t[1:]))


def admissible_t(tc):
    t0, rest = tc[0], tc[1:]
    if rest[0] + rest[1] < 0 or t0 < rest[-1]:
        return False
    if len({x & 1 for x in tc}) != 1:
        return False
    return max(abs(x) for x in tc) <= HEIGHT_CAP


def gamma_t(t):
    tc = canonical(t)
    if tc in _cache:
        return _cache[tc]
    if not admissible_t(tc):
        _cache[tc] = -np.inf
        return -np.inf
    try:
        g = gamma(t_to_a(np.array(tc)))
    except Exception:  # degenerate points: no convergence, repeated roots...
        g = -np.inf
    _cache[tc] = g
    return g


def neighbors(tc):
    """Moves: single +-2 (s_i +- 1), all +-1 (parity flip), transfers."""
    out = []
    for i in range(8):
        for d in (2, -2):
            v = list(tc)
            v[i] += d
            out.append(v)
    out.append([x + 1 for x in tc])
    out.append([x - 1 for x in tc])
    for i in range(8):
        for j in range(8):
            if i != j:
                v = list(tc)
                v[i] += 2
                v[j] -= 2
                out.append(v)
    return [canonical(v) for v in out]


def hill_climb(t0, log=lambda *a: None, first_improvement=False):
    cur = canonical(t0)
    cur_g = gamma_t(cur)
    while True:
        best_n, best_g = None, cur_g
        for nb in neighbors(cur):
            g = gamma_t(nb)
            if g > best_g + 1e-12:
                best_n, best_g = nb, g
                if first_improvement:
                    break
        if best_n is None:
            return cur, cur_g
        cur, cur_g = best_n, best_g
        log(cur, cur_g)


def record(tag, t, g):
    a = t_to_a(np.array(t)).tolist()
    with RESULTS.open("a") as f:
        f.write(json.dumps({"tag": tag, "gamma": g, "t": list(t), "a": a,
                            "time": time.time()}) + "\n")


def run_bz():
    t_bz = canonical(a_to_t(BZ_A))
    g0 = gamma_t(t_bz)
    print(f"BZ point t={t_bz}  gamma={g0:.8f}", flush=True)
    top, g = hill_climb(
        t_bz, log=lambda t, g: print(f"  -> {t}  gamma={g:.8f}", flush=True))
    print(f"local optimum: t={top}  gamma={g:.8f}  "
          f"({'IMPROVES on' if g > g0 + 1e-9 else 'equals'} BZ)", flush=True)
    record("bz-hillclimb", top, g)

    # Refine on a doubled lattice (half-integer steps in s).
    t2 = canonical([2 * x for x in top])
    top2, g2 = hill_climb(
        t2, log=lambda t, g: print(f"  2x -> {t}  gamma={g:.8f}", flush=True))
    print(f"refined (x2 lattice): gamma={g2:.8f}", flush=True)
    record("bz-hillclimb-x2", top2, g2)


def random_start(rng):
    for _ in range(1000):
        t0 = int(rng.integers(3, 46))
        rest = np.sort(rng.integers(-t0 // 3, t0 + 1, size=7))
        t = [t0] + rest.tolist()
        par = t0 & 1
        t = [x if (x & 1) == par else x + 1 for x in t]
        tc = canonical(t)
        if admissible_t(tc) and np.isfinite(gamma_t(tc)):
            return tc
    raise RuntimeError("could not sample admissible start")


def run_random(n):
    rng = np.random.default_rng(12345)
    best, best_g = None, -np.inf
    for k in range(n):
        start = random_start(rng)
        top, g = hill_climb(start, first_improvement=True)
        top, g = hill_climb(top)  # finish with steepest ascent
        marker = ""
        if g > best_g:
            best, best_g = top, g
            marker = "  <-- new best"
            record("random-hillclimb", top, g)
        print(f"[{k+1}/{n}] start={start} -> gamma={g:.8f}{marker}",
              flush=True)
    print(f"best of {n} starts: t={best}  gamma={best_g:.8f}", flush=True)


def run_basin(k, seed_t=None):
    rng = np.random.default_rng(6789)
    cur = canonical(seed_t if seed_t is not None else a_to_t(BZ_A))
    cur, cur_g = hill_climb(cur)
    best, best_g = cur, cur_g
    print(f"basin-hopping from gamma={cur_g:.8f}", flush=True)
    for i in range(k):
        pert = list(best)
        for _ in range(int(rng.integers(2, 5))):
            j = int(rng.integers(0, 8))
            pert[j] += 2 * int(rng.integers(-3, 4))
        top, g = hill_climb(canonical(pert))
        marker = ""
        if g > best_g + 1e-12:
            best, best_g = top, g
            marker = "  <-- new best"
            record("basin", top, g)
        print(f"[hop {i+1}/{k}] gamma={g:.8f}{marker}", flush=True)
    print(f"basin best: t={best}  gamma={best_g:.8f}", flush=True)


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "bz"
    if mode == "bz":
        run_bz()
    elif mode == "random":
        run_random(int(sys.argv[2]) if len(sys.argv) > 2 else 50)
    elif mode == "basin":
        run_basin(int(sys.argv[2]) if len(sys.argv) > 2 else 30)
    else:
        raise SystemExit(f"unknown mode {mode}")
