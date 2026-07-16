"""Exhaustive scan of the arithmetic-progression subfamily.

The BZ record point is t = (41; 7,9,11,13,15,17,19), i.e. s1..s7 form an
arithmetic progression.  This scans all t = (t0; c, c+e, ..., c+6e) with
e even (equal parity), c + (c+e) >= 0, t0 >= c+6e, up to a height cap,
using all cores.  gamma is scale-invariant, so this covers the projective
(t0 : c : e) plane restricted to the cap.
"""

import sys
from multiprocessing import Pool

import numpy as np

from gamma import gamma, t_to_a

CAP = int(sys.argv[1]) if len(sys.argv) > 1 else 160


def eval_point(args):
    t0, c, e = args
    t = np.array([t0] + [c + k * e for k in range(7)])
    try:
        g = gamma(t_to_a(t))
    except Exception:  # degenerate points: no convergence, repeated roots...
        g = -np.inf
    return g, (t0, c, e)


def main():
    jobs = []
    seen = set()
    for c in range(-CAP // 4, CAP + 1):
        for e in range(0, CAP // 3 + 1, 2):
            if 2 * c + e < 0:            # t1 + t2 >= 0
                continue
            top = c + 6 * e
            if top > CAP:
                continue
            for t0 in range(max(top, 1), CAP + 1):
                if (t0 - c) % 2:         # equal parity
                    continue
                key = (t0, c, e)
                g = np.gcd.reduce([t0, c, e]) if (c or e) else t0
                if g > 1 and (t0 // g, c // g, e // g) in seen:
                    continue
                seen.add(key)
                jobs.append(key)
    print(f"scanning {len(jobs)} AP points (cap {CAP})", flush=True)

    best = []
    with Pool(10) as pool:
        for i, (g, key) in enumerate(pool.imap_unordered(
                eval_point, jobs, chunksize=16)):
            if np.isfinite(g):
                best.append((g, key))
            if (i + 1) % 2000 == 0:
                best.sort(reverse=True)
                best = best[:20]
                print(f"  {i+1}/{len(jobs)} done; current best "
                      f"{best[0][0]:.8f} at {best[0][1]}", flush=True)
    best.sort(reverse=True)
    print("\ntop 15 AP points:")
    for g, (t0, c, e) in best[:15]:
        print(f"  gamma={g:.8f}  t0={t0} c={c} e={e}")


if __name__ == "__main__":
    main()
