"""Map the true denominator pattern (the 'ell-pattern') on small cone points.

For each small admissible point a and n, recover the exact P, Phat by the
audit pipeline and record which m-selections (proven / refined ell = 1..5)
are consistent with the true den(P), plus any slack (extra savings beyond
the prediction).  Small heights keep the slow 3F2 evaluator viable; the
fast evaluator (fast_eval.py, in progress) will extend this map to larger
points.

Usage: python3 audit_map.py [max_points] [pool_size]
Writes audit_map_results.jsonl.
"""

import json
import sys
import time
import traceback
from multiprocessing import Pool

import numpy as np

import gamma as G
from audit import predicted_denominators, recover_p

RESULTS = "audit_map_results.jsonl"


def candidates(rng, want=16, msum_cap=24):
    """Small interior points (all 28 forms >= 1), canonical-deduped,
    plus a couple of boundary points (some form = 0) for contrast."""
    interior, boundary, seen = [], [], set()
    for _ in range(200000):
        a = rng.integers(1, 5, size=8)
        hv = G.h_values(a)
        if hv.min() < 0:
            continue
        t = G.a_to_t(a)
        key = (int(t[0]),) + tuple(sorted(int(x) for x in t[1:]))
        if key in seen:
            continue
        seen.add(key)
        msum = int(np.sort(hv)[-5:].sum())
        if msum > msum_cap:
            continue
        entry = (msum, [int(x) for x in a])
        (interior if hv.min() >= 1 else boundary).append(entry)
        if len(interior) >= want and len(boundary) >= 3:
            break
    interior.sort()
    boundary.sort()
    return [a for _, a in interior[:want]] + [a for _, a in boundary[:3]]


def job(args):
    a, n = args
    t0 = time.time()
    try:
        Q, P, Phat = recover_p(a, n)
        preds = predicted_denominators(a, n)
        verdicts = {}
        for key, D in preds.items():
            ok = (D.numerator * P.numerator) % (D.denominator
                                                * P.denominator) == 0
            slack = None
            if ok:
                s = (D.numerator // D.denominator) / P.denominator \
                    if D.denominator == 1 else None
                sfr = D / P.denominator
                if sfr.denominator == 1:
                    slack = int(sfr.numerator)
            verdicts[str(key)] = {"consistent": ok, "slack": slack}
        row = {"a": a, "n": n, "Q_digits": len(str(abs(Q))),
               "denP": str(P.denominator), "denPhat": str(Phat.denominator),
               "verdicts": verdicts, "secs": round(time.time() - t0, 1)}
    except Exception as e:
        row = {"a": a, "n": n, "error": f"{type(e).__name__}: {e}",
               "trace": traceback.format_exc()[-400:],
               "secs": round(time.time() - t0, 1)}
    return row


def main():
    want = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    pool_size = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    rng = np.random.default_rng(2026)
    pts = candidates(rng, want=want)
    jobs = [(a, 1) for a in pts]
    jobs += [(a, 2) for a in pts
             if int(np.sort(G.h_values(np.array(a)))[-5:].sum()) <= 14]
    print(f"{len(pts)} points, {len(jobs)} jobs, pool={pool_size}",
          flush=True)
    with Pool(pool_size) as pool, open(RESULTS, "a") as out:
        for row in pool.imap_unordered(job, jobs):
            out.write(json.dumps(row) + "\n")
            out.flush()
            if "error" in row:
                print(f"  a={row['a']} n={row['n']} ERROR {row['error']}",
                      flush=True)
            else:
                summary = {k: ("OK" if v["consistent"] else "X")
                           + (f"/s{len(str(v['slack']))}" if v["slack"]
                              and v["slack"] > 1 else "")
                           for k, v in row["verdicts"].items()}
                print(f"  a={row['a']} n={row['n']} "
                      f"den(P)~10^{len(row['denP'])} {summary} "
                      f"[{row['secs']}s]", flush=True)
    print("done", flush=True)


if __name__ == "__main__":
    main()
