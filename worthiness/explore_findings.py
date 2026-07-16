"""Per-prime exploration of the three audit findings.

For each audited point (n=1) build a per-prime ledger:
    req_p    = ord_p(den P)                     -- what reality demands
    dprod_p  = sum_i ord_p(d_{m_i})             -- what the m-selection pays
    nu_p     = group saving at p (max over S7 orbit of the factorial-ratio
               valuation), computed BOTH restricted (p^2 > m1, BZ's regime)
               and for ALL primes (the identity is exact p-adically, so the
               all-primes version is a legitimate sharper prediction)
    excess_p = req_p - (dprod_p - nu_p)         -- >0 means prediction FAILS at p
    slack_p  = (dprod_p - nu_p) - req_p         -- >0 means unexplained savings

Questions:
 1. Are all excesses at p=2?  Do they correlate with half-integer symmetric
    parameters (t-vector parity)?
 2. What does the consistent-ell set look like per point; is there a
    structural predictor in the h'/h'' split?
 3. How much slack does extending nu_p to ALL primes absorb; what primes
    carry the rest?
"""

import json
from math import gcd, isqrt

import numpy as np

import gamma as G
from audit import E_HP_IDX, E_HPP_IDX

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]


def ordp(x, p):
    e = 0
    while x % p == 0 and x > 0:
        x //= p
        e += 1
    return e


def ord_fact(N, p):
    s, q = 0, p
    while q <= N:
        s += N // q
        q *= p
    return s


def ord_dN(N, p):
    """ord_p lcm(1..N) = floor(log_p N)."""
    e, q = 0, p
    while q <= N:
        e += 1
        q *= p
    return e


def nu_p_orbit(a, n, p, restrict=True):
    hv = G.h_values(np.asarray(a, dtype=np.int64))
    m1 = int(np.sort(hv)[-1])
    if restrict and p * p <= m1 * n:
        return 0
    orbit = G.orbit_value_multisets(np.asarray(a, dtype=np.int64))
    base = sum(ord_fact(int(v) * n, p) for v in np.sort(hv[G.F_IDX]))
    best = 0
    for row in orbit:
        best = max(best, base - sum(ord_fact(int(v) * n, p) for v in row))
    return best


def selections(hv):
    """m-multisets: proven top-5 of union, and refined ell = 1..5."""
    hp = sorted((int(hv[i]) for i in E_HP_IDX), reverse=True)
    hpp = sorted((int(hv[i]) for i in E_HPP_IDX), reverse=True)
    out = {"proven": sorted((int(v) for v in hv), reverse=True)[:5]}
    for ell in range(1, 6):
        out[ell] = hp[:ell] + hpp[:5 - ell]
    return out


def main():
    rows = [json.loads(l) for l in open("audit_map_results.jsonl")
            if "error" not in l]
    rows = [r for r in rows if r["n"] == 1]
    # include the symmetric anchors from the paper
    rows.append({"a": [1] * 8, "n": 1, "denP": "4", "denPhat": "4",
                 "verdicts": {}})

    print("=" * 90)
    print("FINDING 1 — where do the violations live?  per-prime excess "
          "(req - (dprod - nu_all))")
    print("=" * 90)
    parity_table = []
    for r in rows:
        a, denP = r["a"], int(r["denP"])
        hv = G.h_values(np.array(a))
        t = G.a_to_t(np.array(a))
        parity = "half-odd s" if t[0] % 2 else "integer s"
        m = selections(hv)["proven"]
        exc = {}
        for p in PRIMES:
            if p > max(m):
                break
            req = ordp(denP, p)
            dprod = sum(ord_dN(mi, p) for mi in m)
            nu_all = nu_p_orbit(a, 1, p, restrict=False)
            e = req - (dprod - nu_all)
            if e > 0:
                exc[p] = e
        parity_table.append((parity, bool(exc)))
        if exc:
            print(f"  a={a} [{parity}]  EXCESS {exc}  denP={denP} "
                  f"m={m}")
    n_half = sum(1 for p, _ in parity_table if p == "half-odd s")
    v_half = sum(1 for p, v in parity_table if p == "half-odd s" and v)
    n_int = sum(1 for p, _ in parity_table if p == "integer s")
    v_int = sum(1 for p, v in parity_table if p == "integer s" and v)
    print(f"  violations: {v_half}/{n_half} among half-odd-s points, "
          f"{v_int}/{n_int} among integer-s points")

    print()
    print("=" * 90)
    print("FINDING 2 — consistent-ell sets and their structure")
    print("=" * 90)
    for r in rows[:-1]:
        a = r["a"]
        hv = G.h_values(np.array(a))
        hp = sorted((int(hv[i]) for i in E_HP_IDX), reverse=True)[:5]
        hpp = sorted((int(hv[i]) for i in E_HPP_IDX), reverse=True)[:5]
        cons = [k for k, v in r["verdicts"].items() if v["consistent"]]
        print(f"  a={a}  h'top5={hp} h''top5={hpp[:4]}  consistent={cons}")

    print()
    print("=" * 90)
    print("FINDING 3 — slack decomposition (proven selection)")
    print("=" * 90)
    print("point                     p: slack_restricted -> slack_all "
          "(after extending nu to all primes)")
    tot_r, tot_a = {}, {}
    for r in rows:
        a, denP = r["a"], int(r["denP"])
        hv = G.h_values(np.array(a))
        m = selections(hv)["proven"]
        parts = []
        for p in PRIMES:
            if p > max(m):
                break
            req = ordp(denP, p)
            dprod = sum(ord_dN(mi, p) for mi in m)
            s_r = (dprod - nu_p_orbit(a, 1, p, restrict=True)) - req
            s_a = (dprod - nu_p_orbit(a, 1, p, restrict=False)) - req
            if s_r != 0 or s_a != 0:
                parts.append(f"{p}: {s_r:+d}->{s_a:+d}")
                tot_r[p] = tot_r.get(p, 0) + max(s_r, 0)
                tot_a[p] = tot_a.get(p, 0) + max(s_a, 0)
        print(f"  a={a}: " + "  ".join(parts))
    print(f"\n  total positive slack by prime, restricted nu: {tot_r}")
    print(f"  total positive slack by prime, all-primes nu:  {tot_a}")


if __name__ == "__main__":
    main()
