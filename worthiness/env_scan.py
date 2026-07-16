"""Ceiling of the *conjectural* refined-denominator gamma (BZ Remark on m_i).

BZ conjecture (Remark \\ref{m_i}) that for some ell in {1..5} the true
denominator uses m_1 >= ... >= m_ell = successive maxima of the 21-multiset
h' and m_{ell+1} >= ... >= m_5 = successive maxima of the 7-multiset h''.
Smaller sum(m) => smaller C2 => larger gamma.  The most favorable legal
choice over ell upper-bounds any gamma obtainable if the conjecture holds:

    gamma_env(a) = (C1 - C0) / (C1 + min_ell C2_ell)  >=  gamma_refined(a).

This script evaluates the envelope at the record point and hill-climbs it
over the cone, giving a hard ceiling for "denominator creativity" inside
the BZ family.
"""

import numpy as np

import gamma as G
import search as S

# 0-based indices of h' (orbit of a1, 21 elements) and h'' (orbit of a2, 7).
HP_IDX = [0, 2, 4, 5, 6, 7, 8, 9, 10, 13, 15, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27]
HPP_IDX = [1, 3, 11, 12, 14, 16, 23]


def gamma_envelope(a, full=False):
    a = np.asarray(a, dtype=np.int64)
    hv = G.h_values(a)
    if not np.all(hv >= 0):
        return -np.inf
    l1, l2, l3 = G.asymptotics(a)
    C0, C1 = l2, l3
    phil = G.phi_limit(a)
    hp = np.sort(hv[HP_IDX])[::-1]
    hpp = np.sort(hv[HPP_IDX])[::-1]
    options = {}
    for ell in range(1, 6):
        if 5 - ell > len(hpp):
            continue
        msum = int(hp[:ell].sum() + hpp[:5 - ell].sum())
        options[ell] = (C1 - C0) / (C1 + msum - phil)
    naive_msum = int(np.sort(hv)[-5:].sum())
    g_naive = (C1 - C0) / (C1 + naive_msum - phil)
    g_env = max(options.values())
    if full:
        return {"gamma_naive": g_naive, "gamma_envelope": g_env,
                "by_ell": options,
                "best_ell": max(options, key=options.get)}
    return g_env


def main():
    print("record point a = (8,16,10,15,12,16,18,13):")
    d = gamma_envelope(np.array([8, 16, 10, 15, 12, 16, 18, 13]),
                       full=True)
    print(f"  proven-m gamma   = {d['gamma_naive']:.8f}")
    for ell, g in sorted(d["by_ell"].items()):
        print(f"  ell={ell}: gamma = {g:.8f}")
    print(f"  envelope         = {d['gamma_envelope']:.8f} (ell={d['best_ell']})")

    # Hill-climb the envelope objective over the cone.
    S._cache.clear()

    def gamma_t_env(t):
        tc = S.canonical(t)
        if tc in S._cache:
            return S._cache[tc]
        if not S.admissible_t(tc):
            S._cache[tc] = -np.inf
            return -np.inf
        try:
            g = gamma_envelope(G.t_to_a(np.array(tc)))
        except Exception:
            g = -np.inf
        S._cache[tc] = g
        return g

    S.gamma_t = gamma_t_env  # hill_climb reads the module-level name

    rng = np.random.default_rng(777)
    best, best_g = None, -np.inf
    t_bz = S.canonical(G.a_to_t(np.array(S.BZ_A)))
    for tag, start in [("bz", t_bz)] + [
            ("rand", S.random_start(rng)) for _ in range(40)]:
        top, g = S.hill_climb(start, first_improvement=(tag == "rand"))
        if tag != "rand":
            top, g = S.hill_climb(top)
        marker = " <-- new best" if g > best_g else ""
        if g > best_g:
            best, best_g = top, g
        print(f"[{tag}] start={start} -> envelope gamma={g:.8f}{marker}",
              flush=True)
    print(f"\nsup envelope gamma (this search) = {best_g:.8f} at t={best}")
    print(f"a = {G.t_to_a(np.array(best)).tolist()}")


if __name__ == "__main__":
    main()
