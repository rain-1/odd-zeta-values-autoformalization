"""V1 (cross-product identity) + V2 (double-binomial formula) + V3 (Lucas).

V1: verify (q_n, p_n, p̃_n) equals the cross product (u,w,v) x (ũ,w̃,ṽ) up to the
    exact per-component sign, recording the sign convention.
V2: verify Brown-Zudilin's manifestly-integral double-binomial formula
        Q_n = Σ_{k,l=0}^n C(n+k,n)C(n,k)² C(n+l,n)C(n,l)² C(n+k+l,n)
    against the normalized q-data Q_n = (-1)^{n+1} q_n / C(2n,n).
V3: verify the Lucas-Frobenius congruence  Q_{ap+r} ≡ Q_a Q_r (mod p)  on a wide
    grid (single-digit and iterated two-digit forms).

Usage: python3 salvage_v123.py
"""

from math import comb
from salvage_data import triple, get_all


def Q_double(n):
    """Brown-Zudilin double-binomial integer formula."""
    tot = 0
    Ck = [comb(n + k, n) * comb(n, k) ** 2 for k in range(n + 1)]
    for k in range(n + 1):
        ak = Ck[k]
        for l in range(n + 1):
            tot += ak * Ck[l] * comb(n + k + l, n)
    return tot


def Q_double_mod(n, p):
    """Same formula reduced mod p (fast, small ints)."""
    tot = 0
    Ck = [(comb(n + k, n) * comb(n, k) ** 2) % p for k in range(n + 1)]
    for k in range(n + 1):
        ak = Ck[k]
        if ak == 0:
            continue
        for l in range(n + 1):
            tot = (tot + ak * Ck[l] * (comb(n + k + l, n) % p)) % p
    return tot % p


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def v1_crossproduct(hi=24):
    get_all(0, hi)
    print("=== V1: cross-product identity (q,p,p̃) vs (u,w,v)×(ũ,w̃,ṽ) ===")
    # correspondence is a cyclic shift: q<->cross_3, p<->cross_1, p̃<->cross_2
    signs = {}
    ok = True
    for n in range(1, hi + 1):
        d = triple(n)
        a = (d["u"], d["w"], d["v"])
        b = (d["ut"], d["wt"], d["vt"])
        c1, c2, c3 = cross(a, b)
        # sign of q/c3, p/c1, p̃/c2
        def sgn(gi, ci):
            if ci == 0:
                return "0" if gi == 0 else "??"
            r = gi / ci
            return "+1" if r == 1 else ("-1" if r == -1 else str(r))
        s = (sgn(d["q"], c3), sgn(d["p"], c1), sgn(d["pt"], c2))
        signs.setdefault(s, []).append(n)
    for sig, ns in signs.items():
        print(f"  signs (q/cross_3, p/cross_1, p̃/cross_2) = {sig}  for n in "
              f"{ns[0]}..{ns[-1]} ({len(ns)} values)")
    # explicit exact statement check
    for n in range(1, hi + 1):
        d = triple(n)
        a = (d["u"], d["w"], d["v"])
        b = (d["ut"], d["wt"], d["vt"])
        c1, c2, c3 = cross(a, b)
        # expected: q=+c3, p=-c1, p̃=-c2
        if not (d["q"] == c3 and d["p"] == -c1 and d["pt"] == -c2):
            ok = False
            print(f"  MISMATCH at n={n}")
    print(f"  EXACT relation q=+(a×b)_3, p=-(a×b)_1, p̃=-(a×b)_2 : "
          f"{'HOLDS' if ok else 'FAILS'} for n=1..{hi}")
    return ok


def v2_double_binomial(hi=24):
    get_all(0, hi)
    print("\n=== V2: double-binomial formula vs normalized q-data ===")
    ok = True
    for n in range(0, hi + 1):
        d = triple(n)
        Qd = Q_double(n)
        Qn = d["Q"]
        match = (Qn == Qd)
        ok = ok and match
        if n <= 6 or not match:
            print(f"  n={n:>2}  Q_double={Qd}  Q_norm={Qn}  match={match}")
    print(f"  Q_n = Σ C(n+k,n)C(n,k)²C(n+l,n)C(n,l)²C(n+k+l,n)  "
          f"{'VERIFIED' if ok else 'FAILS'} for all n=0..{hi} (integers)")
    return ok


def v3_lucas(primes=(5, 7, 11, 13)):
    print("\n=== V3: Lucas-Frobenius congruence  Q_{ap+r} ≡ Q_a·Q_r (mod p) ===")
    overall_ok = True
    total = 0
    for p in primes:
        Qm = {}

        def Q(m):
            if m not in Qm:
                Qm[m] = Q_double_mod(m, p)
            return Qm[m]

        fails = []
        cnt = 0
        # single-digit form: a in 0..12 (include a=p), r in 0..p-1
        avals = list(range(0, 13)) + [p]
        for a in avals:
            for r in range(0, p):
                m = a * p + r
                lhs = Q(m)
                rhs = Q(a) * Q(r) % p
                cnt += 1
                if lhs != rhs:
                    fails.append((a, r, m, lhs, rhs))
        # iterated two-digit: n = a2 p^2 + a1 p + a0, check Q ≡ Q_a2 Q_a1 Q_a0
        it_cnt = 0
        it_fail = []
        a2max = 3
        for a2 in range(0, a2max):
            for a1 in range(0, p):
                for a0 in range(0, p):
                    m = a2 * p * p + a1 * p + a0
                    if m == 0:
                        continue
                    lhs = Q(m)
                    rhs = Q(a2) * Q(a1) % p * Q(a0) % p
                    it_cnt += 1
                    if lhs != rhs:
                        it_fail.append((a2, a1, a0, m))
        total += cnt + it_cnt
        ok = not fails and not it_fail
        overall_ok = overall_ok and ok
        print(f"  p={p:>2}: single/two-digit  {cnt} checks, {len(fails)} fail; "
              f"iterated 3-digit  {it_cnt} checks, {len(it_fail)} fail  -> "
              f"{'PASS' if ok else 'FAIL'}")
        if fails:
            print("     first single-digit failures:", fails[:5])
        if it_fail:
            print("     first iterated failures:", it_fail[:5])
    print(f"  TOTAL {total} congruence checks -> "
          f"{'ALL PASS' if overall_ok else 'FAILURES FOUND'}")
    return overall_ok


if __name__ == "__main__":
    r1 = v1_crossproduct(24)
    r2 = v2_double_binomial(24)
    r3 = v3_lucas((5, 7, 11, 13))
    print("\nSUMMARY: V1", "OK" if r1 else "FAIL",
          "| V2", "OK" if r2 else "FAIL",
          "| V3", "OK" if r3 else "FAIL")
