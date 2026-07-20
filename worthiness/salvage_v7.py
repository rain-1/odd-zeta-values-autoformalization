"""V7: the master descent (D) itself (SALVAGE §S1).

   (D):  v_p(P_n) >= v_p(P_{floor(n/p)}) - 5     (p >= 5, all n),

with P_n = (-1)^{n+1} p_n / C(2n,n) the normalized weight-5 ladder.  Exact grid
p in {5,7,11,13} (+ extended), all n <= 60 with floor(n/p) >= 1.  Records the
slack distribution (how often equality) and checks the §S1 iteration assembly
(descend n -> floor(n/p) -> ... -> n_L < p) reproduces v_p(P_n) >= -5 floor(log_p n).

Any single violation of (D) = headline finding.

Usage: python3 salvage_v7.py
"""

from fractions import Fraction
from salvage_data import triple, get_all


def vp(x, p):
    if x == 0:
        return None
    fr = Fraction(x)
    num, den, v = abs(fr.numerator), fr.denominator, 0
    while num % p == 0:
        num //= p; v += 1
    while den % p == 0:
        den //= p; v -= 1
    return v


def floorlog(m, p):
    L, pw = 0, p
    while pw <= m:
        L += 1; pw *= p
    return L


def run(primes, hi=60):
    get_all(0, hi)
    P = {m: Fraction(triple(m)["P"]) for m in range(0, hi + 1)}
    print("=== V7: master descent (D)  v_p(P_n) >= v_p(P_{floor(n/p)}) - 5 ===")
    grand_viol = 0
    grand_total = 0
    for p in primes:
        total = viol = eq = strict = 0
        slack_hist = {}
        first_v = []
        for m in range(p, hi + 1):          # need floor(m/p) >= 1
            a = m // p
            vn = vp(P[m], p)
            va = vp(P[a], p)
            if vn is None or va is None:
                continue
            total += 1
            slack = vn - (va - 5)           # (D) says slack >= 0
            slack_hist[slack] = slack_hist.get(slack, 0) + 1
            if slack < 0:
                viol += 1
                if len(first_v) < 8:
                    first_v.append((m, a, vn, va, slack))
            elif slack == 0:
                eq += 1
            else:
                strict += 1
        grand_viol += viol
        grand_total += total
        hist = dict(sorted(slack_hist.items()))
        print(f"  p={p:>2}: {total} descents, {viol} VIOLATIONS, "
              f"{eq} tight (slack 0), {strict} slack>0; slack histogram {hist}")
        if first_v:
            print("     violations (n, floor(n/p), v_p(P_n), v_p(P_a), slack):", first_v)
    print(f"  TOTAL {grand_total} descents, {grand_viol} violations -> "
          f"{'(D) HOLDS on the grid' if grand_viol == 0 else 'VIOLATION = HEADLINE'}")
    return grand_viol == 0


def assembly_check(primes, hi=60):
    """§S1: iterate (D) down the digit chain and check the endpoint bound
       v_p(P_n) >= -5 floor(log_p n), plus the terminal (n_L < p) integrality."""
    get_all(0, hi)
    P = {m: Fraction(triple(m)["P"]) for m in range(0, hi + 1)}
    print("\n=== V7: §S1 iteration assembly ===")
    for p in primes:
        bad_bound = bad_term = 0
        examples = []
        for m in range(1, hi + 1):
            # iterate the chain
            chain = [m]
            while chain[-1] >= p:
                chain.append(chain[-1] // p)
            nL = chain[-1]                    # < p
            L = len(chain) - 1                # = floor(log_p m)
            assert L == floorlog(m, p)
            vn = vp(P[m], p)
            # endpoint: n_L < p so 2 n_L < 2p; P_{n_L} p-integral when 2 n_L < p,
            # else the Phase-1 Frobenius certificate supplies it (n_L < p <= 2 n_L)
            vterm = vp(P[nL], p) if nL >= 1 else 0
            if vterm is not None and vterm < 0:
                bad_term += 1
                if len(examples) < 4:
                    examples.append(("term", nL, vterm))
            # assembled bound from iterating (D):  vn >= vterm - 5 L
            if vn is not None and vn < vterm - 5 * L:
                bad_bound += 1
            # final law:  vn >= -5 L
            if vn is not None and vn < -5 * L:
                bad_bound += 1
        print(f"  p={p:>2}: assembled bound v_p(P_n) >= v_p(P_nL) - 5L and "
              f">= -5L: {bad_bound} failures; terminal P_nL non-integral: "
              f"{bad_term}", examples if examples else "")


if __name__ == "__main__":
    ok = run((5, 7, 11, 13, 17, 19, 23), 60)
    assembly_check((5, 7, 11, 13), 60)
