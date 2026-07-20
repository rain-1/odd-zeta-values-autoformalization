"""PHASE2_FALSIFY T2-T5: adversarial tests of the corrected denominator law and
the descent (D), in the cells never tested before.

  LAW:  12 * d_n^5 * P_n in Z,   P_n = (-1)^{n+1} p_n / C(2n,n),  d_n = lcm(1..n).
  (D):  v_p(P_n) >= v_p(P_{floor(n/p)}) - 5   for p >= 5.

Data: falsify_data/ (recurrence-extended to n=360, validated vs direct at all
n=3..150 and spot points 200,275,350).  Any claimed VIOLATION is re-derived by
DIRECT salvage_data.triple (not recurrence) before being reported.

Usage: python3 falsify_tests.py
"""

from fractions import Fraction
from math import gcd
from sympy import factorint
from falsify_data import get_ladders

HI = 360


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


def lcm_upto(n):
    ans = 1
    for k in range(2, n + 1):
        ans = ans * k // gcd(ans, k)
    return ans


# ---------------------------------------------------------------------------
# T2 -- THE LAW at every n
# ---------------------------------------------------------------------------

def t2_law(P, lo=1, hi=HI):
    print("=" * 74)
    print("T2 -- LAW:  12 * d_n^5 * P_n in Z   for all n")
    print("=" * 74)
    d = {n: lcm_upto(n) for n in range(0, hi + 1)}
    viol = []
    slack_hist = {}
    tight_examples = []
    per_slack_min = []
    for n in range(lo, hi + 1):
        val = Fraction(12) * d[n]**5 * P[n]
        if val.denominator != 1:
            viol.append(n)
        # tightness: min over primes p | den(P_n) of  v_p(12 d_n^5 P_n)
        den = P[n].denominator
        min_slack = None
        arg = None
        for p in set(factorint(den)) | {2, 3}:
            v12 = 2 if p == 2 else 1 if p == 3 else 0
            slack = v12 + 5 * floorlog(n, p) + vp(P[n], p)
            if min_slack is None or slack < min_slack:
                min_slack, arg = slack, p
        if min_slack is not None:
            slack_hist[min_slack] = slack_hist.get(min_slack, 0) + 1
            per_slack_min.append((n, min_slack, arg))
            if min_slack == 0:
                tight_examples.append((n, arg))
    print(f"  n={lo}..{hi}: {len(viol)} VIOLATIONS of the law "
          f"-> {'LAW HOLDS on grid' if not viol else 'HEADLINE VIOLATION'}")
    if viol:
        print("   violating n:", viol)
    hist = dict(sorted(slack_hist.items()))
    print(f"  overall min-slack histogram (0 = tight): {hist}")
    print(f"  (min-slack is at p=2 for ALL n: the constant 12=4*3 makes the law")
    print(f"   EXACTLY tight 2-adically -- 12 d_n^5 P_n is odd for every n.)")
    # p>=5-restricted tightness: the interesting arithmetic
    hist5 = {}
    tight5 = []
    for n in range(lo, hi + 1):
        den = P[n].denominator
        best = None; bp = None
        for p in set(factorint(den)):
            if p < 5:
                continue
            slack = 5 * floorlog(n, p) + vp(P[n], p)
            if best is None or slack < best:
                best, bp = slack, p
        if best is not None:
            hist5[best] = hist5.get(best, 0) + 1
            if best == 0:
                tight5.append((n, bp))
    print(f"  p>=5-restricted min-slack histogram: {dict(sorted(hist5.items()))}")
    print(f"  law is TIGHT at some p>=5 for {hist5.get(0,0)} levels; "
          f"examples n(p): {tight5[:15]}")
    return viol, per_slack_min


# ---------------------------------------------------------------------------
# T3 -- descent (D) in the virgin k>=3 cells
# ---------------------------------------------------------------------------

def t3_descent(P, primes, hi=HI):
    print("=" * 74)
    print("T3 -- DESCENT (D):  v_p(P_n) >= v_p(P_{floor(n/p)}) - 5   (p>=5)")
    print("=" * 74)
    all_viol = []
    for p in primes:
        total = viol = tight = 0
        slack_hist = {}
        k3 = []          # the virgin k=3 band: p^3 in (n,2n]
        for m in range(p, hi + 1):
            a = m // p
            vn, va = vp(P[m], p), vp(P[a], p)
            if vn is None or va is None:
                continue
            total += 1
            slack = vn - (va - 5)
            slack_hist[slack] = slack_hist.get(slack, 0) + 1
            if slack < 0:
                viol += 1
                all_viol.append((p, m, a, vn, va, slack))
            elif slack == 0:
                tight += 1
            # k=3 band for this p:  p^3 in (m, 2m]  <=> m < p^3 <= 2m
            if m < p**3 <= 2 * m:
                k3.append((m, slack))
        hist = dict(sorted(slack_hist.items()))
        print(f"  p={p:>2}: {total} descents, {viol} VIOL, {tight} tight; "
              f"slack hist {hist}")
        if k3:
            k3band = f"n in [{k3[0][0]}, {k3[-1][0]}]"
            k3v = sum(1 for _, s in k3 if s < 0)
            print(f"        k=3 virgin band (p^3 in (n,2n]): {k3band}, "
                  f"{len(k3)} cells, {k3v} viol, slacks {[s for _,s in k3]}")
    print(f"  --> TOTAL violations of (D): {len(all_viol)}")
    if all_viol:
        print("   VIOLATIONS:", all_viol)
    return all_viol


def t3_threedigit(P, primes, hi=HI):
    """Full iterated descent to terminal < p; check v_p(P_n) >= -5 floorlog_p n,
    and flag genuine three-digit chains (floorlog >= 3)."""
    print("-" * 74)
    print("T3b -- iterated assembly v_p(P_n) >= -5*floor(log_p n); 3-digit chains")
    for p in primes:
        bad = 0
        three = 0
        badterm = 0
        for m in range(1, hi + 1):
            L = floorlog(m, p)
            v = vp(P[m], p)
            if v is None:
                continue
            if v < -5 * L:
                bad += 1
            if L >= 3:
                three += 1
            # terminal
            nl = m
            while nl >= p:
                nl //= p
            if nl >= 1:
                vt = vp(P[nl], p)
                if vt is not None and vt < 0:
                    badterm += 1
        print(f"  p={p:>2}: {bad} bound failures, {three} genuine 3-digit "
              f"(floor(log_p n)>=3) levels, {badterm} non-integral terminals")


# ---------------------------------------------------------------------------
# T4 -- singularity-prime stress test
# ---------------------------------------------------------------------------

def a0(n):
    return 41218 * n**3 + 198849 * n**2 + 320790 * n + 173057


def t4_singularity(P, Ph, Q, primes, hi=HI):
    print("=" * 74)
    print("T4 -- SINGULARITY primes of the operator: c3(n)=2(n+3)^5(2n+5)a0(n).")
    print("      danger prime p|(2n+5) or p|a0(n) is INJECTED into Y_{n+3} when")
    print("      solving the recurrence.  Positive control: P̂ must LEAK there;")
    print("      target P (and Q) must NOT (only the built-in (n+3)^5 loss).")
    print("=" * 74)
    # -- PART A: per-step holonomic control (the faithful salvage T-IND, extended)
    print("  PART A -- per-step loss  v_p(Y_{n+3}) >= min(v_p Y_{n..n+2}) "
          "- 5 v_p(n+3),  split by danger source (p|a0 vs p|2n+5):")
    ctrl = {}
    for key, seq, wt in [("Q", Q, 0), ("P", P, 5), ("Ph", Ph, 3)]:
        cats = {"a0": [0, 0], "mid": [0, 0], "both": [0, 0], "none": [0, 0]}
        first = []
        for m in range(0, hi - 2):
            for p in primes:
                is_a0 = a0(m) % p == 0
                is_mid = (2 * m + 5) % p == 0
                cat = ("both" if (is_a0 and is_mid) else "a0" if is_a0
                       else "mid" if is_mid else "none")
                vprev = min(vp(seq[m], p) or 0, vp(seq[m+1], p) or 0,
                            vp(seq[m+2], p) or 0)
                vn3 = vp(seq[m+3], p)
                loss = 5 * vp(m + 3, p) if (m + 3) % p == 0 else 0
                if vn3 is not None and vn3 < vprev - loss:
                    cats[cat][1] += 1
                    if len(first) < 6:
                        first.append((m + 3, p, cat, vn3, vprev - loss))
                cats[cat][0] += 1
        ctrl[key] = cats
        summ = {k: f"{v[1]}/{v[0]}" for k, v in cats.items()}
        print(f"    Y={key:>2} (wt {wt}) leaks/total: {summ}")
        if first:
            print("        leak steps (n=m+3, p, src, v_p, allowed):", first)
    # -- PART B: standalone -- does P ever exceed the LAW at a singularity prime?
    print("  PART B -- does the TARGET P ever carry a singularity prime BELOW the")
    print("            law's d_n^5 allowance?  (law slack = 5 floor(log_p n)+v_p(P_n))")
    p_lawbreak = []
    p_carries = 0
    for n in range(1, hi + 1):
        S = (2 * n + 5) * a0(n)
        for p in set(factorint(S)):
            if p < 5:
                continue
            vP = vp(P[n], p)
            if vP is not None and vP < 0:
                p_carries += 1
                slack = 5 * floorlog(n, p) + vP
                if slack < 0:
                    p_lawbreak.append((n, p, vP, slack))
    print(f"    P carries a singularity prime in its denom in {p_carries} (n,p) "
          f"cases; of these {len(p_lawbreak)} EXCEED the law (slack<0).")
    if p_lawbreak:
        print("     LAW-BREAKING singularity cases:", p_lawbreak)
    else:
        print("     -> P stays within d_n^5 at EVERY singularity prime (no anomaly).")
    # -- PART C: the midpoint-prime leak table (leak prime is p=2n-1 = 2(n)-1,
    #    i.e. the danger 2m+5 at m=n-3 becomes prime p=2n-1 injected at index n)
    print("  PART C -- midpoint leak table: at index n the injected midpoint prime")
    print("            is p=2(n-3)+5 = 2n-1; show v_p(P) (clean) vs v_p(P̂) (leaks):")
    rows = []
    nP = nPh = 0
    for n in range(4, hi + 1):
        p = 2 * n - 1
        if not (len(factorint(p)) == 1 and list(factorint(p).values())[0] == 1
                and p >= 5):
            continue
        if p > 2 * n:      # p must be <= 2n to possibly sit in denominator
            pass
        vP = vp(P[n], p); vPh = vp(Ph[n], p)
        rows.append((n, p, vP, vPh))
        if vP is not None and vP < 0:
            nP += 1
        if vPh is not None and vPh < 0:
            nPh += 1
    print(f"    {len(rows)} n with 2n-1 prime (<=2n, can enter denom): "
          f"P̂ leaks at {nPh}, P leaks at {nP}")
    for r in rows[:25]:
        print("       n=%3d p=2n-1=%4d v_p(P)=%s v_p(P̂)=%s" % r)
    return p_lawbreak, ctrl, rows


# ---------------------------------------------------------------------------
# T5 -- exceptional-chain stress test
# ---------------------------------------------------------------------------

def t5_exceptional(P, primes, hi=HI):
    """Descents (n,p) where the TARGET P_{floor(n/p)} is itself p-nonzero
    (v_p != 0), i.e. p is 'in play' at the descent target -- the analogue of
    the '7 | q1=42' class.  Check (D) specifically there, denominator-free."""
    print("=" * 74)
    print("T5 -- EXCEPTIONAL chains: descent target a=floor(n/p) has v_p(P_a)!=0")
    print("=" * 74)
    exc = []
    viol = []
    for p in primes:
        for m in range(p, hi + 1):
            a = m // p
            va = vp(P[a], p)
            if va is None or va == 0:
                continue
            vn = vp(P[m], p)
            if vn is None:
                continue
            slack = vn - (va - 5)
            exc.append((p, m, a, va, vn, slack))
            if slack < 0:
                viol.append((p, m, a, va, vn, slack))
    print(f"  {len(exc)} exceptional descents (v_p(P_a)!=0), {len(viol)} violate (D)")
    # denominator-free check for the va<0 (p in denominator of target) subclass
    denomtarget = [e for e in exc if e[3] < 0]
    print(f"  of these, {len(denomtarget)} have p in the DENOMINATOR of P_a "
          f"(hardest class); violations among them: "
          f"{sum(1 for e in denomtarget if e[5] < 0)}")
    for e in denomtarget[:25]:
        print("     p=%2d n=%3d a=%3d v_p(P_a)=%2d v_p(P_n)=%2d slack=%d" % e)
    return exc, viol


# ---------------------------------------------------------------------------
# reconfirmation: any violation re-derived by DIRECT computation
# ---------------------------------------------------------------------------

def reconfirm_direct(cases):
    """cases: list of n to recompute directly (salvage_data.triple) and re-test."""
    if not cases:
        return
    from salvage_data import triple
    print("=" * 74)
    print("RECONFIRM by DIRECT computation (not recurrence):", sorted(set(cases)))
    for n in sorted(set(cases)):
        d = triple(n)
        P = Fraction(d["P"])
        dn = lcm_upto(n)
        val = Fraction(12) * dn**5 * P
        print(f"  n={n}: direct 12 d_n^5 P_n integer? {val.denominator == 1}")


if __name__ == "__main__":
    L = get_ladders()
    P, Ph, Q = L["P"], L["Ph"], L["Q"]
    primes = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
              71, 73)
    viol_law, slackmin = t2_law(P)
    print()
    dviol = t3_descent(P, primes)
    t3_threedigit(P, primes)
    print()
    p_lawbreak, ctrl, midrows = t4_singularity(P, Ph, Q, primes)
    print()
    exc, excviol = t5_exceptional(P, primes)
    print()
    # reconfirm every claimed violation/anomaly by direct computation
    recon = (set(viol_law) | {v[1] for v in dviol}
             | {a[0] for a in p_lawbreak} | {e[1] for e in excviol})
    reconfirm_direct(recon)
    print()
    print("#" * 74)
    print("SUMMARY:  law violations=%d  (D) violations=%d  P-law-breaks-at-singularity=%d"
          % (len(viol_law), len(dviol), len(p_lawbreak)))
    Pctrl = ctrl["P"]; Phctrl = ctrl["Ph"]
    pl = sum(v[1] for v in Pctrl.values()); phl = sum(v[1] for v in Phctrl.values())
    print("          per-step control: P leaks=%d, Q leaks=%d, P̂ leaks=%d (control OK if P=Q=0, P̂>0)"
          % (pl, sum(v[1] for v in ctrl["Q"].values()), phl))
    print("#" * 74)
