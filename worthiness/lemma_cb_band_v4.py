"""V4 -- Reduction to the finite head-window congruence list, and the window
E_M / Frobenius certificate test.

Findings feeding V4 (from V1-V3, exact arithmetic):
  * n = p + r, band r in [ceil(p/2), p-1]; only multiple of p in [1,n] is p.
  * ord_p(S_i^head) = i - 5 for i=2..6 (S_i^head := sum_{j=0}^r a_{i,j}); S_1 deep-integral.
  * v = Sing + resid, Sing := sum_i p^{-i}(-1)^{i+1} S_i^head (the H-tail singular part),
    resid := sum_{i,j} a_{i,j} Hhat_j^{(i)} has ord_p >= -2  (a-singularity residue, V1).
  * Universal constants (V3):  rho_p = 29/28 * p^{-5},  sig_p = 101/84 * p^{-3}.

THE CLOSING CHAIN (all congruences verified exactly below; band target ord_p(p_n) >= kappa-5 = -4):
  (G1) HW  : Sing            ≡ rho_p u_n + sig_p w_n   (mod p^0)   [deep head-window]
  (G1~) HW~: Sing~           ≡ rho_p ut_n + sig_p wt_n (mod p^0)
  (G2) resid, resid~ have ord_p >= -2                              [a-singularity residue]
       => (Z_p): v ≡ rho_p u + sig_p w, vt ≡ rho_p ut + sig_p wt   (mod p^{-2})
  (G3) ord_p(w), ord_p(wt) >= -2                                   [Zudilin, proved]
  (G4) ord_p(q_n) >= kappa = 1                                     [FREE, BZ sumQ]
  Then p_n = rho_p q_n + (wt*E_v - w*E_vt), ord(error) >= ord(wt)+ord(E_v) >= -2 + -2 = -4,
  and ord(rho_p q_n) = -5 + kappa = -4, so ord_p(p_n) >= -4.  QED(band).

The remaining PROOF obligation is (G1)/(G1~): the explicit head-window congruences,
with the explicit rationals 29/28, 101/84. Leading mod-p form (verified):
  p^5 * Sing ≡ (29/28) u + (101/84) p^2 w   (mod p).
V4(C) tests whether the exact infinity-vanishing relations E_M (over Q; = 0 on the
true coefficient vector) FORCE (G1) -- i.e. whether the mod-p^K functional p^6*HW is
in the Z/p^K-module span of {E_M}, mimicking lemma_cb_certificate.py at module level.
"""
import sys
from fractions import Fraction
sys.path.insert(0, '.')
from lemma_cb_explore import all_data, primes_in, ord_p_fraction

RHO = Fraction(29, 28)
SIG = Fraction(101, 84)


def band_primes(n):
    return [p for p in primes_in(n // 2 + 1, (2 * n) // 3) if p >= 5]


def head(a, i, r):
    return sum((a[i, j] for j in range(r + 1)), Fraction(0))


# ---------- parts A/B: ladder + closing-chain verification ----------

def partsAB(lo, hi, pmax):
    print("=" * 78)
    print("V4(A/B): S_i^head ladder + closing-chain congruences (exact ord_p)")
    print("=" * 78)
    print(f"{'n':>3} {'p':>3} {'r':>3} | ordS: {'S2':>3}{'S3':>3}{'S4':>3}{'S5':>3}{'S6':>3} | "
          f"{'HW':>4}{'HW~':>4}{'res':>4}{'res~':>4}{'Zv':>4}{'Zv~':>4} | "
          f"{'p_n-rq':>7} need>=-4")
    worst = {"HW": 99, "HW~": 99, "res": 99, "res~": 99, "Zv": 99, "Zv~": 99, "prox": 99}
    for n in range(lo, hi + 1):
        for p in band_primes(n):
            if p > pmax:
                continue
            d = all_data(n)
            a, at = d["a"], d["at"]
            r = n - p
            u, ut, w, wt = d["u"], d["ut"], d["w"], d["wt"]
            v, vt, q = d["v"], d["vt"], d["u"] * d["wt"] - d["ut"] * d["w"]
            pn = wt * v - w * vt
            rp, sp = RHO * Fraction(p) ** -5, SIG * Fraction(p) ** -3
            Sing = sum((Fraction((-1) ** (i + 1), p ** i) * head(a, i, r) for i in range(1, 7)), Fraction(0))
            Singt = sum((Fraction((-1) ** (i + 1), p ** i) * head(at, i, r) for i in range(1, 7)), Fraction(0))
            HW = Sing - rp * u - sp * w
            HWt = Singt - rp * ut - sp * wt
            res, rest = v - Sing, vt - Singt
            Zv, Zvt = v - rp * u - sp * w, vt - rp * ut - sp * wt
            prox = pn - rp * q
            def o(x): return ord_p_fraction(x, p) if x != 0 else 99
            vals = {"HW": o(HW), "HW~": o(HWt), "res": o(res), "res~": o(rest),
                    "Zv": o(Zv), "Zv~": o(Zvt), "prox": o(prox)}
            for k in worst:
                worst[k] = min(worst[k], vals[k])
            oS = [ord_p_fraction(head(a, i, r), p) if head(a, i, r) != 0 else 99 for i in range(2, 7)]
            print(f"{n:>3} {p:>3} {r:>3} |       "
                  + "".join(f"{x:>3}" for x in oS)
                  + f" | {vals['HW']:>4}{vals['HW~']:>4}{vals['res']:>4}{vals['res~']:>4}"
                  f"{vals['Zv']:>4}{vals['Zv~']:>4} | {vals['prox']:>7}")
    print("\nWORST-CASE ords across the whole band table:")
    print(f"  HW >= {worst['HW']}, HW~ >= {worst['HW~']}   (need >= 0 for the deep congruence)")
    print(f"  resid >= {worst['res']}, resid~ >= {worst['res~']}   (need >= -2)")
    print(f"  Z_p(v) >= {worst['Zv']}, Z_p(vt) >= {worst['Zv~']}   (=> theta = {min(worst['Zv'],worst['Zv~'])})")
    print(f"  PROX ord(p_n - rho_p q_n) >= {worst['prox']}   (need >= -4: band target)")
    band_ok = worst['prox'] >= -4
    print(f"  ==> BAND TARGET ord_p(p_n) >= -4 : {'CLOSES (margin '+str(worst['prox']+4)+')' if band_ok else 'FAILS'}")


# ---------- part C: module-level E_M certificate for HW ----------

def Cneg(i, r):
    v = Fraction(1)
    for x in range(r):
        v *= Fraction(-i - x, x + 1)
    return int(v)


def module_span_reduce(rows, target, K, p):
    """Is `target` in the Z/p^K-module span of `rows`? Valuation-aware elimination.
    Returns (in_span, max_order_forced): reduces target; residual ord_p tells to what
    p-power HW is forced."""
    mod = p ** K
    R = [[x % mod for x in row] for row in rows]
    ncol = len(target)
    piv_cols = []
    used = [False] * len(R)
    # build echelon by valuation
    def val(x):
        if x % mod == 0:
            return K
        v = 0
        while x % p == 0:
            x //= p; v += 1
        return v
    basis = []  # (row, pivcol, pivval)
    for col in range(ncol):
        # pick unused row with minimal valuation at col
        best, bestv = None, K
        for ri in range(len(R)):
            if used[ri]:
                continue
            vv = val(R[ri][col])
            if vv < bestv:
                bestv, best = vv, ri
        if best is None or bestv == K:
            continue
        used[best] = True
        prow = R[best]
        basis.append((prow, col, bestv))
        # eliminate this column from all other rows where possible
        pu = (prow[col] // p ** bestv) % mod  # unit part
        pu_inv = pow(pu % (p ** (K)), -1, p ** K)
        for ri in range(len(R)):
            if ri == best or used[ri]:
                continue
            e = R[ri][col]
            if e % mod == 0:
                continue
            ev = val(e)
            if ev >= bestv:
                f = ((e // p ** bestv) * pu_inv) % mod  # so f*pivunit*p^bestv = e
                R[ri] = [(R[ri][k] - f * prow[k]) % mod for k in range(ncol)]
    # reduce target against basis
    t = [x % mod for x in target]
    for prow, col, bestv in basis:
        e = t[col]
        if e % mod == 0:
            continue
        ev = val(e)
        if ev >= bestv:
            pu = (prow[col] // p ** bestv) % mod
            pu_inv = pow(pu, -1, p ** K)
            f = ((e // p ** bestv) * pu_inv) % mod
            t = [(t[k] - f * prow[k]) % mod for k in range(ncol)]
    # residual valuation = to what p-power target is forced 0
    resid_val = min((val(x) for x in t), default=K)
    return resid_val >= K, resid_val


def partC(n, p, K=6, window=False):
    d = all_data(n)
    r = n - p
    N = n + 1
    dim = 6 * N
    idx = lambda i, j: (i - 1) * N + j
    # E_M rows over Z (then mod p^K)
    rows = []
    for M in range(1, 4 * n + 5):
        row = [0] * dim
        for i in range(1, min(6, M) + 1):
            rr = M - i
            c = Cneg(i, rr)
            for j in range(N):
                row[idx(i, j)] += c * (j ** rr if rr else 1)
        if window:
            # window-restrict: keep only j<=r columns (Frobenius on [0,r])
            for i in range(1, 7):
                for j in range(r + 1, N):
                    row[idx(i, j)] = 0
        rows.append(row)
    # target functional  p^6 * HW  (integers; denom 28,84 cleared by 2352, coprime to p>=11)
    L = 2352  # lcm(28,84)
    tgt = [0] * dim
    for i in range(1, 7):
        coeff = (-1) ** (i + 1) * L * p ** (6 - i)
        for j in range(r + 1):
            tgt[idx(i, j)] += coeff
    for j in range(N):  # - (29/28) p * u  ,  u = sum a_{5,j}
        tgt[idx(5, j)] += -(L // 28 * 29) * p
    for j in range(N):  # - (101/84) p^3 * w , w = sum a_{3,j}
        tgt[idx(3, j)] += -(L // 84 * 101) * p ** 3
    in_span, rv = module_span_reduce(rows, tgt, K, p)
    return in_span, rv, K


def run_C(pairs, K=6):
    print("\n" + "=" * 78)
    print(f"V4(C): does the E_M infinity-machinery force HW mod p^{K}?  (module span test)")
    print("  target = 2352 * p^6 * HW  (HW = Sing - rho_p u - sig_p w); E_M = exact relations")
    print("=" * 78)
    for (n, p) in pairs:
        for window in (False, True):
            in_span, rv, K_ = partC(n, p, K, window)
            tag = "WINDOW E_M ([0,r] cols)" if window else "FULL E_M"
            print(f"  n={n:3d} p={p:3d} [{tag:24s}]: HW forced mod p^{rv}"
                  f"  (target 0 mod p^{K}? {'YES -> certificate' if in_span else 'NO'})")


if __name__ == "__main__":
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 45
    pmax = int(sys.argv[3]) if len(sys.argv) > 3 else 23
    partsAB(lo, hi, pmax)
    run_C([(17, 11), (20, 13), (26, 17), (29, 19), (35, 23)], K=6)
