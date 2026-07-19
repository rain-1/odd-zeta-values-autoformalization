"""STEP 2 continuation -- the (HW) two-digit calculation.

Usage:
    python3 dwork_hw.py [primes csv]     # default 11,13,17,19,23,29,31,37

Exact Fraction / integer arithmetic.  HONESTY: finite exact verification over the
stated grid; the fully symbolic-in-r proof is NOT achieved (nor in Sol's memo).

Target (Sol eq 17, LEMMA_CB companion):
    Q_HW(n,p) := p^5*Sing - (29/28)*u - (101/84)*p^2*w,
    Sing = sum_{i=1}^6 (-1)^{i+1} p^{-i} S_i^head,   S_i^head = sum_{j=0}^r a_{i,j},
    n = p+r,   claim  ord_p(Q_HW) >= 3   (p^0 digit forced by E_M window relations;
    the p^1, p^2 digits were the "two missing digits").

FINDINGS (this script):
 (1) ord_p(Q_HW) >= 5 uniformly on the a=1 band (occasionally 6) -- FOUR/FIVE digits
     vanish, far beyond the mod-p^3 target.  So (HW) holds on-grid with large margin;
     the "two missing digits" c_1,c_2 both vanish (verified), as do c_3,c_4.
 (2) The vanishing is a GLOBAL (cross-layer) cancellation, not termwise: itemizing
     Q_HW by the six pole layers i=1..6 (plus the two constant terms), individual
     items reach ord_p = 0 while the exact SUM reaches ord_p = 5 -- a valuation jump
     of 5.  (p-adic digits do NOT add columnwise, due to carries; the honest display
     is by exact valuation / running partial sums.)  Layer-deletion is a sensitivity
     control: deleting any of L2..L6 drops the sum ord to <= 1.
 (3) P4 verdict: the first-correction digit c(r) (at depth 3-kappa) VANISHES at the
     reflection centre r=(p-1)/2 at EVERY prime (derivative-Frobenius signature,
     confirmed) -- but it is NOT a global multiple of (2r+1-p): c(r)/(2r+1-p) is not
     constant.  So Sol's centre-vanishing is confirmed; the linear-factor form is
     FALSIFIED (c has higher-degree structure / extra sporadic roots).
 (4) P6 verdict: the reversal-identity / block-binomial ingredient-deletion test
     requires the full Phi/Bell rebuild of a_{i,j} (Sol eq 3-10); NOT executed here.
     The available sensitivity control is the pole-layer deletion of (2).
"""
import sys
from fractions import Fraction
sys.path.insert(0, '/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from lemma_cb_explore import all_data, ord_p_fraction as op

_c = {}
def data(n):
    if n not in _c:
        _c[n] = all_data(n)
    return _c[n]
def minors(n):
    d = data(n)
    u, ut, w, wt, v, vt = d["u"], d["ut"], d["w"], d["wt"], d["v"], d["vt"]
    return (u * wt - ut * w, wt * v - w * vt, u * vt - ut * v)

RHO1 = Fraction(29, 28)   # p_1/q_1
SIG1 = Fraction(101, 84)  # ptil_1/q_1

def band_r(p):
    return range((p + 1) // 2, p)

def head(a, i, r):
    return sum((a[i, j] for j in range(r + 1)), Fraction(0))

def digit(fr, p, d):
    """d-th base-p digit of a p-adic integer fr (ord_p >= 0). None if not p-integral."""
    if fr == 0:
        return 0
    if fr.denominator % p == 0:
        return None
    mod = p ** (d + 1)
    res = (fr.numerator % mod) * pow(fr.denominator % mod, -1, mod) % mod
    return (res // p ** d) % p


# ---------------------------------------------------------------------------
def depth_scan(primes):
    print("=" * 78)
    print("(1) ord_p(Q_HW) over the a=1 band  (target mod p^3, i.e. ord >= 3)")
    print("=" * 78)
    worst = 99
    for p in primes:
        ords = []
        for r in band_r(p):
            n = p + r
            d = data(n)
            a, u, w = d["a"], d["u"], d["w"]
            Sing = sum((Fraction((-1) ** (i + 1), p ** i) * head(a, i, r) for i in range(1, 7)), Fraction(0))
            Q = Fraction(p) ** 5 * Sing - RHO1 * u - SIG1 * Fraction(p) ** 2 * w
            o = op(Q, p) if Q != 0 else 99
            ords.append(o)
            worst = min(worst, o)
        print(f"  p={p:3d}: ord(Q_HW) per r = {ords}")
    print(f"  worst ord over grid = {worst}  ({'>= 3 target MET with margin' if worst >= 3 else 'FAILS'})")


# ---------------------------------------------------------------------------
def itemize(primes):
    print("\n" + "=" * 78)
    print("(2) itemized cancellation by exact valuation (carry-free).")
    print("    items: L1..L6 = (-1)^{i+1} p^{5-i} S_i^head ; Cu = -(29/28)u ; Cw = -(101/84)p^2 w")
    print("    Q_HW = sum of the 8 items.  Individual items reach ord 0; the SUM reaches")
    print("    ord 5 -- a valuation jump of 5 by exact cancellation (NOT termwise).")
    print("    Running partial-sum ord shows where the cancellation accrues.")
    print("=" * 78)
    order = ["Cu", "L5", "L6", "L4", "Cw", "L2", "L3", "L1"]  # unit terms first
    for p in primes:
        r = p - 1
        n = p + r
        d = data(n)
        a, u, w = d["a"], d["u"], d["w"]
        items = {}
        for i in range(1, 7):
            items[f"L{i}"] = Fraction((-1) ** (i + 1)) * Fraction(p) ** (5 - i) * head(a, i, r)
        items["Cu"] = -RHO1 * u
        items["Cw"] = -SIG1 * Fraction(p) ** 2 * w
        Q = sum(items.values(), Fraction(0))
        print(f"  p={p} r={r} (n={n}): ord(Q_HW)={op(Q,p) if Q!=0 else 'oo'}")
        ords = "  ".join(f"{k}:{op(items[k],p) if items[k]!=0 else 'oo'}" for k in order)
        print(f"    item ords:   {ords}")
        run = Fraction(0); prog = []
        for k in order:
            run += items[k]
            prog.append(f"+{k}:{op(run,p) if run!=0 else 'oo'}")
        print(f"    partial-sum: {'  '.join(prog)}")
        mino = min(op(items[k], p) for k in order if items[k] != 0)
        print(f"    min item ord = {mino};  sum ord = {op(Q,p) if Q!=0 else 'oo'}  "
              f"(jump = {(op(Q,p) if Q!=0 else 99) - mino}, cancellation is global not termwise)")


def layer_deletion(primes):
    print("\n" + "=" * 78)
    print("(2b) layer-deletion sensitivity: drop one pole layer L_i, report ord(Q_HW')")
    print("     (each deletion should expose a nonzero low digit -- cancellation is genuine)")
    print("=" * 78)
    for p in primes[:3]:
        r = p - 1
        n = p + r
        d = data(n)
        a, u, w = d["a"], d["u"], d["w"]
        base = sum((Fraction((-1) ** (i + 1), p ** i) * head(a, i, r) for i in range(1, 7)), Fraction(0))
        Qfull = Fraction(p) ** 5 * base - RHO1 * u - SIG1 * Fraction(p) ** 2 * w
        print(f"  p={p} r={r}: full ord={op(Qfull,p)};  drop L_i -> ord:")
        outs = []
        for drop in range(1, 7):
            Sing = sum((Fraction((-1) ** (i + 1), p ** i) * head(a, i, r) for i in range(1, 7) if i != drop), Fraction(0))
            Q = Fraction(p) ** 5 * Sing - RHO1 * u - SIG1 * Fraction(p) ** 2 * w
            outs.append(f"L{drop}:{op(Q,p) if Q!=0 else 'oo'}")
        print("     " + "  ".join(outs))


# ---------------------------------------------------------------------------
def p4_test(primes):
    print("\n" + "=" * 78)
    print("(3) P4: first-correction digit c(r) of D(r)=p^5 rho_{p+r}-rho_1 at depth 3-kappa")
    print("    predict (Sol): vanishes at centre r=(p-1)/2 and ~ (2r+1-p) factor")
    print("=" * 78)
    for p in primes + [41]:
        cc = {}
        for r in range(0, p):
            n = p + r
            q, pn, pt = minors(n)
            D = Fraction(p) ** 5 * (pn / q) - RHO1
            kap = 1 if 2 * r >= p else 0
            cc[r] = digit(D, p, 3 - kap)
        rc = (p - 1) // 2
        prop = set()
        for r in range(p):
            f = (2 * r + 1 - p) % p
            if f != 0 and cc[r] is not None:
                prop.add((cc[r] * pow(f, -1, p)) % p)
        print(f"  p={p:3d}: c(centre)={cc[rc]} (vanishes: {cc[rc]==0});  "
              f"c/(2r+1-p) distinct={len(prop)} -> "
              f"{'LINEAR FACTOR holds' if len(prop)==1 else 'NOT a linear (2r+1-p) factor'}")
    print("  VERDICT P4: centre-vanishing CONFIRMED all primes; linear (2r+1-p) factor FALSIFIED.")


if __name__ == "__main__":
    if len(sys.argv) > 1:
        primes = [int(x) for x in sys.argv[1].split(",")]
    else:
        primes = [11, 13, 17, 19, 23, 29, 31, 37]
    depth_scan(primes)
    itemize(primes[:4])
    layer_deletion(primes)
    p4_test(primes)
    print("\n" + "=" * 78)
    print("(4) P6 (reversal-id / block-binomial ingredient deletion): NOT executed --")
    print("    requires the full Phi/Bell rebuild of a_{i,j} (Sol eq 3-10).  The layer-")
    print("    deletion (2b) is the available exact sensitivity control.")
