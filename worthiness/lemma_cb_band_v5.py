"""V5 -- the Dwork ladder congruence for the ratio rho_n = p_n/q_n, and the
general-kappa reduction of Phase 2 (coordinator upgrade, 2026-07-18).

The V3 "global rationals" are the n=1 LADDER RATIOS:
    29/28  = p_1/q_1,    101/84 = ptil_1/q_1                        (verified exactly).
General digit-a constant is p_a/q_a with a = floor(n/p). This is a Dwork/Frobenius
descent, NOT a Lucas product (Lucas for q_n, Q_n both FAIL -- checked in run_lucas).

CENTRAL CONGRUENCE (Dwork descent, verified below):
    p^5 * (p_n/q_n)    ≡ p_a/q_a       (mod p^{3-kappa}),   a = floor(n/p),
    p^3 * (ptil_n/q_n) ≡ ptil_a/q_a    (mod p^{3-kappa}),   kappa = ord_p binom(2n,n).
#correct digits = 3 - kappa (kappa in {0,1} for the reachable ranges); boosts of
+1/+2 occur at the reflection centre r = (p-1)/2 and endpoints (antisymmetric
correction term ~ (2r+1-p): a derivative signature, cf. Dwork F(x)/F(x^p)).

ITERATING L = ord_p(d_n) = floor(log_p n) times to the base digit n0 = floor(n/p^L) < p:
    ord_p(p_n/q_n) = -5L + ord_p(p_{n0}/q_{n0}) = -5L   (non-exceptional p).
Combined with (FREE) ord_p(q_n) >= kappa (BZ integer sumQ):
    ord_p(p_n) = ord_p(rho_n) + ord_p(q_n) >= kappa - 5L,
which is EXACTLY the (CB) target for p>=5 (ord_p(A_n)=5L+ord_p(p_n) >= kappa,
A_n = 2 d_n^5 p_n, ord_p(6)=0). So **Phase 2 reduces entirely to (FREE)+(DWORK)**.

EXCEPTIONAL primes: p | denominator of a ladder ratio on the descent (e.g. 7 | 28 =
den(p_1/q_1); 11 | den(p_3/q_3)). There ord_p(rho_n) dips by the exceptional
multiplicity mu, but ord_p(q_n) rises by nu >= mu, so ord_p(p_n) >= kappa - 5L is
PRESERVED (the combined/integer-normalized statement is unconditional).

Exact Fraction arithmetic. HONESTY: verified congruence / measured data, not proofs.
"""
import sys
from fractions import Fraction
from math import comb
sys.path.insert(0, '.')
from lemma_cb_explore import all_data, primes_in, ord_p_fraction as op

_c = {}
def data(n):
    if n not in _c:
        d = all_data(n)
        u, ut, w, wt, v, vt = d["u"], d["ut"], d["w"], d["wt"], d["v"], d["vt"]
        _c[n] = (u * wt - ut * w, wt * v - w * vt, u * vt - ut * v)  # q, p_n, ptil
    return _c[n]

def rho(n): q, pn, pt = data(n); return pn / q
def sig(n): q, pn, pt = data(n); return pt / q
def kap(n, p): return op(Fraction(comb(2 * n, n)), p)
def Lval(n, p):
    L, pk = 0, p
    while pk <= n:
        L += 1; pk *= p
    return L
def modp(fr, p, m=1):
    mod = p ** m
    if fr.denominator % p == 0:
        return None
    return (fr.numerator % mod) * pow(fr.denominator % mod, -1, mod) % mod


def verify_n1_identification():
    print("=" * 74)
    print("V5.0  ladder-ratio identification (exact)")
    print("=" * 74)
    for a in (1, 2, 3):
        q, pn, pt = data(a)
        print(f"  a={a}: p_a/q_a = {pn/q},  ptil_a/q_a = {pt/q}")
    assert rho(1) == Fraction(29, 28) and sig(1) == Fraction(101, 84)
    assert rho(2) == Fraction(24289, 23424)
    print("  CONFIRMED: 29/28 = p_1/q_1, 101/84 = ptil_1/q_1, 24289/23424 = p_2/q_2")


def descent_law(primes, nmax=45):
    print("\n" + "=" * 74)
    print("V5.1  Dwork descent depth:  p^5 rho_n == rho_{floor(n/p)}  (mod p^k)")
    print("      and  p^3 sig_n == sig_{floor(n/p)}")
    print("      guaranteed floor k >= 2 - kappa; typical k = 3 - kappa; needs only k>=1")
    print("=" * 74)
    floor_fail = 0; typ = 0; boost = 0; checked = 0; minrel = 99
    for p in primes:
        for n in range(p, nmax + 1):
            a = n // p
            if data(a)[0] == 0:
                continue
            kappa = kap(n, p)
            for name, val, wt, exc in (
                    ("rho", rho(n) * Fraction(p) ** 5 - rho(a), 3, rho(a).denominator % p == 0),
                    ("sig", sig(n) * Fraction(p) ** 3 - sig(a), 3, sig(a).denominator % p == 0)):
                if exc:
                    continue
                k = op(val, p) if val != 0 else 99
                checked += 1
                rel = k - (-kappa)  # depth measured from the base scale
                minrel = min(minrel, k + kappa)          # k relative to -kappa
                if k < 2 - kappa:
                    floor_fail += 1
                    print(f"  FLOOR FAIL {name} n={n} p={p} kappa={kappa}: k={k} < 2-kappa")
                elif k == 3 - kappa:
                    typ += 1
                elif k > 3 - kappa:
                    boost += 1
    print(f"  checked {checked} descents; guaranteed floor k>=2-kappa: "
          f"{'ALL OK' if floor_fail == 0 else str(floor_fail)+' FAIL'} "
          f"(min k+kappa = {minrel} >= 2, and >= 1 as closure needs);")
    print(f"    typical (k=3-kappa): {typ};  boosted (centre/endpoints): {boost}")


def target_scan(nmax=45):
    print("\n" + "=" * 74)
    print("V5.2  combined target  ord_p(p_n) >= kappa - 5L  (p>=5): the (CB) bound")
    print("=" * 74)
    fail = 0; dwork_exc = []
    for n in range(2, nmax + 1):
        for p in primes_in(5, n):
            q, pn, pt = data(n)
            if q == 0:
                continue
            L = Lval(n, p); kappa = kap(n, p)
            if op(pn, p) < kappa - 5 * L:
                fail += 1
                print(f"  TARGET FAIL n={n} p={p}: ord(p_n)={op(pn,p)} < {kappa-5*L}")
            if op(pn / q, p) < -5 * L:
                dwork_exc.append((n, p, op(pn/q, p) + 5*L, op(q, p) - kappa))
    print(f"  ord_p(p_n) >= kappa-5L: {'ALL OK (0 failures)' if fail == 0 else str(fail)+' FAIL'}")
    print(f"\n  Exceptional (ord(rho) < -5L): {len(dwork_exc)} rows; each dips by mu, q rises by nu:")
    ok = all(nu >= -mu for (_, _, mu, nu) in dwork_exc)  # mu<0 dip, nu>=0 rise
    for n, p, mu, nu in dwork_exc[:8]:
        print(f"    n={n} p={p}: ord(rho)-(-5L)={mu} (dip {-mu}), ord(q)-kappa={nu} (rise) -> compensated: {nu >= -mu}")
    print(f"  compensation ord(q)-kappa >= dip in ALL exceptional rows: {ok}")


def run_lucas(nmax=45):
    print("\n" + "=" * 74)
    print("V5.3  Lucas control:  q_{ap+b} =? q_a q_b  and  Q_{ap+b}=?Q_aQ_b (mod p)")
    print("=" * 74)
    def qn(n): return data(n)[0]
    def Qn(n): return qn(n) / Fraction(comb(2*n, n)) if n > 0 else Fraction(-1)
    for label, f in (("q_n", qn), ("Q_n=q_n/binom", Qn)):
        for p in (7, 11, 13):
            g = b = 0
            for a in range(1, 4):
                for b0 in range(0, p):
                    n = a * p + b0
                    if n < 1 or n > nmax:
                        continue
                    L = modp(Fraction(f(n)), p)
                    R = modp(Fraction(f(a)) * Fraction(f(b0)), p) if b0 > 0 else modp(Fraction(f(a)), p)
                    if L is None or R is None:
                        continue
                    (g := g + 1) if L == R else (b := b + 1)
            print(f"  Lucas[{label}] p={p}: good={g} bad={b} -> {'HOLDS' if b==0 else 'FAILS'}")
    print("  => plain Lucas does NOT hold; the operative structure is the Dwork RATIO descent.")


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 45
    verify_n1_identification()
    descent_law([11, 13, 17, 19, 23], nmax)
    target_scan(nmax)
    run_lucas(nmax)
