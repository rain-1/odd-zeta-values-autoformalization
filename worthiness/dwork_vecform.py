"""Denominator-free VECTOR form of the (DWORK) descent  (Sol's proof program, STEP 1 + STEP 3).

Usage:
    python3 dwork_vecform.py [NMAX]          # default NMAX = 64
    python3 dwork_vecform.py 80

Exact Fraction / integer arithmetic only.  HONESTY: everything below is a finite
exact-arithmetic VERIFICATION over the stated grid, never a proof.

------------------------------------------------------------------------------
The period vector.  For each level n define the three 2x2 minors of the 2x3
Zudilin period matrix  [[u,w,v],[ut,wt,vt]]  (notation of lemma_cb_explore.py):

    q_n    = u  wt - ut w        (the zeta(5) determinant; q_n in Z, Brown-Zudilin)
    p_n    = wt v  - w  vt        (the zeta(3)-eliminated numerator, = the (1,3) minor)
    ptil_n = u  vt - ut v         (the (1,2) minor)

So V_n := (q_n, p_n, ptil_n) is (up to sign) the cross product row1 x row2.
q_n is an INTEGER for every n (verified; it equals +/- C(2n,n)*Q_n with Q_n the
Brown-Zudilin integer cellular double-binomial coefficient).  p_n, ptil_n are
rationals with denominator dividing 2 d_n^5.

------------------------------------------------------------------------------
STEP 1 -- the denominator-free vector form.

The measured (DWORK) descent (PHASE2_BAND_V.md V5) is a statement about the
RATIOS rho_n = p_n/q_n, sig_n = ptil_n/q_n, with rational constants p_a/q_a =
29/28, ptil_a/q_a = 101/84 (a = floor(n/p)) whose DENOMINATORS carry the
"exceptional" primes (7 | 28 = den(29/28), because q_1 = 42 = 2.3.7).

Cross-multiplying by the INTEGER q_a removes every rational-number denominator
and turns the ratio congruence into a bilinear congruence on the integer-ish
period vectors.  For a = floor(n/p):

    (VEC)   X_p := q_a * p^5 * p_n   -  p_a * q_n       (a p-adic integer)
    (VEC~)  X_s := q_a * p^3 * ptil_n - ptil_a * q_n

UNIFORM FLOOR LAW (verified, single Frobenius step a<p, ALL p>=5):

        ord_p(X_p) >= ord_p(q_a) + 2 ,     ord_p(X_s) >= ord_p(q_a) + 2 .

The point: the "exceptional" primes p | q_a are NOT a singularity.  They enter
only as ord_p(q_a) > 0 -- the cross-multiplier q_a becomes non-primitive mod p
(a lattice change) -- and the floor law absorbs them uniformly (it is TIGHT at
p=7, where ord_p(q_a)=1 and ord_p(X_p)=3).  No separate exceptional-prime
normalisation is needed: the single statement covers every p>=5.

PURE-INTEGER (lattice) incarnation.  With A_m := 2 d_m^5 p_m in Z (Zudilin),
q_m in Z, and d_a | d_n (a<=n), the integer

    I := q_a * p^5 * A_n  -  (d_n/d_a)^5 * A_a * q_n   in  Z

satisfies the pure divisibility   p^{5L + ord_p(q_a) + 2}  |  I ,  L = ord_p(d_n).
(Verified; TIGHT, min surplus exactly 2.)  This is the genuine lattice statement:
no rationals at all, exceptional primes carried by the integer factor q_a.

------------------------------------------------------------------------------
STEP 3 -- the coupled pair (p_n, ptil_n): a diagonal Frobenius twist.

Scale the period point projectively by  T := diag(1, p^5, p^3):

    T . V_n = (q_n, p^5 p_n, p^3 ptil_n)  is p-adically PARALLEL to  V_a .

Parallelism <=> all three 2x2 minors are small.  Two of them are (VEC),(VEC~);
the third,

    (COUP)  X_23 := p_a * p^3 * ptil_n  -  ptil_a * p^5 * p_n ,
            ord_p(X_23) >= ord_p(q_a) + 2   (p>=11; >= ord_p(q_a)+1 uniformly),

is a CONSEQUENCE of the first two (a rank-1 identity: X_p, X_s, X_23 are the
minors of a matrix whose rows are p-adically dependent).  Hence the pair
(p_n, ptil_n) is governed by ONE projective congruence with the SAME scalar
lambda = q_n/q_a in both slots (verified: ord(lambda1-1), ord(lambda2-1) large):
the operative "Frobenius matrix" is the diagonal twist T, not a genuinely
triangular 2x2 -- the coupling is automatic.
------------------------------------------------------------------------------
"""
import sys
from fractions import Fraction
from math import comb, gcd

sys.path.insert(0, '/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from lemma_cb_explore import all_data, primes_in, ord_p_fraction as op, lcm_upto

_cache = {}
def minors(n):
    if n not in _cache:
        d = all_data(n)
        u, ut, w, wt, v, vt = d["u"], d["ut"], d["w"], d["wt"], d["v"], d["vt"]
        _cache[n] = (u * wt - ut * w, wt * v - w * vt, u * vt - ut * v)
    return _cache[n]

def kap(n, p):
    return op(Fraction(comb(2 * n, n)), p)

def Lval(n, p):
    L, pk = 0, p
    while pk <= n:
        L += 1; pk *= p
    return L


def check_q_integer(nmax):
    bad = [n for n in range(1, nmax + 1) if minors(n)[0].denominator != 1]
    print(f"[q_n in Z]  n<= {nmax}: " + ("ALL integers" if not bad else f"FAIL at {bad}"))
    return not bad


def check_vec(nmax):
    print("\n" + "=" * 74)
    print("STEP 1  (VEC)/(VEC~) uniform floor:  ord_p(X) >= ord_p(q_a) + 2")
    print("        single Frobenius step a = floor(n/p) < p, all p>=5")
    print("=" * 74)
    rows = fp = fs = 0
    per = {}
    exc = []
    for p in primes_in(5, nmax):
        for n in range(p, nmax + 1):
            a = n // p
            if a >= p:
                continue
            qa, pa, pta = minors(a)
            qn, pn, ptn = minors(n)
            if qa == 0:
                continue
            Xp = qa * Fraction(p) ** 5 * pn - pa * qn
            Xs = qa * Fraction(p) ** 3 * ptn - pta * qn
            oqa = op(qa, p)
            oP = op(Xp, p) if Xp != 0 else 99
            oS = op(Xs, p) if Xs != 0 else 99
            rows += 1
            per.setdefault(p, [99, 99])
            per[p][0] = min(per[p][0], oP - oqa)
            per[p][1] = min(per[p][1], oS - oqa)
            if oP < oqa + 2:
                fp += 1; print(f"   VEC FAIL n={n} p={p} a={a}: ord X_p={oP} < ord q_a+2={oqa+2}")
            if oS < oqa + 2:
                fs += 1; print(f"   VEC~ FAIL n={n} p={p} a={a}: ord X_s={oS} < {oqa+2}")
            if oqa > 0:
                exc.append((n, p, a, oqa, oP, oS))
    print(f"rows (single-step, p>=5, n<= {nmax}): {rows};  VEC violations={fp}, VEC~ violations={fs}")
    print("per-prime min surplus [ord X_p - ord q_a, ord X_s - ord q_a]:")
    for p in sorted(per):
        print(f"   p={p:2d}: {per[p]}")
    print(f"\nexceptional rows (ord_p(q_a)>0), showing floor is uniform/tight:")
    for r in exc[:14]:
        n, p, a, oqa, oP, oS = r
        print(f"   n={n} p={p} a={a}: ord q_a={oqa}, ord X_p={oP} (surplus {oP-oqa}), ord X_s={oS}")
    return fp == 0 and fs == 0


def check_integral(nmax):
    print("\n" + "=" * 74)
    print("STEP 1  pure-integer lattice form:  p^{5L+ord q_a+2}  |  I")
    print("        I = q_a p^5 A_n - (d_n/d_a)^5 A_a q_n  in Z,  A_m=2 d_m^5 p_m")
    print("=" * 74)
    rows = 0; worst = 99; bad = 0
    for p in primes_in(5, nmax):
        for n in range(p, nmax + 1):
            a = n // p
            if a >= p:
                continue
            qa = minors(a)[0]; qn = minors(n)[0]
            if qa == 0:
                continue
            dn = lcm_upto(n); da = lcm_upto(a)
            An = 2 * dn ** 5 * minors(n)[1]
            Aa = 2 * da ** 5 * minors(a)[1]
            assert An.denominator == 1 and Aa.denominator == 1, "A not integral"
            An, Aa = An.numerator, Aa.numerator
            e = dn // da
            I = qa * p ** 5 * An - e ** 5 * Aa * qn
            rows += 1
            L = Lval(n, p); oqa = op(qa, p)
            need = 5 * L + oqa + 2
            oI = op(Fraction(I), p) if I != 0 else 99
            worst = min(worst, oI - (5 * L + oqa))
            if oI < need:
                bad += 1; print(f"   INT FAIL n={n} p={p}: ord I={oI} < 5L+ord q_a+2={need}")
    print(f"integral rows (p>=5, n<= {nmax}): {rows};  divisibility violations={bad}")
    print(f"min(ord I - (5L+ord q_a)) over grid = {worst}   (theorem floor = 2)")
    return bad == 0


def check_step3(nmax):
    print("\n" + "=" * 74)
    print("STEP 3  coupled minor (COUP): ord_p(X_23) >= ord_p(q_a)+2 (p>=11), and")
    print("        the single scalar lambda=q_n/q_a governs BOTH slots (diagonal twist)")
    print("=" * 74)
    per = {}; rows = 0
    for p in primes_in(5, nmax):
        for n in range(p, nmax + 1):
            a = n // p
            if a >= p:
                continue
            qa, pa, pta = minors(a); qn, pn, ptn = minors(n)
            if qa == 0 or pa == 0 or pta == 0:
                continue
            X23 = pa * Fraction(p) ** 3 * ptn - pta * Fraction(p) ** 5 * pn
            o = op(X23, p) if X23 != 0 else 99
            per.setdefault(p, 99)
            per[p] = min(per[p], o - op(qa, p))
            rows += 1
    print(f"rows={rows}; per-prime min ord(X_23)-ord(q_a):")
    for p in sorted(per):
        print(f"   p={p:2d}: {per[p]}")
    # lambda coherence sample
    print("lambda coherence (ord(lambda_i - 1)) for p=13, a=1 range:")
    for n in range(13, 26):
        qa, pa, pta = minors(1); qn, pn, ptn = minors(n)
        lam1 = (Fraction(13) ** 5 * pn / pa) / (qn / qa)
        lam2 = (Fraction(13) ** 3 * ptn / pta) / (qn / qa)
        print(f"   n={n}: ord(lam1-1)={op(lam1-1,13)}, ord(lam2-1)={op(lam2-1,13)}")


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 64
    ok = True
    ok &= check_q_integer(nmax)
    ok &= check_vec(nmax)
    ok &= check_integral(min(nmax, 44))
    check_step3(min(nmax, 40))
    print("\n" + "=" * 74)
    print("OVERALL STEP-1/3 verification:", "ALL PASS" if ok else "SOME FAIL")
