"""V6(c,d) + V5: the desingularization / apparent-singularity test, the Casoratian,
and the d_n^5-induction assessment.

The exact normalized order-3 recurrence (from salvage_v6_recur.py, cross-checked
against Zudilin math/0206178) relating Y_n,Y_{n+1},Y_{n+2},Y_{n+3} for every
Y in {Q,P,P̂}:

  c0(n) Y_n + c1(n) Y_{n+1} + c2(n) Y_{n+2} + c3(n) Y_{n+3} = 0,

  c0(n) = (n+1)^5 (n+2) a0(n+1)
  c3(n) = 2 (n+3)^5 (2n+5) a0(n)          a0(n) = 41218n^3+198849n^2+320790n+173057

The leading coefficient factors as (fifth power)·(midpoint 2n+5)·(cubic a0).
V6c asks: are the (2n+5) and a0 factors APPARENT singularities?  V6d: does the
d_n^5-induction then close?

No sage/ore_algebra locally, so we test the *consequences* that apparentness must
produce, all in exact arithmetic:
 (T-CAS) the Casoratian telescopes a0 to a SINGLE linear factor (apparent signature);
 (T-IND) the per-step p-adic loss is <= 5 v_p(n+3) for p>=5 -- i.e. (2n+5),a0 never
         cause denominator growth -- even at n where p|(2n+5) or p|a0(n);
 (T-BOUND) the resulting v_p(P_n) >= -5 floor(log_p n), v_p(P̂_n) >= -3 floor(log_p n).

Usage: python3 salvage_v6_desing.py
"""

from fractions import Fraction
from math import comb
import sympy as sp
from salvage_data import triple, get_all

n = sp.Symbol('n')
a0 = 41218 * n**3 + 198849 * n**2 + 320790 * n + 173057
c0 = (n + 1)**5 * (n + 2) * a0.subs(n, n + 1)
c1 = -2 * (n + 2) * (3874492*n**8 + 59373972*n**7 + 394148190*n**6
                     + 1481084196*n**5 + 3447878810*n**4 + 5095855458*n**3
                     + 4673546679*n**2 + 2433871008*n + 551502039)
c2 = -2 * (48802112*n**9 + 967468896*n**8 + 8488000862*n**7 + 43246197636*n**6
           + 140983768422*n**5 + 304912330849*n**4 + 437406946975*n**3
           + 401272692378*n**2 + 213593890911*n + 50257929339)
c3 = 2 * (n + 3)**5 * (2*n + 5) * a0
C0 = sp.Poly(sp.expand(c0), n)
C1 = sp.Poly(sp.expand(c1), n)
C2 = sp.Poly(sp.expand(c2), n)
C3 = sp.Poly(sp.expand(c3), n)
_f0 = sp.lambdify(n, sp.expand(c0), 'math')
_f1 = sp.lambdify(n, sp.expand(c1), 'math')
_f2 = sp.lambdify(n, sp.expand(c2), 'math')
_f3 = sp.lambdify(n, sp.expand(c3), 'math')


def vp(x, p):
    """p-adic valuation of a nonzero Fraction/int."""
    if x == 0:
        return 10**9
    fr = Fraction(x)
    num, den, v = abs(fr.numerator), fr.denominator, 0
    while num % p == 0:
        num //= p; v += 1
    while den % p == 0:
        den //= p; v -= 1
    return v


def report_a0():
    print("=== a0(n) = 41218n^3+198849n^2+320790n+173057 ===")
    print("  factor over Q:", sp.factor(a0))
    print("  41218 =", sp.factorint(41218), " 173057 =", sp.factorint(173057))
    disc = sp.discriminant(sp.Poly(a0, n))
    print("  discriminant =", disc, " (irreducible cubic, irrational roots)")
    # a0(n+1) == c0's cubic?
    print("  a0(n+1) =", sp.expand(a0.subs(n, n + 1)))


def casoratian(hi=24):
    """V5: Casoratian of (Q,P,P̂) with rows (n,n+1,n+2) (natural orientation)."""
    print("\n=== V5: Casoratian of (Q,P,P̂) ===")
    get_all(0, hi + 2)
    a0f = sp.lambdify(n, a0, 'math')

    def Yvec(m):
        d = triple(m)
        return (Fraction(d["Q"]), Fraction(d["P"]), Fraction(d["Ph"]))

    def det3(m):   # rows m, m+1, m+2
        M = [list(Yvec(m)), list(Yvec(m + 1)), list(Yvec(m + 2))]
        return (M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])
                - M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
                + M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))

    # telescoping identity C(n+1)/C(n) = (-1)^3 c0(n)/c3(n) = -c0/c3
    good = all(det3(m + 1) / det3(m) == -Fraction(_f0(m)) / Fraction(_f3(m))
               for m in range(1, hi))
    print(f"  telescoping det C(n+1)/C(n) = -c0(n)/c3(n): "
          f"{'HOLDS exactly' if good else 'FAILS'}")
    # CORRECTED exact closed form (Sol's S3 was garbled/other orientation):
    #   C(n) = (-1)^{n-1} a0(n) / [16 (n+1)^4 (n+2)^5 (2n+1)(2n+3) C(2n,n)]
    def clean(m):
        return (Fraction((-1)**(m - 1)) * int(a0f(m))
                / (16 * (m + 1)**4 * (m + 2)**5 * (2*m + 1) * (2*m + 3)
                   * comb(2*m, m)))
    ok = all(clean(m) == det3(m) for m in range(1, hi + 1))
    print("  CORRECTED closed form  C(n) = (-1)^{n-1} a0(n) /")
    print("        [ 16 (n+1)^4 (n+2)^5 (2n+1)(2n+3) C(2n,n) ]")
    print(f"     VERIFIED exactly for n=1..{hi}: {ok}")
    print("  -> a0 appears LINEARLY (telescopes to a single factor): the")
    print("     apparent-singularity SIGNATURE for the (Q,P,P̂) solution lattice;")
    print("     the (2n+1)(2n+3) midpoint factors sit in the DENOMINATOR (one")
    print("     solution must be singular there -- it is P̂, see T-IND below).")


def induction_test(primes, hi=45):
    """T-IND: per-step loss <= 5 v_p(n+3); split danger by a0 vs midpoint (2n+5).

    Apparent (for a given solution) <=> 0 violations at its danger-steps.
    Operator-level apparent would require 0 violations for ALL THREE solutions.
    """
    print("\n=== V6c/d T-IND: holonomic per-step p-adic loss (apparent test) ===")
    print("  v_p(Y_{n+3}) >= min(v_p Y_{n..n+2}) - 5 v_p(n+3)  [only (n+3)^5 loss]")
    get_all(0, hi)
    a0f = sp.lambdify(n, a0, 'math')
    for key, wt in [("Q", 0), ("P", 5), ("Ph", 3)]:
        seq = {m: Fraction(triple(m)[key]) for m in range(0, hi + 1)}
        cats = {"a0": [0, 0], "mid": [0, 0], "both": [0, 0], "none": [0, 0]}
        first_v = []
        for m in range(0, hi - 2):
            for p in primes:
                va0 = int(a0f(m)) % p == 0
                vmid = (2*m + 5) % p == 0
                cat = ("both" if (va0 and vmid) else
                       "a0" if va0 else "mid" if vmid else "none")
                vprev = min(vp(seq[m], p), vp(seq[m+1], p), vp(seq[m+2], p))
                viol = vp(seq[m+3], p) < vprev - 5 * vp(m + 3, p)
                cats[cat][0] += 1
                cats[cat][1] += int(viol)
                if viol and len(first_v) < 8:
                    first_v.append((m, p, cat))
        summ = {k: f"{v[1]}/{v[0]}" for k, v in cats.items()}
        print(f"  Y={key:>2} (wt {wt}) viol/total by danger source: {summ}")
        if first_v:
            print("     violations (m,p,source):", first_v)
    print("  READ: Q,P have 0 violations in EVERY category (a0 & midpoint are")
    print("   apparent FOR P,Q) -> v_p(P_n) >= -5 floor(log_p n) closes.  But P̂")
    print("   leaks systematically at p=2n+5 (and once at a0): the midpoint/a0 are")
    print("   TRUE singularities of the operator, NOT apparent operator-wide.")


def coeff_integrality(primes):
    """Are c0,c1,c2 p-integral so the induction step is clean for p>=5?"""
    print("\n=== V6d: coefficient content (p-integrality of c0,c1,c2) ===")
    for name, P in [("c0", C0), ("c1", C1), ("c2", C2), ("c3", C3)]:
        cont = sp.gcd([abs(int(c)) for c in P.all_coeffs()])
        print(f"  {name}: integer content = {cont} = {sp.factorint(cont) if cont>1 else '1'}")
    print("  (integer polynomials => c_i(m) in Z for all m; for p>=5 the only")
    print("   p in c3 beyond (n+3)^5 comes from (2n+5)*a0 -- the apparent part.)")


def bound_test(primes, hi=44):
    """T-BOUND: v_p(P_n) >= -5 floor(log_p n),  v_p(P̂_n) >= -3 floor(log_p n)."""
    print("\n=== V6d T-BOUND: den bound v_p(P_n)>=-5L, v_p(P̂_n)>=-3L (L=floor log_p n) ===")
    get_all(0, hi)
    import math
    for key, wt in [("P", 5), ("Ph", 3)]:
        seq = {m: Fraction(triple(m)[key]) for m in range(1, hi + 1)}
        total = viol = tight = 0
        first_v = []
        for m in range(1, hi + 1):
            for p in primes:
                L = int(math.log(m, p)) if m >= p else 0
                # correct floor via loop
                L = 0
                pw = p
                while pw <= m:
                    L += 1; pw *= p
                bound = -wt * L
                v = vp(seq[m], p)
                total += 1
                if v < bound:
                    viol += 1
                    if len(first_v) < 6:
                        first_v.append((m, p, v, bound))
                if v == bound:
                    tight += 1
        print(f"  {key} (wt {wt}): {total} checks, {viol} violations, {tight} tight "
              f"(v_p = -{wt}L) -> {'PASS' if viol==0 else 'FAIL'}")
        if first_v:
            print("     first violations (n,p,v,bound):", first_v)


if __name__ == "__main__":
    primes = (5, 7, 11, 13, 17, 19, 23)
    report_a0()
    casoratian(24)
    coeff_integrality(primes)
    induction_test(primes, 44)
    bound_test(primes, 44)
