"""h1_residue_sum.py -- ATTEMPT (INCOMPLETE) at the explicit weight-0 residue
sum for the symmetric P_n.  HONEST STATUS: does NOT yet reproduce P_n.

Goal (closing E2 of PROOF_SYMMETRIC_v2): write -2 P_n as an explicit finite
double-residue sum of the weight-0 (zeta-free) part of

    Phi(s,t) = (-1)^n pi^3 r(s) r(t) C(s,t) / (sin pi s sin pi t sin pi(s+t)),
    I_n = n! (2 pi i)^{-2} ∬ Phi,   weight-0 part of I_n = -2 P_n.

The weight-0 kernel keeps only 1/(pi z) from each pi/sin(pi z), giving the germ
at a pole pair (s,t)=(-a',-b'), (eps,delta)=(s+a',t+b'):

    germ = (-1)^n r(-a'+eps) r(-b'+delta) C(-a'+eps,-b'+delta) / (eps*delta*(eps+delta)).

WHAT THIS SCRIPT SHOWS (the precise obstruction, not a solution):
Summing the iterated residue Res_eps Res_delta of `germ` over ONLY the
double-pole pairs a',b' in {n+1,...,2n+1} gives, at n=1,

    n! * sum = -106,     but the target weight-0 part -2 P_1 = -87/2 = -43.5.

So the double-pole-pair configuration is INCOMPLETE.  Missing, and required for
the true sum (this is exactly BZ's "skip the details" contour bookkeeping):
  (i)  the coupling pole delta = -eps (the zero of sin pi(s+t)), which the naive
       Res_delta at delta=0 omits;
  (ii) mixed configurations pairing a double pole of r in one variable with the
       simple poles at s in {0,1,2,...} or s in {-(2n+2),...} in the other;
  (iii) correct orientation / which poles the vertical contours
       Re s=-c1, Re t=-c2 (0<c_i<n+1, c1+c2>n+1) actually enclose.
Until (i)-(iii) are pinned down and the sum matches recover_p exactly, section
4a of H1_COLLAPSE.md must remain OPEN.  Do NOT treat the number below as P_n.
"""
import sympy as sp

def double_pole_pair_sum(n):
    e, d = sp.symbols('e d')
    def rlaurent(shift, var):
        x = -shift + var
        num = sp.prod([x + i for i in range(1, n + 1)])
        den = sp.prod([(x + j) ** 2 for j in range(n + 1, 2 * n + 2)])
        return sp.series(num / den, var, 0, 5).removeO()
    def Cfun(sv, tv):
        return sp.prod([sv + tv + l for l in range(n + 2, 2 * n + 2)])
    poles = range(n + 1, 2 * n + 2)
    tot = 0
    for ap in poles:
        for bp in poles:
            germ = ((-1) ** n * rlaurent(ap, e) * rlaurent(bp, d)
                    * Cfun(-ap + e, -bp + d) / (e * d * (e + d)))
            r1 = sp.residue(sp.together(germ), d, 0)
            tot += sp.residue(sp.together(r1), e, 0)
    return sp.nsimplify(sp.simplify(tot))

TARGET = {1: sp.Rational(87, 4), 2: sp.Rational(1190161, 384)}
if __name__ == "__main__":
    for n in (1, 2):
        tot = double_pole_pair_sum(n)
        got = -sp.factorial(n) * tot / 2          # if -2P = n! tot then P = -n! tot/2
        tgt = TARGET[n]
        print(f"n={n}: n!*sum(double-pole pairs) = {sp.factorial(n)*tot} ; "
              f"P candidate = {got} ; target P_{n} = {tgt} ; "
              f"{'MATCH' if got == tgt else 'NO MATCH (incomplete sum)'}")
    print("\nVERDICT: residue sum INCOMPLETE -- coupling-pole and mixed/simple-pole "
          "contributions missing. Section 4a stays OPEN.")
