"""h1_beta_r.py -- Zagier's beta_r dictionary (arXiv:1601.00950, App. A) made
concrete, with an EXACT closed formula for the rational part and an explicit
lcm-denominator bound.  This is the one-variable instantiation of the H1
reformulation (H1_COLLAPSE.md Section 2): it shows precisely how "the rational
(weight-0) part of a period" is a beta_r residue whose denominator is
lcm-controlled by the already-proven Lemmas 5.1 (partial-fraction integrality)
and 5.2 (harmonic clearing).

Zagier (44):  for R in V_0 (poles in {-1,-2,...}, R(inf)=0) with beta_1(R)=0,
    sum_{k>=0} R(k) = R_0(0) + sum_{r>=2} beta_r(R) zeta(r),
with beta_r(R) = sum_j c_{j,r}   (c_{j,i} = coeff of 1/(k+j)^i in R),
because 1/(k+j)^r ≡ 1/(k+1)^r (mod Delta V).

DERIVED HERE (and verified below):  the RATIONAL part is the finite rational
    R_0(0) = - sum_{j>=1} sum_{i>=1} c_{j,i} * H^{(i)}_{j-1},
    H^{(i)}_m = sum_{l=1}^m l^{-i}  (H^{(i)}_0 = 0).
Proof:  R_0(0) = sum_{k>=0}(R(k) - sum_r beta_r/(k+1)^r); using
    sum_{k>=0} 1/(k+j)^i = zeta(i) - H^{(i)}_{j-1} and beta_i = sum_j c_{j,i},
    the zeta(i) cancel, leaving -sum_{j,i} c_{j,i} H^{(i)}_{j-1}.  (QED)

DENOMINATOR BOUND [PROVEN, from repo Lemmas 5.1+5.2]:
  If R = P(k)/prod_j (k+j)^{s_j} with the poles j in a window of width w
  (max difference of pole locations = w) and total order s = sum s_j, then
  every c_{j,i} is cleared by d_w^{s-i} (Lemma 5.1: the clearing index is the
  pole *difference* bound w, NOT the absolute index), and H^{(i)}_{j-1} by
  d_{j-1}^i (Lemma 5.2).  Hence d_W^{s} R_0(0) in Z, where W = max(w, max_j (j-1)).
"""
import sympy as sp
from math import gcd
from fractions import Fraction

k = sp.symbols('k')

def dlcm(N):
    r = 1
    for m in range(2, N + 1):
        r = r * m // gcd(r, m)
    return r

def partial_fraction_coeffs(R):
    """Return dict {(j,i): c_{j,i}} for R(k) = sum c_{j,i}/(k+j)^i, poles at k=-j."""
    R = sp.together(sp.sympify(R))
    num, den = sp.fraction(R)
    apart = sp.apart(R, k, full=True).doit()
    coeffs = {}
    for term in sp.Add.make_args(apart):
        # each term: c / (k+j)**i   (or a polynomial part -> ignore/none in V_0)
        t = sp.together(term)
        n_t, d_t = sp.fraction(t)
        if d_t.has(k):
            poly = sp.Poly(d_t, k)
            i = poly.degree()
            # d_t = leadcoeff*(k+j)^i ; find j from the root
            roots = sp.roots(sp.Poly(d_t, k))
            j = -list(roots.keys())[0]
            lead = poly.LC()
            c = sp.simplify(n_t / lead)
            key = (int(j), int(i))
            coeffs[key] = coeffs.get(key, 0) + c
    return coeffs

def beta(coeffs):
    """beta_r(R) = sum_j c_{j,r}."""
    out = {}
    for (j, i), c in coeffs.items():
        out[i] = out.get(i, 0) + c
    return {r: sp.nsimplify(v) for r, v in out.items()}

def H(i, m):
    return sum(sp.Rational(1, l**i) for l in range(1, m + 1))

def rational_part(coeffs):
    """R_0(0) = - sum_{j,i} c_{j,i} H^{(i)}_{j-1}."""
    return sp.nsimplify(-sum(c * H(i, j - 1) for (j, i), c in coeffs.items()))

def check_sum(R, terms=200000):
    """Numeric sum_{k>=0} R(k) for cross-checking."""
    Rf = sp.lambdify(k, R, 'mpmath')
    import mpmath as mp
    mp.mp.dps = 30
    return mp.nsum(lambda kk: Rf(kk), [0, mp.inf])

# -------------------------------------------------------------------- tests
def selftest():
    import mpmath as mp
    mp.mp.dps = 25
    zeta = mp.zeta
    cases = [
        ("1/((k+1)*(k+2))",            None),   # telescopes to 1
        ("1/((k+1)*(k+2)**2)",         None),
        ("1/(k+1)**2",                 None),   # zeta(2)
        ("1/((k+1)**2*(k+2)**2)",      None),
        ("(2*k+3)/((k+1)**2*(k+2)**2)",None),
    ]
    print("== Zagier (44) rational-part formula, exact vs numeric ==")
    for expr, _ in cases:
        R = sp.sympify(expr)
        coe = partial_fraction_coeffs(R)
        bet = beta(coe)
        b1 = bet.get(1, 0)
        r0 = rational_part(coe)
        # reconstruct sum = r0 + sum_{r>=2} beta_r zeta(r)
        recon = complex(r0)
        for r, br in bet.items():
            if r >= 2:
                recon += float(br) * float(zeta(r))
        num = complex(check_sum(R))
        ok = abs(recon - num) < 1e-15
        print(f"  R={expr}")
        print(f"    beta = {bet},  beta_1={b1} (must be 0),  R_0(0)={r0}")
        print(f"    reconstructed sum={recon.real:.12f}  numeric={num.real:.12f}  [{'OK' if ok and abs(complex(b1))<1e-20 else 'CHECK'}]")

    print("\n== denominator bound d_W^s * R_0(0) in Z (Lemma 5.1+5.2) ==")
    # window-width example: poles at j in {3,4,5} (width w=2), order 2 each
    R = sp.sympify("1/((k+3)**2*(k+4)**2*(k+5)**2)")
    coe = partial_fraction_coeffs(R)
    r0 = rational_part(coe)
    s = 6  # total order
    w = 2  # pole-difference window 5-3
    W = max(w, 5 - 1)  # also H^{(i)}_{j-1} up to j-1=4
    dW = dlcm(W)
    val = sp.Rational(r0)
    ok = (sp.denom(val * dW**s) == 1)
    print(f"  R=1/((k+3)^2(k+4)^2(k+5)^2): R_0(0)={r0}")
    print(f"    s={s}, window w={w}, W={W}, d_W={dW};  d_W^s*R_0(0) in Z: {ok}")
    # tighter: the difference-window bound w vs absolute-index bound
    print(f"    (note: absolute max index is 5 -> d_5={dlcm(5)}, but the")
    print(f"     difference window is only w={w} -> d_2={dlcm(2)}; the harmonic")
    print(f"     H^(i)_{{j-1}} up to j-1=4 forces d_4={dlcm(4)} here.)")

if __name__ == "__main__":
    selftest()
