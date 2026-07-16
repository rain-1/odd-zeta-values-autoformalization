#!/usr/bin/env python3
"""
Exact denominator check for Zudilin's asymmetric ZETA(5..11) series Z_n,
as formulated verbatim in Krattenthaler-Rivoal, "Hypergeometrie et fonction
zeta de Riemann" (arXiv:math/0311114), section 17.1:

  Z_n = prod_{u=1}^{10} ((13+2u)n)! / (27n)!^6
        * sum_{k=1}^inf  (1/2) d^2/dk^2 [ (k + 37n/2)
              * (k-27n)_{27n}^3 (k+37n+1)_{27n}^3
              / prod_{u=1}^{10} (k+(12-u)n)_{(13+2u)n+1} ]

with  Z_n = z_{0,n} + sum_{j=1}^4 z_{j,n} zeta(2j+3)   (form in 1,z5,z7,z9,z11).

  Proven (KR):        2 d_{35n}^3 d_{34n} d_{33n}^8 z_{j,n} in Z.
  Conjectured (17.1): 2 d_{35n}^3 d_{34n} d_{33n}^7 z_{j,n} in Z.

QUESTION addressed here: is the leading factor 2 actually needed?

GENERAL ENGINE.  For a summand  S0(k) = pref * (k+h) * prod(num linear factors)
/ prod(den linear factors),  and operator (1/C!) d^C/dk^C, the only poles are at
k=-j (integer) where den vanishes; the numerator never vanishes there.  With
principal part  S0 = sum_m a_{j,m}(k+j)^{-m},
   (1/C!)d^C S0 has principal part  sum_m a_{j,m}*(-1)^C*binom(m+C-1,C)*(k+j)^{-(m+C)},
and  sum_{k>=1}(k+j)^{-s} = zeta(s) - H_j^{(s)}  (s>=2).  The a_{j,m} are Taylor
coeffs of ((k+j)^{r_j} S0) at k=-j, got as a truncated power series in exact
rationals (Fraction).  No floats, no symbolic diff, no polynomial factoring.

SELF-TEST: the same engine is run on the KR very-well-poised zeta(4) series
S_{n,4,2,1,1}(1) (C=1, half-shift n/2), whose values u_1=36,v_1=39,
v_2=-41769/16 were obtained independently with sympy; they must match.
"""
from fractions import Fraction as F
from math import factorial, lcm, comb
from collections import Counter


def ser_mul(A, B, L):
    C = [F(0)] * L
    for i, a in enumerate(A):
        if a == 0 or i >= L:
            continue
        for j, b in enumerate(B):
            if i + j >= L:
                break
            if b:
                C[i + j] += a * b
    return C


def lin_series(a, L):
    out = [F(0)] * L
    out[0] = a
    if L > 1:
        out[1] = F(1)
    return out


def inv_linear(a, L):
    return [(F(1) if i % 2 == 0 else F(-1)) / (a ** (i + 1)) for i in range(L)]


def dn(N):
    return lcm(*range(1, N + 1)) if N >= 1 else 1


def linear_form_coeffs(pref, halfshift, num_bases, den_bases, C):
    """Return (As, const) where As[s]=coeff of zeta(s), const=rational (=+constant part
    of the sum, i.e. sum_{k} (1/C!)d^C S0 = sum_s As[s] zeta(s) + const).

    pref: Fraction prefactor.
    halfshift h: the linear factor (k+h) (Fraction; h may be half-integer).
    num_bases: list of constants b, each a numerator linear factor (k+b).
    den_bases: list of integer constants b, each a denominator linear factor (k+b).
    C: order of the derivative operator (1/C!) d^C/dk^C.
    """
    cnt = Counter(den_bases)
    poles = sorted(cnt.keys())
    As = {}
    const = F(0)
    for j in poles:
        r = cnt[j]
        L = r
        # g(t) = pref*(k+h)*prod(num)/prod(den_red)  at k=-j+t, to order t^{r-1}
        g = [F(1)] + [F(0)] * (L - 1)
        g = ser_mul(g, lin_series(F(halfshift) - j, L), L)   # the (k+h) factor
        for b in num_bases:
            g = ser_mul(g, lin_series(F(b) - j, L), L)
        for b, m in cnt.items():
            a = b - j
            times = m - (r if b == j else 0)
            if times <= 0:
                continue
            inv = inv_linear(F(a), L)
            for _ in range(times):
                g = ser_mul(g, inv, L)
        g = [pref * x for x in g]
        # a_{j,m} = g[r-m]; contribute to zeta(s), s=m+C
        for m in range(1, r + 1):
            a_jm = g[r - m]
            if a_jm == 0:
                continue
            s = m + C
            coeff = a_jm * ((-1) ** C) * comb(m + C - 1, C)
            As[s] = As.get(s, F(0)) + coeff
            Hjs = sum(F(1, i ** s) for i in range(1, j + 1))
            const += -coeff * Hjs
    return As, const


# ---------------- self-test on the well-poised zeta(4) series ----------------
def zeta4_series(n):
    """S_{n,4,2,1,1}(1) = u_n zeta(4) - v_n.  A=4,B=2,C=1,r=1, half-shift n/2,
    summand (k+n/2)(k-n)_n^2 (k+n+1)_n^2 / (k)_{n+1}^4, prefactor n!^{A-2Br}=1."""
    pref = F(1)
    num = []
    for i in range(n):
        num += [F(-n + i), F(-n + i)]         # (k-n)_n squared
    for i in range(n):
        num += [F(n + 1 + i), F(n + 1 + i)]   # (k+n+1)_n squared
    den = []
    for _ in range(4):
        for i in range(n + 1):
            den.append(i)                     # (k)_{n+1} to 4th power: bases 0..n
    As, const = linear_form_coeffs(pref, F(n, 2), num, den, C=1)
    u = As.get(4, F(0))          # coeff of zeta(4)
    v = -const                   # S = u zeta4 - v  =>  const = -v
    # ensure no other zetas
    other = {s: As[s] for s in As if s != 4 and As[s] != 0}
    return u, v, other


def run_selftest():
    print("SELF-TEST on KR zeta(4) series S_{n,4,2,1,1}(1) = u_n zeta(4) - v_n")
    expected = {1: (36, F(39)), 2: (-2412, F(-41769, 16)),
                3: (266040, F(62195315, 216)), 4: (-37159020, F(-92662434865, 2304))}
    ok = True
    for n in (1, 2, 3, 4):
        u, v, other = zeta4_series(n)
        eu, ev = expected[n]
        good = (u == eu and v == ev and not other)
        ok = ok and good
        print(f"  n={n}: u={u} v={v}  other_zetas={other}  match={good}")
    print("  SELF-TEST", "PASSED" if ok else "FAILED")
    return ok


# ---------------- Zudilin asymmetric zeta(5..11) series ----------------
def compute_Zn(n, verbose=True):
    pref = F(1)
    for u in range(1, 11):
        pref *= factorial((13 + 2 * u) * n)
    pref /= factorial(27 * n) ** 6
    num = []
    for i in range(27 * n):
        b = -27 * n + i
        num += [F(b), F(b), F(b)]              # (k-27n)_{27n}^3
    for i in range(27 * n):
        b = 37 * n + 1 + i
        num += [F(b), F(b), F(b)]              # (k+37n+1)_{27n}^3
    den = []
    for u in range(1, 11):
        for i in range((13 + 2 * u) * n + 1):
            den.append((12 - u) * n + i)        # prod (k+(12-u)n)_{(13+2u)n+1}
    As, const = linear_form_coeffs(pref, F(37 * n, 2), num, den, C=2)
    z0 = const
    return As, z0


def factor_int(x):
    x = abs(int(x))
    f = {}
    d = 2
    while d * d <= x:
        while x % d == 0:
            f[d] = f.get(d, 0) + 1
            x //= d
        d += 1 if d == 2 else 2
    if x > 1:
        f[x] = f.get(x, 0) + 1
    return f


def report(n):
    print("=" * 70)
    print(f"n = {n}")
    As, z0 = compute_Zn(n)
    print("zeta(s) coefficients present in Z_n:")
    for s in sorted(As):
        flag = ''
        if As[s] != 0 and (s % 2 == 0 or s < 5 or s > 11):
            flag = '  <-- UNEXPECTED (should vanish)'
        print(f"   s={s:2d}: {'nonzero' if As[s] != 0 else 'ZERO'}{flag}")
    zc = {0: z0, 1: As.get(5, F(0)), 2: As.get(7, F(0)),
          3: As.get(9, F(0)), 4: As.get(11, F(0))}
    D35, D34, D33 = dn(35 * n), dn(34 * n), dn(33 * n)
    proven      = 2 * D35 ** 3 * D34 * D33 ** 8      # KR proven
    proven_no2  =     D35 ** 3 * D34 * D33 ** 8      # factor 2 removed, proven d-powers
    conj_w2     = 2 * D35 ** 3 * D34 * D33 ** 7      # conjecture (17.1) with 2
    conj_no2    =     D35 ** 3 * D34 * D33 ** 7      # conjecture (17.1) without 2
    v2 = lambda x: (x & -x).bit_length() - 1
    print(f"\nd_35n,d_34n,d_33n bit-sizes: {D35.bit_length()},{D34.bit_length()},{D33.bit_length()}")
    print(f"v2(d_35n)={v2(D35)} v2(d_34n)={v2(D34)} v2(d_33n)={v2(D33)}; "
          f"v2(proven_no2 multiplier)={v2(proven_no2)}")
    for lbl, jj in [('z0', 0), ('z_zeta5', 1), ('z_zeta7', 2), ('z_zeta9', 3), ('z_zeta11', 4)]:
        z = zc[jj]
        den = z.denominator
        fac = factor_int(den)
        print(f"\n {lbl}: den(z) factored = {fac}   (v2={fac.get(2,0)})")
        print(f"    proven  2 d35^3 d34 d33^8 * z in Z ? {(z*proven).denominator==1}")
        print(f"    NO-2    d35^3 d34 d33^8 * z in Z ?   {(z*proven_no2).denominator==1}"
              f"   <== factor 2 needed here? -> {'NO' if (z*proven_no2).denominator==1 else 'YES'}")
        print(f"    conj17.1 2 d35^3 d34 d33^7 * z ?     {(z*conj_w2).denominator==1}")
        print(f"    conj NO-2  d35^3 d34 d33^7 * z ?     {(z*conj_no2).denominator==1}")


if __name__ == '__main__':
    import sys
    if not run_selftest():
        raise SystemExit("engine self-test failed; aborting")
    ns = [int(x) for x in sys.argv[1:]] or [1, 2]
    for n in ns:
        report(n)
