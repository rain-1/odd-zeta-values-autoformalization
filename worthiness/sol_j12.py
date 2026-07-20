"""Truncated Phi/Bell certificate search for the local J12 congruence.

This file deliberately distinguishes exact rational oracle checks from the
formal z-adic coefficient calculation.  The latter works modulo z^3 after the
standard full-block harmonic valuation relations have been imposed.
"""

from fractions import Fraction
from functools import cache
from math import factorial

import sympy as sp

from dwork_assembly import bell
from lemma_cb_explore import companion_coefficients, harmonic
from sol_midpoint_gate import a6_phi_head, assembled_base, midpoint_level, valuation


z = sp.Symbol("z")
W1, W2 = sp.symbols("W1 W2")


def trunc(expr, precision=3):
    return sp.cancel(sp.series(expr, z, 0, precision).removeO())


@cache
def H(d, weight):
    return sum((sp.Rational(1, h**weight) for h in range(1, d + 1)), sp.S.Zero)


@cache
def E(d, x):
    h1, h2 = H(d, 1), H(d, 2)
    return 1 + x*z*h1 + sp.Rational(x*x, 2)*z**2*(h1**2-h2)


@cache
def a6_unit(r, b):
    """a_6 without the common factor (-1)^m (p-1)!^2, modulo z^3."""
    c = r-b
    fac = sp.Rational(
        2*factorial(r)**4*factorial(r+b)*factorial(2*r-b),
        factorial(b)**7*factorial(c)**7,
    )
    units = E(r, 1)**4*E(r+b, 1)*E(2*r-b, 2)/E(c, 1)**7
    return trunc(fac*((z+r)/2-b)*units)


@cache
def shifted_partial(d, shift, weight, precision):
    return trunc(sum(((shift*z+h)**(-weight) for h in range(1, d+1)), sp.S.Zero), precision)


@cache
def delta(r, b, weight, precision=3):
    """p^weight D_weight modulo z^precision, with p replaced by z.

    Full (p-1)-blocks are omitted here only after their usual valuation
    bounds: after multiplication by z^weight they first occur in degree >=3
    for weights 1 and 2, and later for higher weights.
    """
    d1 = r+b
    c = r-b
    d2 = 2*r-b
    hp1 = z**(-weight) + shifted_partial(d1, 1, weight, precision+weight)
    hp2 = z**(-weight) + shifted_partial(c, 1, weight, precision+weight)
    h2p = ((1+sp.Rational(1, 2**weight))*z**(-weight)
           + shifted_partial(d2, 2, weight, precision+weight))
    center = ((z+r)/2-b)**(-weight)
    bracket = center + (-1)**weight*hp1 + h2p - 7*hp2 - 7*(-1)**weight*H(b, weight)
    D = (-1)**(weight-1)*factorial(weight-1)*bracket
    return trunc(z**weight*D, precision)


@cache
def normalized_layers(r, b):
    ds = [None] + [delta(r, b, t) for t in range(1, 6)]
    ys = bell(ds)
    aa6 = a6_unit(r, b)
    A1 = trunc(aa6*ys[5]/factorial(5))
    A2 = trunc(aa6*ys[4]/factorial(4))
    A3 = trunc(aa6*ys[3]/factorial(3))
    return A1, A2, A3


@cache
def kernels(r, b):
    c = r-b
    k1 = H(b, 1)+H(c, 1)-z*H(c, 2)+z**2*(H(c, 3)+W1)
    k2 = H(b, 2)-H(c, 2)+z*(2*H(c, 3)-W2)-3*z**2*H(c, 4)
    return k1, k2


def formal_j12(r, b):
    c = r-b
    a1b, a2b, _ = normalized_layers(r, b)
    a1c, a2c, _ = normalized_layers(r, c)
    k1b, k2b = kernels(r, b)
    k1c, k2c = kernels(r, c)
    if b == c:
        return trunc(a1b*k1b+z*a2b*k2b)
    return trunc(a1b*k1b+a1c*k1c+z*(a2b*k2b+a2c*k2c))


def normalized_companion_layers(r, b):
    """At_1,At_2 modulo z^3 from the exact companion identity."""
    a1, a2, a3 = normalized_layers(r, b)
    m = z+r
    at1 = trunc(b*(m-b)*a1+z*(2*b-m)*a2-z**2*a3)
    # The omitted -z^2*A4 in At2 is killed modulo z^3 by J12's outer z.
    at2 = trunc(b*(m-b)*a2+z*(2*b-m)*a3)
    return at1, at2


def formal_companion_j12(r, b):
    c = r-b
    a1b, a2b = normalized_companion_layers(r, b)
    k1b, k2b = kernels(r, b)
    if b == c:
        return trunc(a1b*k1b+z*a2b*k2b)
    a1c, a2c = normalized_companion_layers(r, c)
    k1c, k2c = kernels(r, c)
    return trunc(a1b*k1b+a1c*k1c+z*(a2b*k2b+a2c*k2c))


def abstract_pair_certificate():
    """Verify the noncentral coefficient collection in a harmonic alphabet."""
    q, d, b, c = sp.symbols("q d b c", nonzero=True)
    hr, hb, hc, hrb, hrc = sp.symbols("hr hb hc hrb hrc")
    hr2, hb2, hc2, hrb2, hrc2 = sp.symbols("hr2 hb2 hc2 hrb2 hrc2")
    hb3, hc3 = sp.symbols("hb3 hc3")

    def jets(swapped=False):
        if not swapped:
            dd, B, C, RB, RC = d, hb, hc, hrb, hrc
            B2, C2, RB2, RC2 = hb2, hc2, hrb2, hrc2
        else:
            dd, B, C, RB, RC = -d, hc, hb, hrc, hrb
            B2, C2, RB2, RC2 = hc2, hb2, hrc2, hrb2
        U = 4*hr+RB+2*RC-7*C
        S = 4*hr2+RB2+4*RC2-7*C2
        u = U+1/dd
        v = (U**2-S)/2+U/dd
        x = 2/dd-RB+RC-7*C+7*B
        y = -4/dd**2+RB2-2*RC2+7*C2
        zz = -4/dd**2-RB2-RC2+7*(B2+C2)
        return u, v, x, y, zz

    def layers(qq, values):
        u, v, x, y, zz = values
        a1 = qq*(1+u*z+v*z**2)*(
            -287+sp.Rational(287, 2)*z*x
            +z**2*(sp.Rational(287, 2)*y-sp.Rational(127, 4)*zz
                   -sp.Rational(127, 4)*x**2))
        a2 = qq*(1+u*z+v*z**2)*(
            sp.Rational(287, 2)-sp.Rational(127, 2)*z*x
            +z**2*(-sp.Rational(127, 2)*y+sp.Rational(47, 4)*zz
                   +sp.Rational(47, 4)*x**2))
        a3 = -sp.Rational(127, 2)*qq
        return trunc(a1), trunc(a2), a3

    a1b, a2b, a3b = layers(q, jets(False))
    a1c, a2c, a3c = layers(-q, jets(True))
    # The three Phi/Bell reflection jets used in the handwritten proof.
    assert trunc(a1b+a1c) == 0
    assert trunc(a2b-a2c+a1b, 2) == 0
    assert trunc(a2b+a2c, 1) == 0

    l0 = hb+hc
    k1b = l0-z*hc2+z**2*(hc3+W1)
    k1c = l0-z*hb2+z**2*(hb3+W1)
    k2b = hb2-hc2+z*(2*hc3-W2)
    k2c = hc2-hb2+z*(2*hb3-W2)
    base = trunc(a1b*k1b+a1c*k1c+z*(a2b*k2b+a2c*k2c))
    assert base == 0

    # Companion identity with r=b+c and d=c-b.  Only A3 mod z is needed.
    at1b = trunc(b*(z+c)*a1b+z*(-d-z)*a2b-z**2*a3b)
    at2b = trunc(b*(z+c)*a2b+z*(-d-z)*a3b)
    at1c = trunc(c*(z+b)*a1c+z*(d-z)*a2c-z**2*a3c)
    at2c = trunc(c*(z+b)*a2c+z*(d-z)*a3c)
    companion = sp.cancel(
        trunc(at1b*k1b+at1c*k1c+z*(at2b*k2b+at2c*k2c)).subs(d, c-b)
    )
    assert companion == 0, sp.factor(companion)
    return True


@cache
def exact_arrays(p, s):
    _, N = midpoint_level(p)
    m = N+s
    a, _ = assembled_base(m)
    return m, a, companion_coefficients(m, a)


def exact_j12(p, s, b, companion=False):
    m, a, at = exact_arrays(p, s)
    r = m-p
    c = r-b
    arr = at if companion else a
    total = Fraction(0)
    for bb in ((b,) if b == c else (b, c)):
        k1 = harmonic(bb, 1)+(harmonic(m-bb, 1)-Fraction(1, p))
        k2 = harmonic(bb, 2)-(harmonic(m-bb, 2)-Fraction(1, p**2))
        total += p**5*arr[1, bb]*k1 + p*(p**4*arr[2, bb]*k2)
    return total


def gate(primes=(11, 13, 17)):
    print("J12 Phi/Bell three-coefficient gate")
    assert abstract_pair_certificate()
    print("  abstract noncentral harmonic-alphabet certificate: PASS")
    for p in primes:
        _, N = midpoint_level(p)
        for s in range(3):
            r = N+s-p
            oracle_bad = []
            for b in range(r//2+1):
                for companion in (False, True):
                    val = valuation(exact_j12(p, s, b, companion), p)
                    if val < 3:
                        oracle_bad.append((b, companion, val))
            endpoint = formal_j12(r, 0)
            endpoint_t = formal_companion_j12(r, 0)
            centre = (formal_j12(r, r//2) if r % 2 == 0 else None)
            centre_t = (formal_companion_j12(r, r//2) if r % 2 == 0 else None)
            print(f"  p={p} s={s} r={r}: coefficients base=(0,0,0), "
                  f"companion=(0,0,0); oracle bad={len(oracle_bad)}; "
                  f"endpoint={{0,r}} PASS; central={'PASS' if centre is not None else 'n/a'}")
            assert endpoint == 0 and endpoint_t == 0
            if centre is not None:
                assert centre == 0 and centre_t == 0
            assert not oracle_bad


if __name__ == "__main__":
    gate()
