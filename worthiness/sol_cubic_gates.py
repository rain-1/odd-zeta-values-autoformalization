"""Exact diagnostics for Sol session 8: the a=1 cubic gates.

This checker deliberately separates theorem-level polynomial identities from
finite exact evidence.  It records the structural obstruction which prevents
the Session-7 Casoratian proof from being copied at a root of ``a0``.

No floating point arithmetic is used.  The a=1 values are loaded from the
committed exact recurrence ladder; the ladder is never regenerated here.
"""

from fractions import Fraction

import sympy as sp

from falsify_data import a0, c0, c1, c2, get_ladders
from salvage_v6_desing import vp
from sol_local_regular import CUB_D, CUB_ROW
from sol_q3 import closed_casoratian


RHO = Fraction(29, 28)
SMALL_ROOTS = {
    7: (2, 6),
    11: (5, 6, 9),
    13: (7,),
    17: (8,),
    23: (17,),
    29: (27,),
    41: (10,),
    43: (19,),
}


def valuation(x, p):
    return 10**9 if x == 0 else vp(x, p)


def mod_unit(x, p):
    assert x.denominator % p
    return x.numerator % p * pow(x.denominator % p, -1, p) % p


def row_at(m):
    n = sp.symbols("n")
    return tuple(int(sp.expand(A).subs(n, m)) for A in CUB_ROW)


def row_value(row, values):
    return sum((Fraction(row[i]) * values[i] for i in range(3)), Fraction(0))


def polynomial_certificate():
    """The CUB remainder identity is theorem-level exact algebra."""
    n = sp.symbols("n")
    aa = sp.Poly(41218*n**3 + 198849*n**2 + 320790*n + 173057, n)
    for ci, Ai in zip((c0, c1, c2), CUB_ROW):
        # Convert the integer-valued recurrence function back to a polynomial.
        cp = sp.Poly(sp.expand(ci(n)), n)
        assert sp.rem(CUB_D * cp, aa).as_expr() == sp.expand(Ai)
    assert sp.factorint(CUB_D) == {2: 5, 37: 5, 557: 2}
    print("CUB polynomial remainder D*c_i = A_i (mod a0): PASS")


def small_root_oracle():
    got = {}
    for p in list(sp.primerange(5, 50)):
        roots = tuple(r for r in range(p) if a0(r) % p == 0)
        if roots:
            got[p] = roots
    assert got == SMALL_ROOTS
    print("cubic roots for primes p<50:")
    for p, roots in got.items():
        print(f"  p={p:2d}: {list(roots)}")


def casoratian_obstruction():
    """At a cubic root the *saturated* Casoratian is nonunit."""
    ladders = get_ladders()
    for p, roots in SMALL_ROOTS.items():
        if p < 11:
            continue
        for r in roots:
            C = closed_casoratian(r)
            floors = [min(valuation(ladders[key][r+s], p) for s in range(3))
                      for key in ("Q", "P", "Ph")]
            saturated_v = valuation(C, p) - sum(floors)
            assert saturated_v >= 1
            print(f"  p={p:2d}, r={r:2d}: raw v(C)={valuation(C,p):2d}, "
                  f"column floors={floors}, saturated v(det)={saturated_v}")
    print("Saturated Casoratian at every p>=11 small cubic root is in p Z_p: PASS")
    print("  therefore the Session-7 nonvanishing argument cannot select Q here")


def exact_a1_oracle():
    """Finite exact gates at every cubic root with p<50."""
    ladders = get_ladders()
    hi = max(ladders["P"])
    for p, roots in SMALL_ROOTS.items():
        if p < 11:
            continue
        for r in roots:
            N = p + r
            assert N + 3 <= hi
            small_q = [ladders["Q"][r+s] for s in range(3)]
            qdigits = [int(q) % p for q in small_q]
            assert any(qdigits)

            # The CUB row is the reduction of the recurrence row.  Thus it
            # annihilates each integral/saturated solution triple at the root;
            # this explains, rather than repairs, the Casoratian rank drop.
            small_slack = {}
            for key in ("Q", "P", "Ph"):
                ys = [ladders[key][r+s] for s in range(3)]
                e = min(valuation(y, p) for y in ys)
                M = row_value(row_at(r), ys)
                small_slack[key] = valuation(M, p) - e
                assert small_slack[key] >= 1

            ys = [ladders["P"][N+s] for s in range(3)]
            e = min(valuation(y, p) for y in ys)
            M = row_value(row_at(N), ys)
            slack = valuation(M, p) - e
            assert e == -5 and slack >= 1

            # Exact finite check of the levelwise leading digit used by the
            # proposed determinant route.  Internal recurrence gates have
            # r<=p-4; at r=p-3,p-2,p-1 the three-level row meets the allowed
            # digit-boundary loss and is not a separate cubic gate.
            lead = [mod_unit(Fraction(p**5) * y, p) for y in ys]
            predicted = [mod_unit(RHO * ladders["Q"][N+s], p)
                         for s in range(3)]
            internal = r <= p - 4
            if internal:
                assert lead == predicted
            combined = ((2*r + 5) % p == 0)
            print(f"p={p:2d}, r={r:2d}: Q={qdigits}, e={e}, "
                  f"CUB-slack={slack}, small(Q,P,Ph)={small_slack}, "
                  f"LEAD={lead}, internal={internal}, combined={combined}  PASS")

    # At p=43 the midpoint and cubic factors coincide and the actual recurrence
    # asks for their sum.  The cached full recurrence numerator has the required
    # +2, but neither two separate +1 theorems nor this finite check proves it
    # uniformly.
    p, r = 43, 19
    N = p + r
    ys = [ladders["P"][N+s] for s in range(3)]
    e = min(valuation(y, p) for y in ys)
    M = row_value(row_at(N), ys)
    assert valuation(M, p) >= e + 2
    full = sum((Fraction(c(N)) * ys[i]
                for i, c in enumerate((c0, c1, c2))), Fraction(0))
    assert valuation(full, p) >= e + 2
    print("p=43 combined midpoint+cubic full depth-two gate: finite exact PASS")

    # The committed ladder reaches the small p=701 root, but not its a=1 lift
    # N=1049.  Record the structural half of the second combined exception.
    p, r = 701, 348
    assert a0(r) % p == 0 and (2*r + 5) % p == 0
    assert [int(ladders["Q"][r+s]) % p for s in range(3)] == [472, 350, 182]
    for key in ("Q", "P", "Ph"):
        small = [ladders[key][r+s] for s in range(3)]
        floor = min(valuation(y, p) for y in small)
        assert valuation(row_value(row_at(r), small), p) >= floor + 1
    print("p=701 combined small-root structure: exact PASS; a=1 lift unavailable")


def a1_depth_observation():
    # For p>=5 and p<=N<2p, 2N+5 lies strictly between 2p and 4p+5.
    # Direct enumeration makes the relevant assertion transparent: an a=1
    # midpoint can never have p^2 | 2N+5.
    for p in list(sp.primerange(5, 500)):
        for N in range(p, 2*p):
            assert (2*N + 5) % (p*p) != 0
    print("a=1 midpoint depth t>1 is impossible for p>=5: PASS")


def main():
    polynomial_certificate()
    small_root_oracle()
    casoratian_obstruction()
    exact_a1_oracle()
    a1_depth_observation()
    print("Cubic behavior characterized; uniform cubic gate remains OPEN")


if __name__ == "__main__":
    main()
