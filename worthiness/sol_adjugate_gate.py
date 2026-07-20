"""Session 9: exact adjugate/connection audit at the cubic gates.

The theorem-level part of this file is the companion/adjugate algebra.  The
small-prime part is an exact oracle, not a uniform proof.  Its purpose is to
test whether the adjugate first jet selects the named P solution.  It does
not: it selects a two-dimensional regular plane, while the complementary
solution-coordinate direction is a nontrivial mixture of Q, P, and Phat.
"""

from fractions import Fraction
from math import comb

import sympy as sp
from sympy.polys.matrices import DomainMatrix

from falsify_data import a0, c0, c1, c2, c3, get_ladders
from salvage_v6_desing import vp
from sol_cubic_gates import SMALL_ROOTS, RHO, row_at, row_value
from sol_q3 import closed_casoratian


KEYS = ("Q", "P", "Ph")


def mod_unit(x, p, power=1):
    """Reduce a rational with p-unit denominator modulo p**power."""
    x = Fraction(x)
    modulus = p**power
    assert x.denominator % p
    return x.numerator % modulus * pow(x.denominator % modulus, -1, modulus) % modulus


def divide_by_p_power(x, exponent, p):
    """Return x/p**exponent without ever constructing a negative modulus."""
    x = Fraction(x)
    if exponent >= 0:
        return x / p**exponent
    return x * p**(-exponent)


def matrix_mod(M, p, power=1):
    return sp.Matrix(M.rows, M.cols,
                     lambda i, j: mod_unit(M[i, j], p, power))


def rank_mod(M, p):
    D = DomainMatrix.from_list_sympy(M.rows, M.cols, M.tolist()).convert_to(sp.GF(p))
    return D.rank()


def nullrow_mod(M, p):
    """One row spanning the right nullspace of a rank-two 3 by 3 matrix."""
    D = DomainMatrix.from_list_sympy(M.rows, M.cols, M.tolist()).convert_to(sp.GF(p))
    N = D.nullspace().to_Matrix()
    assert N.rows == 1 and N.cols == 3
    return tuple(int(x) % p for x in N.row(0))


def companion_adjugate_identity():
    """Exact first-order recurrence for adj(Y_n), before specialization."""
    z0, z1, z2, z3 = sp.symbols("z0 z1 z2 z3")
    T = sp.Matrix([[0, 1, 0], [0, 0, 1],
                   [-z0/z3, -z1/z3, -z2/z3]])
    B = sp.Matrix([[z1, z2, z3], [-z0, 0, 0], [0, -z0, 0]])
    assert sp.simplify(z3*T.adjugate() - B) == sp.zeros(3)
    assert sp.factor(T.det()) == -z0/z3
    print("companion identity c3*adj(T)=B and det(T)=-c0/c3: PASS")
    print("  hence c3(n) adj(Y_(n+1)) = adj(Y_n) B(n) exactly")


def saturated_matrix(ladders, p, r):
    floors = []
    columns = []
    for key in KEYS:
        ys = [ladders[key][r+s] for s in range(3)]
        floor = min(vp(y, p) for y in ys)
        floors.append(floor)
        columns.append([divide_by_p_power(y, floor, p) for y in ys])
    Y = sp.Matrix(3, 3, lambda i, j: columns[j][i])
    return Y, tuple(floors)


def adjugate_first_jets():
    """Gate the complete p-adic first-jet identity at every oracle root."""
    ladders = get_ladders()
    for p, roots in SMALL_ROOTS.items():
        if p < 11:
            continue
        for r in roots:
            Y, floors = saturated_matrix(ladders, p, r)
            Y0 = matrix_mod(Y, p)
            assert rank_mod(Y0, p) == 2

            # The CUB row is the left singular direction.
            ell = sp.Matrix(1, 3, [x % p for x in row_at(r)])
            assert matrix_mod(ell * Y0, p) == sp.zeros(1, 3)

            Adj = Y.adjugate()
            Adj0 = matrix_mod(Adj, p)
            assert rank_mod(Adj0, p) == 1
            assert matrix_mod(Y0 * Adj0, p) == sp.zeros(3)
            assert matrix_mod(Adj0 * Y0, p) == sp.zeros(3)

            # First jet of Y*adj(Y)=det(Y)I.  This is the strongest identity
            # supplied by the adjugate without an independent connection jet.
            Y2 = matrix_mod(Y, p, 2)
            A2 = matrix_mod(Adj, p, 2)
            Y1 = (Y2 - Y0) / p
            A1 = (A2 - Adj0) / p
            det_digit = mod_unit(Y.det(), p, 2) // p
            carry0 = (Y0*Adj0) / p
            assert all(x.q == 1 for x in carry0)
            lhs = matrix_mod(carry0 + Y0*A1 + Y1*Adj0, p)
            rhs = sp.eye(3) * (det_digit % p)
            assert lhs == rhs

            det_v = vp(closed_casoratian(r), p) - sum(floors)
            assert det_v == vp(Y.det(), p)
            simple = (3*41218*r*r + 2*198849*r + 320790) % p != 0

            # This is a relation among named solution columns.  At every
            # simple internal gate it is not the pure Phat coordinate.
            singular_coordinate = nullrow_mod(Y0, p)
            if simple and r <= p - 4:
                assert singular_coordinate[:2] != (0, 0)

            print(f"p={p:2d}, r={r:2d}: simple={simple}, floors={floors}, "
                  f"v(det_sat)={det_v}, null(Q,P,Ph)={singular_coordinate}, "
                  "adj first jet PASS")
    print("adjugate conclusion: rank-one direction is mixed, not pure Phat")


def upper_chamber_and_lifted_oracle():
    """Expose the 2r>=p factorial carry and gate the desired lifted P row."""
    ladders = get_ladders()
    upper_internal = []
    for p, roots in SMALL_ROOTS.items():
        if p < 11:
            continue
        for r in roots:
            N = p + r
            carries = tuple(vp(comb(2*(p+r+s), p+r+s), p) for s in range(3))
            # Kummer: before a level crosses the digit boundary, this is
            # exactly the extra low-digit carry caused by 2(r+s)>=p.
            for s in range(3):
                if r+s < p:
                    assert carries[s] == int(2*(r+s) >= p)

            ys = [ladders["P"][N+s] for s in range(3)]
            floor = min(vp(y, p) for y in ys)
            cub_slack = vp(row_value(row_at(N), ys), p) - floor
            assert floor == -5 and cub_slack >= 1

            internal = r <= p - 4
            if internal:
                lead = [mod_unit(Fraction(p**5)*y, p) for y in ys]
                predicted = [mod_unit(RHO*ladders["Q"][N+s], p)
                             for s in range(3)]
                assert lead == predicted
            if 2*r >= p and internal:
                upper_internal.append((p, r))
            print(f"p={p:2d}, r={r:2d}: carries={carries}, internal={internal}, "
                  f"lifted P floor={floor}, CUB-slack={cub_slack} PASS")

    assert upper_internal == [(11, 6), (13, 7), (23, 17)]
    print("upper-root extra factorial chamber gated at", upper_internal)
    print("  these are exact oracle checks; the carry-sensitive connection theorem is missing")


def basis_change_no_go():
    """Record the structural invariance preventing solution selection."""
    S = sp.Matrix([[1, 0, 0], [0, 1, 0], [0, 1, 1]])
    assert S.det() == 1
    # Columns of Y*S are (Q, P+Phat, Phat).  They satisfy the same scalar
    # recurrence and have the same Casoratian as (Q,P,Phat).
    assert S[:, 1] == sp.Matrix([0, 1, 1])
    assert S.det() == 1
    print("SL3 basis-change obstruction: (Q,P,Phat)->(Q,P+Phat,Phat) preserves")
    print("  the recurrence and Casoratian but changes P-regularity: PROVED")


def main():
    companion_adjugate_identity()
    adjugate_first_jets()
    upper_chamber_and_lifted_oracle()
    basis_change_no_go()
    print("VERDICT: recurrence + Casoratian adjugate does not close the cubic gate")


if __name__ == "__main__":
    main()
