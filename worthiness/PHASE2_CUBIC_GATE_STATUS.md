# The `a=1` cubic gates: exact status

Date: 20 July 2026. Checker: `sol_cubic_gates.py`.

## Verdict

The cubic gate behaves differently from the midpoint gate. The exact and
finite calculations support regularity of `P`; they do **not** support a need
to subtract a singular `Phat` direction. But the Session-7 Casoratian argument
cannot prove the required primitive leading digit at a cubic root, because its
determinant vanishes there for a structural reason.

Consequently the uniform cubic gate, and hence the complete `a=1` one-step
descent theorem, remain open.

## Exact structure

Let

    a0(n)=41218n^3+198849n^2+320790n+173057

and let `A_0,A_1,A_2,D` be the quadratic CUB row of Session 2. Exact polynomial
division gives

    D c_i(n) = A_i(n)+a0(n)K_i(n),  i=0,1,2,
    D=2^5 37^5 557^2.                                      (CUB-row)

At a residue `r` with `a0(r)=0 mod p`, this is the reduction of the recurrence
row. It annihilates every saturated solution triple, not only the `P` triple.
In particular, after each of the three columns `(Q,P,Phat)` is primitively
scaled, they have a common nonzero left annihilator modulo `p`. Therefore the
**saturated** Casoratian must vanish modulo `p`. Its raw closed formula is

    C_r=(-1)^(r-1)a0(r)/
        [16(r+1)^4(r+2)^5(2r+1)(2r+3) binom(2r,r)].

At upper roots, factors in the displayed denominator can cancel the valuation
of `a0(r)`, so the raw `C_r` need not itself be in `p Z_p`. The exact oracle
confirms instead that `v_p(C_r)` minus the three column floors is always
positive. Thus dividing the numerator by `a0(r)` and declaring the quotient a
unit does not prove that the `Q` column is nonzero. It proves only a
first-jet/rank statement about the whole solution plane. A zero `Q` column is
compatible with that statement. This is the precise self-reference
obstruction.

## What would close a simple cubic gate

For `N=p+r`, the desired row is

    v_p(sum_i A_i(N)P_(N+i)) >= e+1,
    e=min_i v_p(P_(N+i)).                                  (CUB)

The midpoint determinant machinery suggests the following sufficient pair:

1. extend the levelwise congruence

       p^5 P_(p+t) = (29/28)Q_(p+t) mod p                 (LEAD-all-r)

   from the three midpoint levels to all cubic residues;
2. prove that `(Q_r,Q_(r+1),Q_(r+2))` is primitive whenever `a0(r)=0 mod p`.

Then Lucas and (CUB-row) make the CUB combination vanish modulo `p`, while the
primitive Q digit gives `e=-5`. The exact oracle confirms both conclusions at
every cubic root for `11<=p<50`, but neither item is presently a uniform
theorem. The Phi formulas used in the midpoint proof assumed `2r<p`; upper
cubic roots require an additional factorial-block chamber, so (LEAD-all-r)
cannot be quoted from the midpoint certificate.

The alternative is a genuine first-jet theorem: identify the saturated
connection map across `a0=0` and prove directly that its `P` coordinate is
regular. The Casoratian quotient alone is insufficient; one needs an adjugate
minor or connection coefficient selecting the `P` solution. `Phat` is useful
as the third column in that calculation, but the data do not call for
subtracting a `Phat` singular direction: for every oracle row with `p>=11`,
the normalized `Phat` triple itself satisfies the same CUB row with one or
more orders of slack.

## Exact small-prime gates

The roots of `a0` for primes below 50 are

    p=7:  2,6
    p=11: 5,6,9
    p=13: 7
    p=17: 8
    p=23: 17
    p=29: 27
    p=41: 10
    p=43: 19.

For every listed root with `p>=11`, the committed exact ladder gives `e=-5`
and verifies (CUB). At every internal recurrence gate (`r<=p-4`) it also gives
the predicted leading digits from `p^5P=(29/28)Q mod p`. Roots in the final
three residues meet the separate digit-boundary factor `(r+3)^5` and are not
independent cubic gates; their CUB rows are retained as diagnostics. These are
finite exact gates, not a proof.

At `p=43,r=19`, the cubic and midpoint factors coincide. The recurrence needs
the **sum** of their depths, namely `e+2`; two separate `e+1` estimates would
not suffice. The exact cached full recurrence numerator has the required two
orders of slack. At `p=701,r=348`, the cache verifies the small-root Q/P/Phat
structure, including Q digits `[472,350,182]`, but the `a=1` lift `N=1049`
lies beyond it. Thus even generic simple cubic closure would still leave these
two combined gates as a separate depth-two argument.

Finally, prime-power midpoint depth `t>1` cannot occur inside the `a=1` block:
if `p<=N<2p` and `p>=5`, then `p^2` never divides `2N+5`. That depth problem is
necessarily a later-digit (`a>1`) transport problem, not part of the literal
`a=1` gate.
