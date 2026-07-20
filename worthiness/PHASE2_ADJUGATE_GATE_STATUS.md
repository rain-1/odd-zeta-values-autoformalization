# The cubic adjugate/connection first jet: exact obstruction

Date: 20 July 2026. Checker: `sol_adjugate_gate.py`.

## Verdict

The adjugate route does **not** close the cubic gate from the recurrence and
Casoratian alone.  The adjugate is regular and rank one at a simple cubic
root, exactly as expected, but it selects the regular two-plane in the space
of level triples.  It does not select the named `P` column inside the fixed
solution basis `(Q,P,Phat)`.

The missing input is now precise: a Frobenius/connection coefficient, in the
named period basis, proving that the normalized lifted `P` digit belongs to
that regular plane.  In the upper-root chamber this coefficient must include
the extra factorial carry.  This is arithmetic information about `P`; it is
not determined by the scalar recurrence or its determinant.

Consequently the complete `a=1` one-step descent remains open.  The proved
`a=1` midpoint theorem remains the standalone result of Session 7.

## 1. Exact adjugate recurrence

Put

    Y_n = ( (Q,P,Phat) at rows n,n+1,n+2 )

and let `A_n=adj(Y_n)`.  The companion step is

    Y_(n+1)=T_n Y_n,
    T_n = [[0,1,0], [0,0,1],
           [-c0/c3,-c1/c3,-c2/c3]].

Direct classical-adjoint algebra gives

    det(T_n)=-c0/c3,

    c3 adj(T_n)=B_n
      = [[c1,c2,c3],[-c0,0,0],[0,-c0,0]],

and hence, using `adj(TY)=adj(Y)adj(T)`,

    c3(n) A_(n+1) = A_n B_n.                         (ADJ-REC)

This is an exact polynomial/rational identity.  It contains no primitive-Q
input.

At a residue `r` with `a0(r)=0 mod p`, reduction of `(ADJ-REC)` gives

    A_r B_r=0,

while the recurrence row gives

    ell_r Y_r=0,
    ell_r=(A_0(r),A_1(r),A_2(r)),                     (REG-PLANE)

where the `A_i` on the right are the Session-2 CUB coefficients.  Thus the
regular plane of level triples is `ker(ell_r)`.

## 2. What the first jet actually says

After primitive column saturation, write over the local DVR

    Y=Y_0+pY_1+...,
    adj(Y)=J_0+pJ_1+...,
    det(Y)=p delta+...                                 (simple rank drop).

The first jet of `Y adj(Y)=det(Y)I` is

    Y_0 J_0=J_0 Y_0=0,
    Y_0 J_1+Y_1 J_0=delta I.                           (ADJ-JET)

The checker verifies `(ADJ-JET)` exactly modulo `p` at every listed root
(with `delta=0` when saturation raises the determinant order).  Since `Y_0`
has rank two, `J_0` has rank one and factors as

    J_0 = v_r ell_r

up to a nonzero scalar and the row/column orientation.  Here `ell_r` is the
CUB left annihilator, while `v_r` is a relation among the three **solution
columns**.  Therefore `(ADJ-JET)` identifies the quotient transverse to the
regular plane, but membership of a named column in that plane still requires
its connection coefficient.

There is also a direct logical obstruction.  For any constant `S in SL_3`,
`Y'_n=Y_n S` satisfies the same scalar recurrence and has the same
Casoratian.  In particular

    (Q,P,Phat) -> (Q,P+Phat,Phat)

preserves every recurrence and determinant identity used above.  If `Phat`
has a singular component and `P` does not, this change alters the regularity
of the column called `P`.  No invariant of the recurrence plus Casoratian can
distinguish the two bases.  Named initial/period connection data is mandatory.

The oracle makes this failure visible rather than merely formal.  At the
simple internal roots, the saturated right-null vectors in `(Q,P,Phat)`
coordinates are

    (p,r)=(11,5): (3,8,3),    (11,6): (7,4,7),
          (13,7): (5,12,8),   (17,8): (10,14,16),
          (23,17):(11,17,14), (41,10):(38,25,10),
          (43,19):(30,9,30).

None is the pure `Phat` direction.  Thus the proposed identification of the
excluded adjugate direction with the named `Phat` row is false in the actual
saturated matrices.  (`p=29,r=27` is a multiple root of `a0 mod 29`, not a
simple-root instance; it is also a digit-boundary diagnostic.)

## 3. The exact missing identity

For `N=p+r`, set

    x_P=(p^5 P_N,p^5 P_(N+1),p^5 P_(N+2)) mod p.

The desired simple CUB divisibility is exactly

    ell_r x_P=0.                                       (P-CONN)

The adjugate supplies `ell_r` and proves that its kernel is the regular plane.
It supplies no value for `x_P`, and hence cannot prove `(P-CONN)`.  Equivalently,
one needs the `P` column of the one-digit Frobenius connection matrix.  The
already observed stronger identity

    p^5 P_(p+r+s)=(29/28)Q_(p+r+s) mod p

would supply it, but proving that identity in all cubic chambers is precisely
the missing arithmetic input; importing it here would be circular.

Although the rational initial values and recurrence determine each fixed
`P_n`, they do not turn `(P-CONN)` into a uniform prime-independent consequence
of the Casoratian.  A viable proof must evaluate the named connection
coefficient, for example from the defining hypergeometric/period determinant
or an equivalent Dwork theorem.

## 4. Upper-root factorial chamber

The internal upper roots in the requested oracle range are

    (p,r)=(11,6),(13,7),(23,17).

For all three offsets `s=0,1,2`, Kummer's carry in
`binom(2(p+r+s),p+r+s)` is one.  Thus their carry vectors are `(1,1,1)`,
whereas the lower chambers may have `(0,0,0)` or cross only in later offsets.
This is the extra factorial block absent from the midpoint fixed-block proof.

The exact ladder verifies in each upper chamber:

    min_s v_p(P_(p+r+s))=-5,
    v_p(sum_s A_s(p+r)P_(p+r+s)) >= -4,
    p^5P_(p+r+s)=(29/28)Q_(p+r+s) mod p.

These are exact finite oracle gates, not a proof of the carry-sensitive
connection coefficient.  The boundary roots `(11,9)` and `(29,27)` cross
`r+s=p` and are not independent three-level cubic gates.

At `(43,19)` the simple cubic and midpoint factors coincide.  Even a proof of
generic `(P-CONN)` would still need their combined depth-two divisibility.  The
existing finite oracle passes it.  The second combined case `(701,348)` still
lacks the lifted `a=1` ladder value.

## 5. Research question left by the wall

Compute the named one-digit Frobenius connection matrix (or only its `P`
column) through the cubic singular residue, including the `2r>=p` carry
correction, and prove that its residue lies in `ker(ell_r)`.  To explain the
`Phat` leak, the same calculation should show a nonzero transverse coefficient
for the appropriate normalized `Phat` branch.  That distinction cannot be
recovered from `(ADJ-REC)`, `(ADJ-JET)`, and the Casoratian alone.

