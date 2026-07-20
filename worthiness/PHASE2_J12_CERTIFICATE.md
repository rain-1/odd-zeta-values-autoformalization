# J12 certificate for the generic `a=1` midpoint

Date: 20 July 2026.  Checker: `sol_j12.py`.

This note closes the local congruence called `J12` in
`PHASE2_FROM_SOL_4.txt`.  It applies to every prime `p >= 11`, each
`s in {0,1,2}`, and

    r=(p-5)/2+s,  m=p+r,  0<=b<=r,  c=r-b.

All congruences are in `Z_p`.  The endpoint pair `{0,r}` and a possible
central singleton `b=c` are not absorbed into an interior summation.

## 1. Truncated Phi and collision algebra — proved

Put `A_i(b)=p^(6-i)a_(i,b)`.  In the noncentral branch set `d=c-b`, a
`p`-adic unit.  Removing the common factor `(-1)^m(p-1)!^2`, PHI-6 and

    E_e(x)=1+xp H_e^(1)
             +(x^2p^2/2)((H_e^(1))^2-H_e^(2)) mod p^3

give

    a_6(b)=q_b(1+p u_b+p^2 v_b) mod p^3,
    q_c=-q_b,

where, with `H_e=H_e^(1)`,

    U_b=4H_r+H_(r+b)+2H_(r+c)-7H_c,
    S_b=4H_r^(2)+H_(r+b)^(2)+4H_(r+c)^(2)-7H_c^(2),
    u_b=U_b+1/d,
    v_b=(U_b^2-S_b)/2+U_b/d.

The factor `E_(p-1)(1)` is `1 mod p^3` by Wolstenholme.  Collision extraction
from `D_t` gives

    delta_t(b):=p^tD_t(b)=lambda_t+regular terms,
    (lambda_1,...,lambda_5)=(-13/2,19/4,-55/4,237/8,-669/4),

and, to the precision which can reach J12,

    delta_1=lambda_1+p x_b+p^2 y_b mod p^3,
    delta_2=lambda_2+p^2 z_b mod p^3,
    delta_t=lambda_t mod p^3  (t=3,4,5),

with

    x_b=2/d-H_(r+b)+H_(r+c)-7H_c+7H_b,
    y_b=-4/d^2+H_(r+b)^(2)-2H_(r+c)^(2)+7H_c^(2),
    z_b=-4/d^2-H_(r+b)^(2)-H_(r+c)^(2)
                    +7(H_b^(2)+H_c^(2)).

The omitted full `(p-1)` blocks first enter in degree three: odd full-block
harmonics have valuation at least two and even ones valuation at least one.
Thus no discarded term can contribute to the displayed three coefficients.

At the collision constants the two relevant Bell polynomials have jets

    Y_5/5!=-287+(287/2)p x
       +p^2((287/2)y-(127/4)z-(127/4)x^2),
    Y_4/4!=287/2-(127/2)p x
       +p^2(-(127/2)y+(47/4)z+(47/4)x^2).

Direct substitution under `b<->c` proves the three reflection jets

    A_1(c)=-A_1(b)                         mod p^3,       (T1)
    A_2(b)-A_2(c)=-A_1(b)                  mod p^2,       (T2)
    A_2(b)+A_2(c)=0                        mod p.         (T3)

`sol_j12.abstract_pair_certificate` verifies these identities after clearing
the formal denominators in the independent harmonic alphabet.  This is a
symbolic identity check, not interpolation.

## 2. Kernel collection — proved

Write `Omega_1=H_(p-1)^(1)/p^2` and
`Omega_2=H_(p-1)^(2)/p`.  The reflected kernels are

    K_1(b)=H_b+H_c-pH_c^(2)+p^2(H_c^(3)+Omega_1) mod p^3,
    K_2(b)=H_b^(2)-H_c^(2)
             +p(2H_c^(3)-Omega_2) mod p^2.

The formulas with `b,c` exchanged give

    K_1(b)-K_1(c)
       =p(H_b^(2)-H_c^(2))-p^2(H_b^(3)-H_c^(3)),

while the common `Omega_1,Omega_2` terms disappear by (T1) and (T3).
Substitution of (T1)--(T3) now makes the coefficients of `1,p,p^2` in

    A_1(b)K_1(b)+A_1(c)K_1(c)
      +p(A_2(b)K_2(b)+A_2(c)K_2(c))

equal to `(0,0,0)`.  Hence `J12(b)` holds modulo `p^3` for every noncentral
pair.  The exact companion identity

    At_i=b(m-b)A_i+p(2b-m)A_(i+1)-p^2A_(i+2)

reduces its three coefficients to the same collection; the symbolic checker
clears them identically as well.

## 3. Boundary branches — proved

For the endpoint pair `{0,r}`, `d=r` is a `p`-adic unit.  The same displayed
formulas apply without deleting `H_0=0`; the checker retains this as a named
branch and obtains `(0,0,0)` for both arrays.

If `b=c`, the factor `(m/2-b)=p/2` gives `p|a_6`.  The collision constants gain
the centre contribution and satisfy

    (Y_5/5!)_centre=0,  (Y_4/4!)_centre=33/2.

The direct central expansion therefore gives `A_1=0 mod p^3`, `A_2 in pZ_p`,
and `K_2 in pZ_p`; the singleton J12 expression is zero modulo `p^3`.
The companion formula preserves the same bound.  This branch never divides by
the central factor.  Explicitly, the coefficient of `p` in the central
`delta_1` is
`-H_(3r/2)+H_(3r/2)-7H_(r/2)+7H_(r/2)=0`; combined with
`(Y_5/5!)_centre=0` and `p|a_6`, this is the second extra order in `A_1`.

## 4. Required coefficient gates — exact finite checks

Before the symbolic zeros were accepted, all three coefficients were
specialized at `p=11,13,17`, all three offsets, both arrays, every local pair.
Each returned `(0,0,0)`.  Independently, the exact rational oracle returned
`v_p(J12)>=3` in every row.  These specializations are regression gates; the
proof is the prime-independent collection above.

## 5. Consequence for RT — proved

J12 gives the layer-`1+2` local floor `p^-2 Z_p`.  The already proved J3 gives
the same floor for layer 3; the elementary collision counts give it for layers
4--6.  Thus both reflected residuals lie in `p^-2 Z_p` at each of the three
levels.  Since `w,wtilde in p^-2 Z_p`,

    p^5(wtilde R_ht-w Rtilde_ht) in p Z_p.

Here every midpoint binomial normalizer is a unit (`2r_s<p`), and the fixed
three-level row preserves the bound.  Therefore `(RT)` is closed.

Verification status: all statements above are proved by the displayed finite
algebra, with exact-oracle and prime-specialization checks as independent
guards.  No claim about `(H)` or the complete midpoint theorem is made here.
