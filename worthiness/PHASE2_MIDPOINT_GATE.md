# Phase 2: the a=1 midpoint gate in saturated determinant form

Date: 20 July 2026.  Script: `sol_midpoint_gate.py`.

This note treats only the generic midpoint requested in the session-2 handoff.
Exact identities are distinguished from finite verification.  No general
midpoint theorem is claimed.

## 1. Target and exact local reduction

Let `p` be an odd prime, set

    r=(p-5)/2,  N=p+r=(3p-5)/2,

and put

    M_p = 11907 P_N-334374 P_(N+1)-19292 P_(N+2),
    e_p = min_{0<=s<=2} v_p(P_(N+s)).

Then `2N+5=3p`.  For `p!=7` the exact polynomial identity from
`sol_local_regular.py`,

    128 c_i(m)=7 R_i+(2m+5)H_i(m),
    (R_0,R_1,R_2)=(11907,-334374,-19292),

shows that the a=1 simple midpoint gate is exactly the certificate

    Z_p := p^(-e_p-1) M_p in Z_p.                         (MID-Z)

This is the saturated form: it does not divide by any chosen coordinate of the
three-value P-vector.

## 2. Both residuals and the determinant (exact)

At a level `m=p+r_m`, `0<=r_m<p`, write the exact harmonic split

    v_m  = Sing_m  + R_m,
    vt_m = Singt_m + Rt_m,

and define

    E_m  = p^5 Sing_m  - rho u_m  - sigma p^2 w_m,
    Et_m = p^5 Singt_m - rho ut_m - sigma p^2 wt_m,
    rho=29/28, sigma=101/84.

Since `p_m=wt_m v_m-w_m vt_m` and `q_m=u_m wt_m-ut_m w_m`, direct expansion
gives the exact identity

    p^5 p_m-rho q_m
      = wt_m E_m-w_m Et_m + p^5(wt_m R_m-w_m Rt_m).        (DET-m)

This is the point at which the old scalar head-window calculation was
insufficient: neither `R_m` nor `Rt_m` may be discarded before their
determinant is formed.

Let

    alpha_s = R_s (-1)^(N+s+1)/binom(2(N+s),N+s).

Summing (DET-m) for `m=N,N+1,N+2` gives, exactly,

    p^5 M_p
      = rho sum_s alpha_s q_(N+s)
        + sum_s alpha_s (wt E-w Et)_(N+s)
        + sum_C sum_s alpha_s p^5(wt R_C-w Rt_C)_(N+s),   (DET-MID)

where `C` runs over the three chambers below.

## 3. Chamber reduction (exact)

For each `m=N+s` split the regular residual at the two digit thresholds:

    C_h=[0,r_m], C_0=[r_m+1,p-1], C_t=[p,p+r_m].

The proved reflection law for the base coefficients and its direct consequence
for the companion coefficients are

    a_(i,m-j)=(-1)^(i+1)a_(i,j),
    at_(i,m-j)=(-1)^(i+1)at_(i,j).

Thus the head and tail residuals reduce, before taking a determinant, to

    R_h+R_t = sum_(i=1)^6 sum_(b=0)^r_m a_(i,b) K_(i,b;m),
    Rt_h+Rt_t = sum_(i=1)^6 sum_(b=0)^r_m at_(i,b) K_(i,b;m),

with the explicit regular kernel

    K_(i,b;m)=H_b^(i)+(-1)^(i+1)(H_(m-b)^(i)-p^(-i)).     (PAIR)

The middle chamber is reflection-stable and remains a separate finite sum.
Equations (DET-MID) and (PAIR) are the requested chamber-by-chamber determinant
form.  `sol_midpoint_gate.py` asserts all of them over the rationals.

## 4. The Q term is closed by the Lucas theorem

The proven Lucas row gives `Q_(p+t)=Q_1 Q_t (mod p)`.  At the small index `r`,
the recurrence and `p | c_3(r)` give

    sum_(s=0)^2 c_s(r)Q_(r+s)=0 (mod p).

The exact midpoint coefficient identity then yields, for `p!=2,7`,

    11907 Q_r-334374 Q_(r+1)-19292 Q_(r+2)=0 (mod p).

Therefore the first term on the right of (DET-MID) is p-integral and vanishes
modulo `p` (the binomial normalizers are p-units at these three levels).  This
uses Q only through its integer Lucas theorem; it does not assert that `a0` is
apparent for Q.  In particular it is compatible with the order injection at
`(n,p)=(306,7)`.

## 5. Exact finite verification

The committed ladder `falsify_data/ladder_P.json` was loaded, not regenerated.
For every nonexceptional prime with `11<=p<=239` and `N+2<=360`:

- 45 midpoint witnesses were checked;
- 0 violate (MID-Z);
- all 45 have `e_p=-5`;
- 44 are tight (`v_p(M_p)=e_p+1=-4`);
- `p=131` has one extra order.

The full Bell/residual/determinant assembly was run for
`p=11,13,17,19,23,31,37`.  Every exact gate passed, including agreement with
both `sol_hw_allr.error` outputs and with the cached normalized P ladder.
Writing valuations relative to the required scale `p^(e_p+6)=p` in `p^5M_p`,
the generic pattern is

| assembled piece | observed relative valuation |
|---|---:|
| Q/Lucas piece | 0 |
| head-error determinant | at least 2 |
| regular head alone | -3 or -2 |
| regular tail alone | -3 or -2 |
| head+tail after reflection, both residuals, determinant, and three levels | at least 5 |
| regular middle | at least 6 |

This demonstrates why premature reduction of either residual is invalid: the
two dangerous chambers are nonintegral separately and cancel only in the final
paired determinant.

## 6. Honest proof frontier

The midpoint gate is **not proved**.  What is proved is the exact reduction to
(DET-MID)/(PAIR), together with the Q/Lucas component.  A complete generic
certificate still needs symbolic proofs of:

1. the unit-floor statement `e_p=-5` (or a version of the following bounds that
   scales with the actual `e_p`);
2. the three-level head-error determinant in `p Z_p`;
3. the reflected head+tail regular determinant in `p Z_p`;
4. the middle regular determinant in `p Z_p`.

The exact computations show much larger margins for items 2--4, but those
margins are evidence.  The next calculation should substitute the Phi
factorial blocks and Bell layers into the explicit kernel (PAIR), reduce the
three fixed offsets `r,r+1,r+2` simultaneously modulo p, and preserve the
boundary terms at `b=0,r_s` until the determinant is formed.  The regular
head+tail congruence is the first target: it is the only place where raw pieces
lie below the desired lattice.

