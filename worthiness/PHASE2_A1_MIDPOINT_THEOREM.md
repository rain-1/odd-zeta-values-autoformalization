# Complete generic midpoint theorem -- `a=1` band only

Date: 20 July 2026.

## Scope and statement

Let `p>=11` be prime,

    r=(p-5)/2,  N=p+r=(3p-5)/2,
    M_p=11907P_N-334374P_(N+1)-19292P_(N+2),
    e_p=min_{0<=s<=2} v_p(P_(N+s)).

Then

    e_p=-5,
    v_p(M_p) >= e_p+1 = -4.                              (A1-MID)

Equivalently `p^4 M_p` is `p`-integral.  This is the saturated simple-midpoint
gate needed by the descent at the three levels `N,N+1,N+2`.

This theorem is **only the `a=1` midpoint band**.  It makes no claim for
`a>1`, for prime-power midpoint depth, or for the separate cubic gates.

## Certificate-shaped assembly

For `m=N+s`, define the exact head errors

    E_m = p^5 Sing_m-(29/28)u_m-(101/84)p^2w_m,
    Et_m=p^5 Singt_m-(29/28)ut_m-(101/84)p^2wt_m.

The exact determinant identity, after the fixed three-level row, is

    p^5 M_p
      =(29/28) sum_s alpha_s q_(N+s)
       +sum_s alpha_s (wt E-w Et)_(N+s)
       +sum_C sum_s alpha_s p^5(wt R_C-w Rt_C)_(N+s),    (DET-MID)

where

    alpha_s=R_s(-1)^(N+s+1)/C(2(N+s),N+s),
    (R_0,R_1,R_2)=(11907,-334374,-19292),

and `C` is head+tail or middle after reflection.

The already proved certificate inputs are:

1. **Q/Lucas row.** `Q_(p+t)=Q_1 Q_t mod p`, and the midpoint recurrence row
   gives `sum_s R_s Q_(r+s)=0 mod p`.  Hence the Q term in (DET-MID) vanishes
   modulo `p` after the unit binomial normalization.
2. **(H).** The weight-five Phi/Bell row and the infinity relation `E_1=0`
   give `E_m,Et_m in p^5 Z_p`.  Since `w_m,wt_m in p^-2 Z_p`, the head-error
   determinant lies in `p^3 Z_p`.
3. **(RT).** The reflected J12/J3 certificates give
   `R_ht,Rt_ht in p^-2 Z_p`; hence their determinant contribution lies in
   `p Z_p`.
4. **(RM).** The middle factorial count gives `R_mid,Rt_mid in p Z_p`; hence
   its determinant contribution lies in `p^4 Z_p`.

All binomial normalizers in this row are units.  Reducing the levelwise exact
determinant before summation also gives

    p^5 P_(p+t) = (29/28) Q_(p+t) mod p.                 (LEAD)

By the proved Q3 certificate, not all of `Q_r,Q_(r+1),Q_(r+2)` vanish.  Since
`Q_1=21` is a unit for `p>=11`, Lucas and (LEAD) therefore show that at least one of
`p^5P_N,p^5P_(N+1),p^5P_(N+2)` is a unit.  The existing denominator floor
gives valuation at least `-5` for all three, so

    e_p=-5.                                               (U)

Finally, every term on the right of (DET-MID) belongs to `p Z_p`.  Therefore
`p^5M_p in p Z_p`, or `v_p(M_p)>=-4=e_p+1`, which is (A1-MID).

## Dependency ledger

- `(DET-MID)`, chamber reflection, Q row: `PHASE2_MIDPOINT_GATE.md`.
- `(RM)`: Session 4 handoff.
- J12 and `(RT)`: `PHASE2_J12_CERTIFICATE.md`, Session 5 handoff.
- `(H)`, `(H-NF)=E_1`, `(LEAD)`: `PHASE2_H5_CERTIFICATE.md`, Session 6 handoff.
- `(Q3)`: `PHASE2_Q3_CERTIFICATE.md`.

The requested direct gates at `p=11,13,17,19,23` are printed by
`sol_q3.py`; the earlier exact residual checkers cover the determinant pieces.
