# Q3 certificate: the primitive midpoint `Q`-triple

Date: 20 July 2026.  Scope: primes `p >= 11` and only the three indices
`r,r+1,r+2`, where `r=(p-5)/2`.

## Theorem (Q3)

For the Brown--Zudilin integer

    Q_n = sum_{k,l=0}^n C(n+k,n) C(n,k)^2
                         C(n+l,n) C(n,l)^2 C(n+k+l,n),

and every prime `p >= 11`,

    not (Q_r = Q_(r+1) = Q_(r+2) = 0 mod p),
    r=(p-5)/2.

## 1. Fundamental Casoratian

The normalized order-three recurrence shared by `Q,P,Phat` is

    c0(n)Y_n+c1(n)Y_(n+1)+c2(n)Y_(n+2)+c3(n)Y_(n+3)=0,
    c0(n)=(n+1)^5(n+2)a0(n+1),
    c3(n)=2(n+3)^5(2n+5)a0(n),
    a0(n)=41218n^3+198849n^2+320790n+173057.

Let `C_n` be the determinant whose rows are the `(Q,P,Phat)` vectors at
`n,n+1,n+2`.  The companion-matrix determinant gives

    C_(n+1)/C_n = -c0(n)/c3(n).

At `n=1`, direct substitution of the exact first three rows gives

    C_1 = 13591/34560.

Telescoping (or one rational cancellation followed by induction) therefore
gives the exact identity

    C_n = (-1)^(n-1) a0(n) /
          [16 (n+1)^4 (n+2)^5 (2n+1)(2n+3) C(2n,n)].       (CAS)

Indeed, the quotient of the displayed right sides is

    - (n+1)^5(n+2)a0(n+1) /
      [2(n+3)^5(2n+5)a0(n)] = -c0(n)/c3(n).

This is an identity, not the earlier finite Casoratian audit.

## 2. Unit argument at the midpoint

Put `n=r=(p-5)/2`.  Every factor in the denominator of (CAS) is a `p`-unit:
`r+1,r+2,2r+1,2r+3` lie strictly between `0` and `p`, and `2r=p-5<p`, so
`C(2r,r)` is a `p`-unit.

The companion columns are `p`-integral at the same three rows without using
the global denominator conjecture.  Lemma C makes every base/companion
coefficient and harmonic sum in the defining minors `p`-integral when `m<p`.
The normalization divides by `C(2m,m)`, which is a `p`-unit because
`2m<=p-1`.  Hence `P_m,Phat_m in Z_p` for all three rows.  Thus, if the three
`Q` entries vanished modulo `p`, the first column of the Casoratian would
vanish and `C_r` could not be a `p`-unit.

It remains only to decide when its numerator can fail to be a unit.  Exactly,

    8 a0((p-5)/2)
      = 41218p^3-220572p^2+397530p-241144,
    241144 = 8*43*701.

Consequently `C_r` is a `p`-unit for every prime `p>=11` except possibly
`p=43,701`, proving (Q3) away from those two primes.

## 3. The two finite exceptional certificates

Direct reduction of the manifest double-binomial gives

    p=43,  r=19:  (Q_r,Q_(r+1),Q_(r+2)) = (33,0,26) mod 43;
    p=701, r=348: (Q_r,Q_(r+1),Q_(r+2)) = (472,350,182) mod 701.

Both are primitive.  `sol_q3.py` evaluates these sums using factorials below
`p` and one-digit Lucas for the final binomial.  It also gates the requested
oracle primes:

    p=11: (0,5,1),   p=13: (8,5,11),  p=17: (14,10,16),
    p=19: (15,2,0),  p=23: (6,22,13).

Therefore (Q3) is proved for every prime `p>=11`.

## 4. Literature audit

McCarthy--Osburn--Straub, arXiv:1705.05586, does identify the half-period
cellular value with the coefficient of the weight-six level-four newform.  In
this normalization `Q_((p-1)/2)` agrees modulo `p` with that coefficient; it
can vanish (already at `p=19`), so it cannot by itself prove Q3.  Zudilin,
arXiv:math/0206178, supplies the shared third-order recurrence.  The useful
nonvanishing mechanism here is its fundamental Casoratian, not a claim that
one fixed member of the triple is always ordinary.

Checker:

    PYTHONPATH=worthiness python3 worthiness/sol_q3.py
