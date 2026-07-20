# Weight-five head-window certificate

Date: 20 July 2026.  Checker: `sol_h5.py`.

This note closes `(H)` for the three generic `a=1` midpoint levels.  Let

    r=(p-5)/2+s,  m=p+r,  s in {0,1,2},  p>=11,
    0<=b<=r,       c=r-b.

Write `a[i,b]` for the coefficients at index `m`, and write `beta[i,b]`
for the coefficients of the same rational function at the small index `r`.
Tildes have the analogous meaning.  All congruences below are in `Z_p`.

## 1. One Bell functional

Put `A_i=p^(6-i)a[i,b]`.  The reflected local head term of Session 5 is

    T(b)=sum_i (-1)^(i+1)p^(5-i)a[i,b]
           -2(29/28)a[5,b]-2(101/84)p^2a[3,b].

Thus

    p T(b)=F(A(b)),

where

    F(A)=A_1-A_2-(59/42)A_3-A_4-(15/14)A_5-A_6.       (F)

If `delta_t=p^tD_t`, the Bell reconstruction gives

    A_(6-j)=a[6,b] Y_j(delta_1,...,delta_j)/j!,  0<=j<=5.

Consequently (F) is the single fixed Bell row

    Y_5/5! - Y_4/4! - (59/42)Y_3/3!
      - Y_2/2! - (15/14)Y_1 - 1.                       (BELL-5)

This identity is asserted exactly by `H5_BELL_ROW` in the checker before any
valuation is taken.

## 2. Five-coefficient reflection jet

Use

    E_d(x)=prod_(h=1)^d(1+xp/h),
    log E_d(x)=sum_(q=1)^5 (-1)^(q+1)x^q p^q H_d^(q)/q mod p^6

in the fixed-block formula `(PHI-6)` from Session 4.  For the full block use

    H_(p-1)^(q) in p^2 Z_p  (q odd),
    H_(p-1)^(q) in p Z_p    (q even),

and the reversal identity obtained by expanding `(p-h)^(-q)`.  No full-block
harmonic is set to zero: its named quotient is retained until the reflected
pair is collected.

For reference, the finite algebra is as follows.  Substitute the logarithmic
series in `(PHI-6)`, substitute the resulting `delta_1,...,delta_5` in
`(BELL-5)`, exchange

    b <-> c,  H_b^(q) <-> H_c^(q),
    H_(r+b)^(q) <-> H_(r+c)^(q),  c-b <-> b-c,

and collect powers through `p^5`.  After multiplication by
`84 b!^7 c!^7`, the coefficients are polynomial identities in the independent
harmonic letters.  The full-block quotients cancel.  Restoring the small
Bell layer `beta[1,b]=beta[6,b]Y_5(D^(r)(b))/5!` gives

| local digit | base pair `{b,c}` | companion pair `{b,c}` |
|---:|---|---|
| `C_0` | `0` | `0` |
| `C_1` | `0` | `0` |
| `C_2` | `0` | `0` |
| `C_3` | `0` | `0` |
| `C_4` | `-(beta[1,b]+beta[1,c])/84` | `-(betat[1,b]+betat[1,c])/84` |

Equivalently, in a form convenient for formalization,

    T(b)+T(c)
      = -(p^4/84)(beta[1,b]+beta[1,c]) mod p^5,          (RJ5)

and identically with tildes.  This is the promised weight-five reflection-jet
lemma.  It proves the local `p^4` floor rather than inferring it from samples.

The companion row is not a second guessed expansion.  Substitute the exact
identity

    At_i=b(m-b)A_i+p(2b-m)A_(i+1)-p^2A_(i+2)

in the already collected row.  Its surviving term is exactly the simple-pole
coefficient of `-k(k+r)R_r`, namely `betat[1,b]`.

## 3. Boundary branches

For the endpoint pair `{0,r}`, `c-b=r` is a `p`-unit.  The calculation above
is used without deleting `H_0^(q)=0`; hence (RJ5) includes the endpoint pair.

If `b=c`, no division by `c-b` is made.  In `(PHI-6)` retain
`m/2-b=p/2` and take the direct Taylor coefficient at that pole.  The central
Bell row has the same five coefficients with the singleton convention:

    (C_0,C_1,C_2,C_3,C_4)
      =(0,0,0,0,-beta[1,b]/84),

and similarly for the companion.  Thus the central zero supplies, rather than
cancels, the required local floor.

## 4. The finite-field summation certificate

Sum (RJ5) over the endpoint pair, all interior pairs, and the possible central
singleton.  The surviving digit is

    sum C_4 = -(1/84) sum_(b=0)^r beta[1,b].             (NF-base)

But `R_r(k)=O(k^(-4r-5))`.  Its coefficient of `k^(-1)` at infinity is
exactly `sum_b beta[1,b]`, so the first infinity relation is

    E_1(beta)=sum_b beta[1,b]=0                         (over Q).

For the companion, `-k(k+r)R_r(k)=O(k^(-4r-3))`; the identical coefficient
argument gives `E_1(betat)=0`.  Since `p>=11` makes `84` a unit, (NF-base) and
its companion prove `(H-NF)`.

Session 5 already proved that the middle correction belongs to `p^5 Z_p` and
that the reflected decomposition is exact.  Combining that result with
`(RJ5)` and `E_1=0` gives

    E, Et in p^5 Z_p.

Therefore `(H)` is proved for all three midpoint offsets.

## 5. Required exact gates

Before the coefficient table was accepted, `sol_h5.py` checked at
`p=11,13,17`, every offset, every local pair, both arrays, that

    v_p(T_pair + (p^4/84) beta_1_pair) >= 5.

The arrays are independently imported from `sol_j12.exact_arrays` and compared
exactly with `sol_h5`'s assembly.  Thus the gate crosses both Session 5 oracles.
It separately prints the endpoint digit and every central singleton.  The
observed `C_4` lists agree term by term with `-beta_1/84`, and exact `E,Et`
have valuation at least five.  Diagnostic primes through `43` also pass; they
are regression evidence only, not part of the proof.

Verification status: `(RJ5)`, `(H-NF)`, and `(H)` are proved by the displayed
finite Phi/Bell algebra and the exact infinity relation.  The prime gates are
independent transcription checks.
