# PHASE2_SALVAGE_VERIFY — verification of the salvaged Sol claims (V1–V8)

Worker campaign 2026-07-20 (Opus). Verifies/executes the inventory in
`PHASE2_SOL_SALVAGE.md` §"Salvage verification campaign". All arithmetic is exact
(`fractions.Fraction`/`int`). **Honesty standard:** VERIFIED = exact finite check
over a stated grid (evidence, not a theorem); PROVEN cites a prior theorem;
CONFIRMED = a claimed exact identity reproduced exactly; CORRECTED = Sol's PDF
form was garbled and the exact form is restated.

Environment note: no `sage`/`ore_algebra` on this box (`which sage` fails), so the
V6 desingularization is done by directly testing — in exact arithmetic — the
p-adic consequences an apparent singularity must produce, not by an `ore_algebra`
symbolic run. This is spelled out honestly in V6c.

Scripts (all new, in `worthiness/`, exact arithmetic, usage line at top):
`salvage_data.py` (ground-truth q,p,p̃ + normalized Q,P,P̂, disk-cached to n=60),
`salvage_v123.py` (V1/V2/V3 grids), `salvage_v3_lucas_proof.py` (V3 carry-kill
certificate), `salvage_v6_recur.py` (order-3 recurrence exact-fit, both routes),
`salvage_v6_desing.py` (V5 Casoratian + V6c/d desingularization & induction),
`salvage_v7.py` (V7 master descent grid), `salvage_v8_barnes.py` (V8).

Definitions (task/`lemma_cb_explore.py`): `q=u w̃−ũ w`, `p=w̃ v−w ṽ`,
`p̃=u ṽ−ũ v`; normalized `Q=(−1)^{n+1}q/C(2n,n)`, `P=(−1)^{n+1}p/C(2n,n)`,
`P̂=(−1)^{n+1}p̃/C(2n,n)`; `d_n=lcm(1..n)`.

---

## Verdict table

| Item | Claim | Verdict |
|---|---|---|
| V1 | cross-product `(q,p,p̃)=(u,w,v)×(ũ,w̃,ṽ)` | **CONFIRMED** (exact signs below), n≤24 |
| V2 | Brown–Zudilin double-binomial `Q_n` | **CONFIRMED** exact, n≤24 |
| V3 | Lucas `Q_{ap+r}≡Q_a Q_r (mod p)` | **VERIFIED** grid + **certificate-shaped proof** reconstructed & verified (2.19M summands) |
| V4/V6a | common order-3 recurrence | **RECOVERED** two independent routes, cross-checked with Zudilin math/0206178 |
| V6b | normalized weight-(0,3,5) form (Sol §S2) | **CONFIRMED** exactly; the "`a₀(n+?)`" shift is `+1` |
| V5 | Casoratian (Sol §S3) | **CORRECTED** exact form; a₀ telescopes to ONE factor |
| V6c | (2n+5), a₀ apparent? (Sol §S7) | **NUANCED**: apparent for P,Q; TRUE singularities operator-wide (P̂ leaks) |
| V6d | d_n⁵-induction / p≥5 law | closes for P **empirically** (0 viol.); NOT free of the hard content |
| V7 | master descent (D) (Sol §S1) | **VERIFIED**, 0 violations / 332 descents, mostly tight |
| V8 | order-2 Barnes kernel (Sol §S8) | see §V8 |

---

## V1 — cross-product identity  (CONFIRMED)

With `a=(u,w,v)`, `b=(ũ,w̃,ṽ)` and the standard cross product
`a×b=(w ṽ−v w̃, v ũ−u ṽ, u w̃−w ũ)`, the exact componentwise relation is

>   **q = +(a×b)₃,   p = −(a×b)₁,   p̃ = −(a×b)₂**   (HOLDS exactly, n=1..24)

i.e. `(q,p,p̃)` is the cross product read in the cyclic order (3,1,2) with a sign
`(+,−,−)`. This is exactly the "2×2 minors of the 2×3 Zudilin period matrix"
statement of §S5, with the sign convention pinned.

## V2 — double-binomial formula  (CONFIRMED)

`Q_n = Σ_{k,l=0}^n C(n+k,n)C(n,k)² C(n+l,n)C(n,l)² C(n+k+l,n)` equals the
normalized `Q_n=(−1)^{n+1}q_n/C(2n,n)` exactly for every n=0..24 (integers:
1, 21, 2989, 714549, 217515501, …). The formula is manifestly a sum of positive
integers, so `Q_n∈ℤ` — the (FREE) integrality of `q_n` up to `±C(2n,n)`.

## V3 — Lucas–Frobenius congruence + proof  (VERIFIED + reconstructed)

**Grid (`salvage_v123.py`).** `Q_{ap+r}≡Q_a Q_r (mod p)` holds with **0 failures**
over 1592 checks: single-digit (a≤12 and a=p, all r<p) and iterated 3-digit
(`n=a₂p²+a₁p+a₀`, `Q_n≡Q_{a₂}Q_{a₁}Q_{a₀}`) for p∈{5,7,11,13}.

**Reconstructed proof (`salvage_v3_lucas_proof.py`), certificate-shaped.**
Split every index in base p: `k=bp+s`, `l=cp+t` (0≤s,t<p), `N=ap+r`. Two lemmas,
both verified exactly mod p over 2 191 413 summands (p∈{5,7,11,13,17}, a≤8, all
r<p), **0 exceptions**:

- **(CARRY-KILL)** the summand `T(k,l)=C(N+k,N)C(N,k)²C(N+l,N)C(N,l)²C(N+k+l,N)`
  satisfies `T≡0 (mod p)` **unless all of** `b≤a, c≤a, s≤r, t≤r, r+s<p, r+t<p,
  r+s+t<p`. Any base-p carry pushes a units digit of one argument below the
  corresponding digit of `N` (`s≤r` fails, or `r+s≥p` makes the low digit of
  `N+k` equal `r+s−p<r`, etc.), killing a Lucas factor `C(·,r)=0`.
- **(FACTOR)** on the surviving box the summand splits:
  `T(bp+s,cp+t) ≡ T_hi(b,c;a)·T_lo(s,t;r) (mod p)`, where
  `T_hi=C(a+b,a)C(a,b)²C(a+c,a)C(a,c)²C(a+b+c,a)` is the `(b,c)`-summand of `Q_a`
  and `T_lo` the `(s,t)`-summand of `Q_r`.

Summation over the box then gives `Q_N ≡ (Σ T_hi)(Σ T_lo) = Q_a·Q_r`, since the
surviving high box is exactly `{0≤b,c≤a}` (= support of `Q_a` mod p) and the low
box is the mod-p support of `Q_r`. **Status:** the digit-factorization and box
summation are complete; the CARRY-KILL predicate is the only step that (for a
fully human proof) needs the general base-p carry lemma — here it is verified
exhaustively on the stated grid with zero exceptions, exactly the style in which
Lucas-for-diagonals results (Malik–Straub, McCarthy–Osburn–Straub) are
established. This is the "first row of the Frobenius matrix," rigorous modulo that
one standard lemma. **No gap of substance found; the mechanism is exactly Sol's.**

## V4 / V6a — the common third-order recurrence  (RECOVERED, cross-checked)

Two independent routes agree.

**Route (ii), exact-fit (`salvage_v6_recur.py`).** Fitting `Σ_{i=0}^3 c_i(n)X_{n+i}=0`
with polynomial `c_i` of degree ≤ D to ALL THREE sequences simultaneously
(large-prime nullspace + CRT rational reconstruction, then exact re-verification):
minimal **D = 9**, nullspace **dim 1**, annihilates all three ladders at every
offset with 0 failures (123 exact checks each for raw and normalized). Raw
`(q,p,p̃)` (relating `X_n,X_{n+1},X_{n+2},X_{n+3}`):

```
c0 = −4 (n+1)^4 (2n+1)(2n+3) · a₀(n+1)
c1 = −4 (2n+3)(3874492 n^8 + 59373972 n^7 + 394148190 n^6 + 1481084196 n^5
        + 3447878810 n^4 + 5095855458 n^3 + 4673546679 n^2 + 2433871008 n + 551502039)
c2 =  2 (48802112 n^9 + 967468896 n^8 + 8488000862 n^7 + 43246197636 n^6
        + 140983768422 n^5 + 304912330849 n^4 + 437406946975 n^3
        + 401272692378 n^2 + 213593890911 n + 50257929339)
c3 =  (n+3)^6 · a₀(n)
    a₀(n) = 41218 n^3 + 198849 n^2 + 320790 n + 173057   (irreducible over ℚ;
            41218=2·37·557, 173057=61·2837; disc = −178513008142644),
    a₀(n+1) = 41218 n^3 + 322503 n^2 + 842142 n + 733914.
```

**Route (i), Zudilin arXiv:math/0206178.** Printed recurrence (his eq. 1):
`(n+1)^6 a₀(n) q_{n+1} + a₁(n) q_n − 4(2n−1)a₂(n) q_{n−1}
  − 4(n−1)^4(2n−1)(2n−3) a₀(n+1) q_{n−2} = 0`, with `a₀` a cubic and the three
independent solutions `{q_n},{p_n},{p̃_n}` being the ζ(5) denominator/numerator/
companion. Recentering my raw fit `n→n−2` reproduces Zudilin's shape **exactly**:
leading `(n+1)^6 a₀(n)`, trailing `−4(n−1)^4(2n−1)(2n−3) a₀(n+1)`. The two routes
cross-check; the sixth power `(n+1)^6` and the single cubic `a₀` (appearing as
`a₀(n)` leading and `a₀(n+1)` trailing) are confirmed.

## V6b — normalized weight-(0,3,5) recurrence (Sol §S2)  (CONFIRMED)

Substituting `x_n=(−1)^{n+1}C(2n,n)Y_n` (`C(2n+2,n+1)/C(2n,n)=2(2n+1)/(n+1)` drops
one power of `(n+1)`) gives the normalized recurrence for every
`Y∈{Q,P,P̂}` (`salvage_v6_recur.py`, 0 failures):

```
c0(n) Y_n + c1(n) Y_{n+1} + c2(n) Y_{n+2} + c3(n) Y_{n+3} = 0,
   c0(n) = (n+1)^5 (n+2) · a₀(n+1)
   c1(n) = −2 (n+2) · [ deg-8 poly above ]
   c2(n) = −2 · [ deg-9 poly above ]
   c3(n) = 2 (n+3)^5 (2n+5) · a₀(n)         ← LEADING coefficient
```

Recentering to Sol's `Y_{n+1}` form, the coefficient of `Y_{n+1}` is
`2(n+1)^5(2n+1)·a₀(n−2)` and of `Y_{n−2}` is `n(n−1)^5·a₀(n−1)` — **exactly Sol's
§S2 template** `2(n+1)^5(2n+1)a₀(n)·Y_{n+1} − … + n(n−1)^5 a₀(n+?)·Y_{n−2}`, and
the garbled "**`a₀(n+?)`**" is resolved: the two cubics are the SAME `a₀` shifted
by **+1** (`a₀(n+1)` is literally `c0`'s cubic). The fifth powers `(n+1)^5`,
`(n−1)^5` are intrinsic; the loss of exactly five p-adic orders per digit is built
into the normalization, as claimed. Integer content of `(c0,c1,c2,c3)` is
`(1,2,2,2)` — the coefficients are integer polynomials with only the prime 2 as
content, so for **p≥5 every `c_i(m)∈ℤ_p`** and the only p-content of the leading
coefficient beyond `(n+3)^5` is the factor `(2n+5)·a₀(n)`.

## V5 — the Casoratian (Sol §S3)  (CORRECTED exact form)

For the fundamental matrix of `(Q,P,P̂)` with rows at `(n,n+1,n+2)` the Casoratian
telescopes (`C(n+1)/C(n) = (−1)^3 c0(n)/c3(n) = −c0/c3`, HOLDS exactly). The exact
closed form (VERIFIED n=1..24, `salvage_v6_desing.py`):

>   **det 𝒞_n = (−1)^{n−1} · a₀(n) / [ 16 · (n+1)^4 (n+2)^5 (2n+1)(2n+3) · C(2n,n) ]**

Sol's §S3 rendering `(−1)^n a₀(n)/(4(n−1)^5 n^6 C(2n,n))` was garbled (wrong
orientation/constant); the corrected constant is **1/16** and the denominator is
`(n+1)^4(n+2)^5(2n+1)(2n+3)C(2n,n)`. The structural claim survives and sharpens:
**a₀ appears LINEARLY** (it telescopes `∏a₀(k+1)/a₀(k)=a₀(n)/a₀(1)` to a single
factor) — Sol's "the troublesome cubic a₀ telescopes almost entirely." Note the
**midpoint factors `(2n+1)(2n+3)` sit in the DENOMINATOR**: the three solutions
become p-adically dependent at those primes, i.e. one solution must be singular
there — this is exactly what V6c finds (it is P̂).

## V6c — the desingularization test (Sol §S7)  — VERDICT: NUANCED, shortcut does NOT come for free

Leading coefficient `c3(n)=2(n+3)^5·(2n+5)·a₀(n)` = (fifth power)·(midpoint)·(cubic).
The test: are `(2n+5)` and `a₀` **apparent** singularities (removable, so the
effective leading coefficient is `~(n+3)^5` and an ordinary `d_n⁵`-induction
closes the p≥5 law with no Dwork theorem)?

Directly testing the p-adic consequence (`salvage_v6_desing.py`, exact, p∈
{5,7,11,13,17,19,23}, n≤45), the per-step holonomic bound with **only** the
`(n+3)^5` loss —
`v_p(Y_{n+3}) ≥ min(v_p Y_n, v_p Y_{n+1}, v_p Y_{n+2}) − 5·v_p(n+3)` — split by
danger source (`p|a₀(m)` vs `p|(2m+5)`):

| ladder | a₀-danger | midpoint-danger | non-danger |
|---|---|---|---|
| Q (wt 0) | 0/30 | 0/29 | 0/235 |
| **P (wt 5)** | **0/30** | **0/29** | **0/235** |
| P̂ (wt 3) | 1/30 | 6/29 | 0/235 |

(viol/total). **The finding:**

- For the **target P (and Q)**: 0 violations in *every* category, including at
  every point where `p | (2n+5)` or `p | a₀(n)`. So for the P-solution the extra
  factors behave as apparent: the induction loses exactly 5 orders per step.
- For **P̂**: it **leaks systematically**, and precisely at the primes `p=2m+5`
  (the midpoint), plus once at `p|a₀`. Because an *operator-level* apparent
  singularity is regular for **all** solutions, P̂ is a witness that **`(2n+5)`
  and `a₀` are TRUE (non-apparent) singularities of the operator.** The operator
  does **not** desingularize to leading `~(n+3)^5`.

So Sol's hope ("if it desingularizes, the leading coefficient becomes essentially
n⁵ and the entire p≥5 theorem follows by ordinary `d_n⁵`-induction — no Dwork
theorem at all") is **too strong**. The midpoint and cubic are genuine operator
singularities (P̂ leaks there); P merely has non-negative local exponent at them.
The `d_n⁵`-induction closes for P **only under the extra hypothesis that P
specifically is p-adically regular at `(2n+5)` and `a₀`** — equivalently that the
numerator combination `c0 P_n + c1 P_{n+1} + c2 P_{n+2}` is divisible by
`(2n+5)·a₀(n)` to the needed p-adic order at every p≥5. That solution-specific
regularity is exactly the hard content of the original descent (D); the
desingularization **relocates** it, it does not remove it.

## V6d — the d_n⁵-induction, honest assessment

With the P-specific apparentness of V6c as an (empirically airtight) input, the
induction **does** close on data:

- **T-BOUND (`salvage_v6_desing.py`):** `v_p(P_n) ≥ −5⌊log_p n⌋` holds with
  **0 violations / 308 checks**, and is **tight (263/308)** — the `d_n⁵` reserve
  pays exactly 5 orders per digit level. (For the weight-3 companion the analogous
  `v_p(P̂_n) ≥ −3⌊log_p n⌋` **FAILS**, 44/308, first at n=3, p=5: P̂'s denominator
  picks up the midpoint primes `p≈2n`, consistent with the V6c leak. P̂ is not the
  CB-law target, so this does not affect the P-theorem, but it does mean the
  weight-3 lattice statement of §S5 is not a naive `d_n³` denominator bound.)

**What remains for a THEOREM of the p≥5 law (via this route):**
1. **the crux** — prove `(2n+5)·a₀(n) | (c0 P_n + c1 P_{n+1} + c2 P_{n+2})` to the
   needed p-adic order for p≥5 (P-specific apparentness). This is a clean, finite-
   looking reformulation of (D) but is **not** supplied by generic desingularization
   (the operator does not desingularize — P̂ proves it), so it needs the actual
   Frobenius/Dwork structure of P. **Not closed.**
2. base cases `P_0,P_1,P_2` (finite, trivial: `P_0=0,P_1=87/4,P_2=1190161/384`);
3. the singular-n / terminal handling — supplied by Phase-1 (proven) exactly as in
   §S1 (see V7 assembly).

**Bottom line on the shortcut:** it is a genuine and useful reduction — it turns
the whole p≥5 law into a single divisibility of P's numerator by `(2n+5)a₀` — but
it does **not** make the theorem follow "for free from `d_n⁵`-induction with no
Dwork theorem." The operator-level desingularization Sol hoped for does not exist;
the hard, solution-specific arithmetic (essentially (D)) survives intact.

## V7 — the master descent (D) (Sol §S1)  (VERIFIED)

`(D): v_p(P_n) ≥ v_p(P_{⌊n/p⌋}) − 5` for p≥5 (`salvage_v7.py`, exact,
p∈{5,7,11,13,17,19,23}, all n≤60 with ⌊n/p⌋≥1): **332 descents, 0 violations.**
Slack distribution — overwhelmingly **tight**: p=5 all 56 tight (slack 0); p=13,17,
23 all tight; p=7 has 30 tight, 21 slack-1, 3 slack-2; p=11 45 tight, 5 slack-1.
The `d_n⁵` reserve pays exactly 5 per digit level, as §S1 predicts. The §S1
iteration assembly (descend `n→⌊n/p⌋→…→n_L<p`, terminal `P_{n_L}` p-integral)
reproduces `v_p(P_n) ≥ −5⌊log_p n⌋` with **0 failures** and 0 non-integral
terminals across p∈{5,7,11,13}. (D) is the correct single reduction and it holds
on the whole grid.

## V8 — the order-2 Barnes kernel (Sol §S8)

See `salvage_v8_barnes.py` and the note appended below.
