# Is the factor 2 in Krattenthaler–Rivoal (17.1) actually needed?

**Question.** Zudilin's asymmetric derived series `Z_n` produces a ℚ-linear form in
`1, ζ(5), ζ(7), ζ(9), ζ(11)`. Krattenthaler–Rivoal (arXiv:math/0311114, §17.1) prove a
denominator bound and conjecture a sharpening, **both carrying a leading factor 2**:

- **Proven (KR §17.1):**  `2·d_{35n}³·d_{34n}·d_{33n}⁸·z_{j,n} ∈ ℤ`
- **Conjectured, eq. (17.1):**  `2·d_{35n}³·d_{34n}·d_{33n}⁷·z_{j,n} ∈ ℤ`  (gain one factor `d_{33n}`)

Unlike ζ(3) and ζ(4) — where the analogous factor 2 is provably/empirically *removable* —
KR **retain** the 2 even in the conjecture. This file resolves, by exact computation for
small `n`, whether the 2 is genuinely needed. **Verdict: it is not.**

`d_N = lcm(1,…,N)`.

## Source formula — [READ] verbatim LaTeX of arXiv:math/0311114 (e-print source `kratriv.tex`, §17.1)

```
Z_n = prod_{u=1}^{10} ((13+2u)n)! / (27n)!^6
      * sum_{k=1}^inf  (1/2) d^2/dk^2 [ (k + 37n/2)
            * (k-27n)_{27n}^3 (k+37n+1)_{27n}^3
            / prod_{u=1}^{10} (k+(12-u)n)_{(13+2u)n+1} ]
Z_n = z_{0,n} + sum_{j=1}^{4} z_{j,n} zeta(2j+3)
```

The half-integer shift is `37n/2` — the suspected home of the 2 (each pole sits at an
integer `k=-j`, so evaluating `(k+37n/2)` at the pole gives the half-integer `(37n−2j)/2`).

## Method — [COMPUTED] `zn_check.py` (exact rational arithmetic; no floats, no symbolic
differentiation, no polynomial factoring)

The summand `S0(k)` is a rational function whose only poles are at `k=-j` (integer `j`)
where the denominator Pochhammers vanish; the numerator never vanishes there (checked:
`(k−27n)_{27n}` has zeros at `k=1..27n`, `(k+37n+1)_{27n}` at `k=−37n−1..−64n`, neither
in the pole range `j∈[2n,35n]`). At each pole the principal part is
`S0 = Σ_m a_{j,m}(k+j)^{-m}`, so `(1/2)∂² S0` contributes
`a_{j,m}·m(m+1)/2·(k+j)^{-(m+2)}`, and `Σ_{k≥1}(k+j)^{-s} = ζ(s) − H_j^{(s)}`. The
`a_{j,m}` are Taylor coefficients of `(k+j)^{r_j}S0` at `k=-j`, obtained as a truncated
power series (product of linear factors) in `fractions.Fraction`.

**Engine validation.**
- **[COMPUTED] Self-test.** The *same* engine, run on the KR very-well-poised ζ(4) series
  `S_{n,4,2,1,1}(1) = u_n ζ(4) − v_n` (operator `∂¹`, half-shift `n/2`), reproduces the
  values I obtained **independently with sympy** earlier: `u₁=36, v₁=39; u₂=−2412,
  v₂=−41769/16; u₃=266040, v₃=62195315/216; u₄=−37159020, v₄=−92662434865/2304` — exact
  match, no spurious zeta values. (`run_selftest()` in the script; prints `PASSED`.)
- **[COMPUTED] Parity check.** For `Z_n` the engine returns **zero** coefficient for
  `ζ(3),ζ(4),ζ(6),ζ(8),ζ(10),ζ(12)` and **nonzero** only for `ζ(5),ζ(7),ζ(9),ζ(11)`,
  for every `n=1..5`. This is exactly the very-well-poised parity cancellation and is a
  strong independent correctness signal (a transcription/engine bug would break it).
- **[COMPUTED] Proven-bound check.** The KR proven bound
  `2·d_{35n}³·d_{34n}·d_{33n}⁸·z_{j,n} ∈ ℤ` holds for all five coefficients, all `n=1..5`.
  Since my `z_{j,n}` satisfy KR's own proven statement *and* the exact parity structure,
  they are KR's `z_{j,n}` (same construction) — so the factor-2 test below is a statement
  about their exact objects.
- A naive independent cross-check by numerically summing `½S0''` via `mpmath.diff` was
  **[discarded]**: numerical 2nd-differentiation of a function with astronomical dynamic
  range (terms `~10^{97}` for `n=1`) is unreliable and disagreed at low precision; the
  sympy self-test above is the trustworthy validation.

## Results — [COMPUTED], n = 1..5

For **every** `n∈{1,2,3,4,5}` and **every** coefficient `z_{0,n}, z_{5}, z_{7}, z_{9},
z_{11}`:

| test | holds? |
|---|---|
| proven `2·d₃₅ⁿ³·d₃₄ⁿ·d₃₃ⁿ⁸·z ∈ ℤ` | ✅ yes (as KR prove) |
| **factor 2 removed** `d₃₅ⁿ³·d₃₄ⁿ·d₃₃ⁿ⁸·z ∈ ℤ` | ✅ **yes — the 2 is NOT needed** |
| conj (17.1) `2·d₃₅ⁿ³·d₃₄ⁿ·d₃₃ⁿ⁷·z ∈ ℤ` | ✅ yes |
| conj (17.1) with 2 removed `d₃₅ⁿ³·d₃₄ⁿ·d₃₃ⁿ⁷·z ∈ ℤ` | ✅ yes |

**Per-prime 2-adic ledger** (`v₂` = 2-adic valuation). The multiplier without the 2,
`d₃₅ⁿ³·d₃₄ⁿ·d₃₃ⁿ⁸`, has `v₂ = 12·v₂(d_{35n})`. The 2 is unneeded with a *large* margin:

```
n=1:  v2(mult, no 2)=60.   v2(den z): z0=31, z5=3,  z7=0, z9=0, z11=0.   min slack = 60-31 = 29
n=2:  v2(mult, no 2)=72.   v2(den z): z0=42, z5=9,  z7=1, z9=0, z11=0.   min slack = 72-42 = 30
```

The residual factor 2 that KR carry is thus ~29–30 powers of 2 short of being needed —
it is bulk proof slack, not a marginal miss.

Full prime factorizations of `den(z_{j,n})` (the "slack ledger"):
```
n=1  z0 : 2^31·3^22·5^15·7^4·11^8·13^8·17^5·19^10·23^8·29^3·31^3
     z5 : 2^3·3^6·5^5·11^3·13^3·19^3·23^3
     z7 : 11·13·19^3·23
     z9 : 19
     z11: 1
n=2  z0 : 2^42·3^22·5^12·7^12·11^5·13^8·17^8·19^4·23^7·29^3·31^4·37^9·41^9·43^9·47^8·53^7·59^3·61^2·67^3
     z5 : 2^9·3^6·5^2·7·13^3·17^3·23^2·37^4·41^4·43^4·47^3·53
     z7 : 2·17·37^2·41^2·43^2·47
     z9 : 1
     z11: 1
```
(Note the top coefficient `z_{11}` is an *integer* for every `n` tested; `z_9` is
`±1/(single prime)` or integer. These primes are large — near the top of the pole range —
consistent with the RV/Zudilin factorial-quotient "denominator = lcm-product minus
large-prime removal" picture; there is no small-prime anomaly.)

Caveat on `n=1`: for `n=1`, `d_{33n}=d_{34n}=d_{35n}` (no prime in `(31,35]`), so the
`d`-power *structure* is degenerate there; but the **factor-2 question is purely 2-adic**
and is answered cleanly at every `n`. At `n=2` the degeneracy is (partly) broken
(`d_{66} < d_{68}=d_{70}`, since 67 is prime) and the verdict is unchanged.

## Verdict and interpretation

**The leading factor 2 in KR (17.1) is not needed for n = 1..5** — indeed the sharpened
denominator `d₃₅ⁿ³·d₃₄ⁿ·d₃₃ⁿ⁷·z_{j,n} ∈ ℤ` holds *without* it. [COMPUTED]

This is the **new data point**, and it is a **cross-family control** for our audit
methodology. The factor 2 in the odd-zeta ζ(5..11) family behaves exactly as it does in
ζ(3) (`2dₙ³` slack; sharp `dₙ³aₙ∈ℤ`, verified n≤50) and ζ(4) (`2Φₙ⁻¹dₙ⁴` slack; sharp
`dₙ⁴vₙ∈ℤ`, verified n≤5): the leading 2 is a **term-wise 2-adic over-estimate born of the
very-well-poised half-integer shift** (here `37n/2`), which the full sum cancels. In all
three families the 2 sits on the shift, and in all three it evaporates with wide margin.

[INFERRED] The most likely reason KR *state* (17.1) with the 2 is that their machinery
proves everything only "à un facteur 2 près" uniformly (their Théorèmes 1–3), and for the
harder *asymmetric* series they did not resolve the denominator conjecture at all (they
flag the difficulty of arranging the multiple-sum summand "en briques élémentaires"); so
they transcribed the conjecture in the same factor-2-safe form rather than asserting the
sharper 2-free version. My computation gives concrete evidence that the 2-free version is
the truth for small `n`.

**Limits of this evidence.** [COMPUTED] only for `n=1..5` (exact). It is a numerical
demonstration that the 2 is unnecessary in this range, not a proof for all `n`; but the
2-adic slack (~30) is large and stable, so a genuine need for the 2 at larger `n` would be
very surprising. No structural (Bernoulli/von Staudt/K-theory) mechanism is involved —
the 2 is pure residue/shift bookkeeping.

## Files
- `zn_check.py` — the exact engine, self-test, and per-`n` report (`python3 zn_check.py 1 2 3 4 5`).
