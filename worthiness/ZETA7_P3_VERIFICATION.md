# P₃ / I₃ snap — independent verification via the all-positive 4-fold series

2026-07-18. Verifier: Fable (series lower-bound + rigorous-tail agent).
Tests the SNAP claim (`ZETA7_P3_SNAP.md`): **I₃ = 5.6299224184893e-14**.

Tooling (all in `worthiness/`):
- `zeta7_p3_series.py` — exact-`Fraction` cumulative partial sums S_N over [0,N]⁴.
- `zeta7_p3_series_fast.py` — float64/numpy acceleration (G2/H2 precomputed
  *exactly* then cast, so the internal alternating sums carry no cancellation;
  the outer 4-fold sum is all-positive → float64-safe). Validated to 15 digits
  against the exact version at n=2 (N≤28) and n=3 (N=10).
- `zeta7_p3_upperbound.py` — the rigorous majorant / upper bound.

The series itself is the DERIVED+VERIFIED representation from
`ZETA7_BARNES.md` §5f (`zeta7_barnes_num1.py`), all terms positive:

    I_n = Σ_{a,b,c,d≥0} C(n+a,a)C(n+b,b)C(n+c,c)C(n+d,d)·G2(a+b)·H2(b+c,d)
          · B(n+a+b+1,n+1)·B(2n+2+a+b+c+d,n+1)·B(n+b+c+d+1,n+1),
    G2(p)=∬(1−y₁y₂)^p[y₁(1−y₁)y₂(1−y₂)]^n,   H2(q,r)=∬(1−yw)^q y^n(1−y)^n w^n(1−w)^{n+r}.

Because every summand is a **positive** rational, any partial sum S_N over a box
[0,N]⁴ is a **rigorous lower bound** for I_n, and S_N ↑ I_n monotonically.

---

## 1. Revalidation at n=0,1,2 and the flagged "5%" discrepancy  [PASS]

Reproduced `zeta7_barnes_num1.py`: at n=0, n=1 the partial sums climb toward the
exact BZ anchors I₀=3.55544884725, I₁=3.2070602345e-5 (rem shrinks monotonically).

**n=2 — the flagged discrepancy resolved.** Campaign notes quoted I₂ ≈ "1.10e-9";
the exact filtration chain gives I₂ = 1.05312589331e-9. The series settles this:

| N   | S_N (lower bound)     |
|-----|-----------------------|
| 40  | 9.83947e-10           |
| 80  | 1.032513e-09          |
| 120 | 1.043678e-09          |
| 160 | 1.047839e-09  (99.5% of 1.0531e-9) |

Power-law tail extrapolation (S_N = S_∞ − A·N^{−α}, α≈1.83 from N=80,120,160):
**S_∞ = 1.05386e-9**, i.e. **0.07 % from the exact-chain 1.05312589331e-9** and
**4.4 % from the loose "1.10e-9"**. Verdict: **the exact chain (1.0531e-9) is
correct; "1.10e-9" was a loose quote.** The partial sums never approach 1.10e-9.
(Rigorous, up to float rounding: I₂ ≥ 1.047839e-9.)

---

## 2. The decisive test at n=3  [PASS — both criteria]

Exact-`Fraction` lower bounds (`zeta7_p3_series.py`): S_10 = 2.967983163809e-14,
S_22 = 4.6242e-14 — a fully rigorous **I₃ ≥ 4.6242e-14** (exact rational, 154-digit
numerator). Float acceleration (15-digit-validated) pushes further:

| N   | S_N (lower bound)     | S_N / claim |
|-----|-----------------------|-------------|
| 10  | 2.967983e-14          | 52.7 %      |
| 40  | 5.276949e-14          | 93.7 %      |
| 80  | 5.550453e-14          | 98.6 %      |
| 120 | 5.600252e-14          | 99.47 %     |
| 160 | **5.615790e-14**      | **99.75 %** |

- **(a) Never exceeds.** max S_N = 5.61579e-14 < 5.6299224184893e-14. ✔
  (An all-positive partial sum exceeding the claim would have refuted the snap;
  it does not.)
- **(b) Climbs toward it.** Monotone, reaching **99.75 %** of the claimed value at
  N=160 (the ">90% is decisive" bar). Same power-law extrapolation (α≈2.32):
  **S_∞ = 5.6322e-14**, i.e. **0.04 % from the claimed 5.6299224184893e-14**.

**Rigorous sandwich:  5.6158e-14 ≤ I₃ ≤ 3.09e-9  (Task 3), claim 5.6299e-14 inside;
numerics pin I₃ ≈ 5.632e-14.**

---

## 3. Rigorous tail / upper bound  [PASS — I₃ < 1.49e-7]

`zeta7_p3_upperbound.py` majorizes the whole (positive) series by a **fully
separable** bound M(a,b,c,d) = C₀·f_a(a)f_b(b)f_c(c)f_d(d) ≥ T(a,b,c,d), so

    I₃ = Σ T  ≤  C₀ · (Σ_a f_a)(Σ_b f_b)(Σ_c f_c)(Σ_d f_d).

Every factor bound is a **proved** inequality (so M ≥ T is a theorem, not a fit; a
1696-point exact/high-precision check found 0 violations, min ratio 137):

- **G2** (moment in t=1−y₁y₂, hence log-convex): G2(a+b) ≤ √(G2(2a)·G2(2b))
  (Cauchy–Schwarz). G2(2a) used *exactly* for a≤150; for the tail
  G2(p) ≤ (C_p/4)[1+ln(1/(140 C_p))], C_p = 6/[(p+1)(p+2)(p+3)(p+4)]
  (from g(y₂)=∫y₁³(1−y₁)³(1−y₁y₂)^p ≤ min(1/140, C_p/y₂⁴), split at the crossover).
- **H2** decreasing in q ⇒ H2(b+c,d) ≤ H2(0,d) = B(4,4)·B(4,d+4)
  = (1/140)·6/[(d+4)(d+5)(d+6)(d+7)].
- **B(a+b+4,4)** ≤ 6/(a+b+4)⁴ ≤ 6/[(a+4)²(b+4)²]  ((a+b+4)²≥(a+4)(b+4)).
- **B(a+b+c+d+8,4)** ≤ 6/(σ+8)⁴ ≤ 6/[256(a+2)(b+2)(c+2)(d+2)]  (AM–GM).
- **B(b+c+d+4,4)** ≤ 6/(u+4)⁴ ≤ 6/(c+2)⁴   (u+4 ≥ c+2).

Each 1-D sum Σf_x is computed to X₀=10⁵ with a rigorous decreasing-envelope tail
(f_x·x^{1.5} ↓ 0 ⇒ tail ≤ 2X₀·f_x(X₀)). Result:

    RIGOROUS UPPER BOUND:   I₃  ≤  3.0903e-9.

Since **3.09e-9 < 1.49e-7** (the snap half-window 1/(2·12·d₃⁷)), the snap's grid
choice is **unconditional given the denominator-grid hypothesis** — the target
deliverable of Task 3. (The bound is ~55000× the claimed value, so it does *not*
by itself prove I₃ = 5.63e-14; it removes the "value could be outside the window"
loophole. A sub-1e-12 bound was not reached — the corner singularities cost ~4
orders in the majorization.)

---

## 4. Filtration identity vs BZ's zeta-word decomposition  [PASS — no sign error]

Confirmed I_n = I′_n + ζ(2)·I″_n with **exactly**

    I′_n = (75/4)q_n ζ7 − 3 s_n ζ5 − P_n,     I″_n = −9 q_n ζ5 + 2 s_n ζ3 − P̂_n.

The validated code anchor `anchors[1]` in `zeta7_barnes_num1.py` is
`61·(75/4)ζ7 − 900ζ5 − 220 − ζ2·(549ζ5 − 600ζ3 + 152)`. Matching term-by-term:

| coeff        | code value | ⇒ requires |
|--------------|-----------|-----------|
| ζ7 (ζ2-free) | 61·(75/4) | q₁ = 61 |
| ζ5 (ζ2-free) | −900      | s₁ = 300 |
| 1  (ζ2-free) | −220      | P₁ = 220 |
| ζ2·ζ5        | −549      | q₁ = 61  ✔ (−9·61) |
| ζ2·ζ3        | +600      | s₁ = 300 ✔ (2·300) |
| ζ2·1         | −152      | P̂₁ = 152 |

**q₁=61 is forced twice (ζ7 and ζ2ζ5) and s₁=300 twice (ζ5 and ζ2ζ3), consistently.**
The rebuilt I₁ matches the code anchor to 30 digits. n=0 is the degenerate case
(q₀=1, s₀=P₀=P̂₀=0 ⇒ I₀=(75/4)ζ7−9ζ5ζ2). **No sign/normalization mismatch** — the
snap's structural assumption (conditionality item 3) holds; it does not die on a
factor error. (Sidelight consistent with the snap: I′₁=6.451e-5 and ζ2·I″₁=−6.447e-5
nearly cancel, the "I≈0 locks I′≈−ζ2·I″" phenomenon.)

---

## Summary — what is rigorous vs numerical

| Claim | Status |
|-------|--------|
| I₃ ≥ 4.6242e-14 (exact) ; ≥ 5.6158e-14 (float, 15-digit-validated) | **rigorous** (lower bound) |
| I₃ ≤ 3.0903e-9  < 1.49e-7 half-window | **rigorous** (upper bound, proved majorant) |
| Snap grid choice unconditional given den-grid hypothesis | **rigorous** (from the two above) |
| Filtration signs/normalizations = BZ's (q₁, s₁ doubly locked) | **rigorous** (exact identity) |
| I₂ = 1.0531e-9 (not 1.10e-9) | **numerical** (extrap 0.07%); rigorous ≥1.0478e-9 |
| I₃ = 5.6299224184893e-14 | **numerical** (partial sums 99.75%; extrap 0.04%). *Not* proved exactly — still rests on the snap + these self-consistent numerics. |

**Verdict: the snap PASSES every independent test run.** Partial sums never
exceed the claim and climb to 99.75 % of it; the value extrapolates to within
4e-4; the tail is rigorously < 1.49e-7; the filtration signs are exactly BZ's.
The residual conditionality is unchanged from the snap: exactness of I₃ itself
(hence P₃) is *not* established here — it remains contingent on the descent-ladder
operator and the denominator-grid hypothesis. What this verification removes is
every numerical/loophole way the snap could have been wrong.
