# P₃ by denominator snap — the decisive 3-adic cell, resolved (conditionally)

2026-07-17, very late. Method: Fable (coordinator). Verification: **PASSED
2026-07-18** — see `ZETA7_P3_VERIFICATION.md`. All-positive series partial sums at
n=3 reach **99.75%** of the claim without ever exceeding it (extrapolate to 0.04%);
rigorous tail bound **I₃ ≤ 3.09e-9 < 1.49e-7** makes the grid choice unconditional
(given the den-grid hypothesis); filtration signs confirmed exactly (q₁=61, s₁=300
each doubly locked); the flagged n=2 "1.10e-9" quote resolved to the exact-chain
1.0531e-9. Exactness of I₃ itself remains contingent (ladder operator + den-grid).
**Read the conditionality section before quoting.**

## The result

    P₃ = 23478462179525 / 69984,   den(P₃) = 69984 = 2⁵·3⁷

Hence **den(P₃) | d₃⁷ = 2⁷·3⁷: the naive inclusion d₃⁷P₃ ∈ ℤ HOLDS at n=3.**
ord₃ = 7 (tight), ord₂ = 5 (slack 2). No 12-type correction factor appears in
the ζ(7) primitive ladder at the first 3-adic opportunity — the weight-7 family
continues to show NO growing Betti excess (matches n≤2 scout verdict and the
descended-ladder n=3 finding den(P̂₃) = 2²·3⁵).

Numerator factors: 5² · 60427 · 15541703 (no small structure).

## The method (no integral computed)

1. **Filtration identity** I_n = I′_n + ζ(2)·I″_n, validated numerically on
   BZ's printed anchors: I₀ = 3.55544884725, I₁ = 3.20706023452e-5,
   I₂ = 1.05312589331e-9 (all positive, matching the all-positive-series
   values; NOTE the campaign note quoted "1.10e-9" for I₂ — the exact-chain
   value is 1.0531e-9; the note's figure was a loose quote, discrepancy ~5%,
   flagged for the verification agent).
2. Tonight's exact s₃ = 1396906795/3, P̂₃ = 232175579999/972 give I″₃ to
   arbitrary precision, so P₃_approx := (75/4)q₃ζ₇ − 3s₃ζ₅ + ζ₂I″₃ = P₃ + I₃
   with 0 < I₃ < I₂ ≈ 1.05e-9 — far inside the snap half-window
   1/(2·12·d₃⁷) = 1.49e-7.
3. **Snap** to the grid (1/3359232)ℤ: lands 5.63e-14 from a grid point
   (chance alignment ≈ 2e-7).

## Certification status (UPGRADED after Sol's review, 2026-07-18 ~00:45)

**Conditional-rigor lemma (Sol).** The grid spacing is h = 1/(12·6⁷) = 2.977e-7.
The integral representation gives 0 < I₃ < I₂ = 1.0531e-9 < h/2 RIGOROUSLY
(positivity: all-positive series; monotonicity: the n+1 integrand is the n
integrand times a factor < 1 on the open domain). Hence, GIVEN the two
hypotheses (i) den(P₃) | 12d₃⁷ and (ii) the ladder identification (s₃, P̂₃
exact), the snapped value is EXACTLY P₃ — no numerical precision enters the
argument at all. The 5.6e-14 proximity below is consistency evidence for
hypothesis (i), not the certificate.

Independent reproduction: Sol (GPT-5.6) reproduced all numerics to 80 digits.

## Self-certification (three independent locks)

- Residual sign: P₃_approx − P₃ = +I₃ = 5.6299224184893e-14 > 0 as the
  all-positive series REQUIRES (stable at 120 digits).
- Magnitude: I₃/I₂ = 5.35e-5, continuing the ratio sequence 9.0e-6, 3.28e-5 —
  monotone toward the char-poly root 1.58e-4 (sector A), as Poincaré-duality
  pairing predicts for the full form.
- Grid coincidence odds ~2e-7 under a wrong-denominator hypothesis.

## Immediate corollaries

- **I′₃ = 3.56748…e-5 (= ζ₂|I″₃| + I₃)**; ratio I′₃/I′₂ = 0.030641 — equal to
  the I″ ratio. The filtration (I ≈ 0) LOCKS I′ ≈ −ζ₂I″: **both projections
  ride sector B (0.0939)**. The symmetric family CANNOT beat the e⁻⁷ threshold;
  the sector-split conjecture (primitive = sector A) is FALSIFIED for the
  projections — sector A is ridden by the full 5-word form only.
- Archimedean elimination cost measured: ζ₂-elimination costs decay factor
  ≈ 594 (0.0939/1.58e-4) — the archimedean mirror of the Betti lattice cost.
- Remaining Diophantine route for weight 7 (Sol's): asymmetric/RV-group
  denominator reduction — need effective κ < −log(0.0939) = 2.365 vs the
  symmetric κ = 7.

## Conditionality (what this result depends on)

1. s₃, P̂₃ exact ⟸ the descent ladder (q,s,P̂) satisfies the discovered
   order-4 operator (74-term certified, motivic order match; NOT yet a theorem
   — CT certificate would close it).
2. den(P₃) | 12·d₃⁷ (snap-grid hypothesis; certified only statistically by the
   5.6e-14 coincidence + sign + magnitude locks).
3. BZ's printed anchors and ladder structure (I′ = (75/4)qζ₇ − 3sζ₅ − P,
   I″ = −9qζ₅ + 2sζ₃ − P̂, I = I′ + ζ₂I″ — the last validated numerically at
   n = 0,1,2 to 6 digits).

Pending independent test: all-positive 4-fold series partial sums at n=3 are
rigorous LOWER bounds for I₃ and must (a) never exceed 5.6299224184893e-14,
(b) climb toward it. Either failure refutes the snap; passage certifies it.
