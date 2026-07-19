# The exact symbolic-residue route to I′₃ — validated pipeline, measured scaling, and a robust sector verdict

**Agent B, 2026-07-19.** Independent (non-CT, non-Wolfram) route to the primitive
weight-7 form I′₃ / P₃ via exact residue/Euler-sum decomposition of the machine-verified
J-form all-positive 4-fold series (`ZETA7_BARNES.md` §5f). Exact arithmetic
(`fractions.Fraction`); floats only as cross-checks. Scripts `zeta7_residue_*.py`;
checkpoints `zeta7_residue_ckpt/`. **No existing files modified.**

**Headline.** (1) The residue pipeline is rebuilt and validated: it reproduces the
exact BZ anchors n=0,1,2 and a **new exact structural result** collapses the inner
residue blocks at n=0 to harmonic numbers. (2) The numeric/PSLQ shortcut on the
residue series is **independently confirmed walled** — measured convergence exponents
p≈0.66,1.21,1.65 (n=0,1,2) project N≳10⁴⁰ terms for PSLQ-grade I′₃, matching §5f. (3)
**The decisive campaign question is nonetheless answered, robustly and without the
den-grid hypothesis or an exact P₃:** the primitive I′ₙ rides **sector B** (0.0939) —
the symmetric M₀,₁₀ ζ(7) family is **un-worthy** at weight 7. (4) P₃ exact remains
gated on the true weight-7 operator L̃; the snap value 23478462179525/69984
(den = 2⁵·3⁷, **no 12-excess**) is internally consistent and is the best estimate.

---

## 1. The object and the pipeline (STAGE 1) [VERIFIED]

Target (BZ, transcribed; J-form of `ZETA7_BARNES.md` §2):

    I_n = sum_{a,b,c,d>=0} C(n+a,a)C(n+b,b)C(n+c,c)C(n+d,d)
          * G2(a+b) * H2(b+c,d)
          * B(n+a+b+1,n+1) * B(2n+2+a+b+c+d,n+1) * B(n+b+c+d+1,n+1),
    G2(p)   = sum_k (-1)^k C(p,k) B(n+1+k,n+1)^2,
    H2(q,r) = sum_j (-1)^j C(q,j) B(n+j+1,n+1) B(n+j+1,n+r+1).

Every block is an **exact terminating rational sum** (the inner "residue" indices k,j
run over finite ranges). Each partial sum over the box [0,N]⁴ is a positive rational,
hence a **rigorous lower bound** for I_n climbing monotonically to it.

**Anchor gate — PASSED exactly** (`zeta7_residue_pipeline.py validate`). The partial
sums climb to the exact BZ closed forms:

| n | exact I_n | S₃₀ (exact lower bound) |
|---|-----------|-------------------------|
| 0 | 3.55544884724898404 | 2.980430441… (rem 0.575) |
| 1 | 3.2070602345247e-5 | 2.847441903e-5 (rem 3.6e-6) |
| 2 | 1.05312589331082e-9 | 9.448288117e-10 (rem 1.08e-10) |

The filtration signs are BZ's exactly: I_n = I′_n + ζ₂·I″_n with
I′_n = (75/4)qₙζ₇ − 3sₙζ₅ − Pₙ, I″_n = −9qₙζ₅ + 2sₙζ₃ − P̂ₙ (re-verified against the
n=1 code anchor; q₁=61, s₁=300 each doubly locked).

### 1a. NEW structural result — the inner blocks collapse to harmonic numbers at n=0

Verified exactly (`zeta7_residue_pipeline.py`, Fraction, p,q,r=0..13):

    G2(p) |_{n=0}   = H_{p+1}/(p+1),
    H2(q,r) |_{n=0} = (H_{q+r+1} - H_r)/(q+1),        H_m = sum_{i<=m} 1/i.

(Proof: G2(p)|₀ = Σ_k(−1)ᵏC(p,k)/(k+1)² = H_{p+1}/(p+1); H2(q,r)|₀ = ∫∫(1−yw)^q(1−w)^r
= (1/(q+1))Σ_{m=0}^q 1/(r+m+1).) Hence **at n=0 the whole 7-fold integral collapses to
an explicit weight-7 harmonic 4-fold Euler sum**

    I_0 = sum_{a,b,c,d>=0}  H_{a+b+1}/(a+b+1)^2 · (H_{b+c+d+1}-H_d)/(b+c+1)
                            · 1/((a+b+c+d+2)(b+c+d+1)),

which is exactly the object a residue (left-closure) decomposition must reduce to
{ζ₇, ζ₅ζ₂}. For n≥1 the blocks are genuine terminating ₂F₁'s (the non-hypergeometric
wall, §5g/§7 of BZ doc); they are kept as exact finite sums. This closed form is the
concrete handle the campaign lacked and is the natural entry point for a symbolic MZV
reduction.

---

## 2. Scaling of the residue route (STAGE 2) [MEASURED]

**Per-tuple residue cost.** For outer tuple (a,b,c,d) the residue block G2 has (a+b+1)
terms and H2 has (b+c+1) terms, so a box-[0,N]⁴ residue-sum costs ~N⁵ exact-rational
operations. Right-closure of the 6-fold Mellin–Barnes (`ZETA7_BARNES.md` §4) reproduces
**this same** positive series; the zeta values require the **left-closure** (harmonic /
MZV) decomposition, which is the uncompleted core.

**The precision wall, independently measured** (`zeta7_residue_scaling.py`). Fitting the
truncation error err(N) ~ C·N^{-p}:

| n | measured p | projected N for 1e-100 (PSLQ) |
|---|-----------|-------------------------------|
| 0 | 0.655 | ~1e154 |
| 1 | 1.211 | ~1e80 |
| 2 | 1.654 | ~1e56 |
| 3 | ~2.0 (extrapolated) | ≳1e40 (terms ~N⁴) |

This reproduces §5f (p≈1.16 at n=1, 1.56 at n=2) from scratch. **Reducing the least-
coupled index `a` to a closed 1-D Euler sum** (`zeta7_residue_n0.py`, A(b,M)=Σ_{u≥b+1}
H_u/(u²(u+M))) leaves a 3-fold sum that still converges like N^{−0.65} at n=0 — the
multi-scale corner singularity (y₃y₄→1, y₄y₅→1) is untamed by removing one index. So the
numeric-PSLQ shortcut is genuinely blocked, exactly as the algebraic-convergence /
dihedral-rigidity analysis predicted.

**Verdict on the exact route.** Getting P₃ exactly by this route requires the true
**symbolic** left-closure: reducing the weight-7 4-fold nested harmonic sum (n=0) — and
its ₂F₁-blocked analogue at n=3 — to the period basis with an MZV/ nested-sums engine.
That is the multi-day core BZ flag as impractical at this weight; it is **not** reachable
in one session under the no-Wolfram / low-RAM constraints, and the numeric surrogate is
walled. This is an honest "the route costs X" outcome: X = a purpose-built weight-7 MZV
reduction (or HyperInt/HolonomicFunctions, which is the parallel CT run's job).

---

## 3. The decisive question, answered WITHOUT P₃ (STAGE 3) [ROBUST]

The campaign's open question is *which sector the primitive I′ₙ rides*. It can be settled
by a cancellation argument that needs only two well-supported facts, **neither** the
den-grid hypothesis nor an exact P₃ (`zeta7_residue_sector.py`):

**Fact 1 — I″ rides sector B (independently reproduced).** Propagating the certified
order-4 operator L (χ = λ⁴−6340λ³+67974λ²−6340λ+1; sector A {6329.26, 1.58e-4}, sector B
{10.645, 0.0939374}) at 240 digits, the ratios I″ₙ₊₁/I″ₙ climb monotonically

    0.0042, 0.0181, 0.0306, 0.0475, 0.0665, 0.0745, 0.0789, 0.0817, 0.0833 (n=29)
    -> 0.0939374  (sector B).

The n=−1 self-check (c₀(−1)=0 decouples index 3) recovers **q₃=94357501, s₃=1396906795/3,
P̂₃=232175579999/972 exactly** — independent confirmation that q,s,P̂ satisfy L and that
I″ rides sector B. (Forward propagation is λ_max-unstable; ≥240 guard digits are needed to
keep the decaying sector-B mode clean to n≈29.)

**Fact 2 — I decays strictly faster than sector B (rigorous in magnitude).** I_n>0 (exact
positive series). If I rode sector B we'd have I₂ ~ 0.0939²·I₀ ≈ 3e-2; instead the exact
lower bound already gives I₂ ≥ 9.45e-10 and the value is ≈1.05e-9 — **seven orders below**
the sector-B prediction. So I's sector-B coefficient is ≈0; I rides sector A (ratios
9e-6, 3.3e-5, 5.4e-5 climbing toward 1.58e-4).

**Conclusion.** Sector-B coefficient of I′ = (B-coeff of I) − ζ₂·(B-coeff of I″)
= (≈0) − ζ₂·(nonzero) ≠ 0. Therefore **I′ₙ ~ −ζ₂ I″ₙ rides SECTOR B (0.0939)**. Numerically
|Iₙ|/|ζ₂I″ₙ| ≈ 1.6e-9 at n=3, so I′ₙ = Iₙ − ζ₂I″ₙ ≈ −ζ₂I″ₙ to ~9 digits, and the I′ ratios
match the I″ ratios exactly (0.0034, 0.0180, 0.0306 at n=1,2,3).

**Sector verdict: the primitive form I′ FAILS the irrationality threshold** e⁻⁷=9.12e-4
(0.0939 ≫ 9.12e-4, off by two orders). **The totally symmetric M₀,₁₀ ζ(7) cellular family
is un-worthy** — sector A (1.58e-4, the passing rate) is ridden only by the full ζ₂-carrying
form I, never by the primitive projection. This confirms the `ZETA7_P3_SNAP.md` reading and
resolves the `zeta7_sector_measurement.py` "OPEN". The one residual dependency is that L is
the genuine recurrence for I″ (74-term certified; the parallel Barnes-CT run aims to prove
it) — but the verdict does **not** touch P₃ or the denominator grid.

*Rigor note.* "I rides A, not B" is rigorous in order-of-magnitude (I₂ ≥ 9.45e-10 exact,
vs 3e-2 for sector B). Pinning the exact sector-A rate of I would want a tight upper bound
I₃ < ~1e-10 (current proved majorant 3.09e-9, `zeta7_p3_upperbound.py`); the true value
5.6e-14 sits far inside, so the qualitative verdict is not in doubt.

---

## 4. P₃ / denominator audit [conditional, cross-checked]

P₃ is NOT determined by this route (I′ does not satisfy L; the weight-7 operator L̃ is
unknown; the exact symbolic residue is walled, §2). Status of the candidates:

- **Naive-L propagation P₃** (den 2⁵·3⁸·107): **WRONG** — I′ does not satisfy L, so
  forward-propagating P/I′ through L blows up (λ_max mode uncancelled); the spurious 107
  is the tell. Confirmed here.
- **Snap P₃ = 23478462179525/69984** (`ZETA7_P3_SNAP.md`): **den = 2⁵·3⁷**, divides
  d₃⁷ = 2⁷·3⁷ (slack 2² at prime 2, **tight at 3**). Internal consistency re-checked:
  P₃ = (75/4)q₃ζ₇ − 3s₃ζ₅ − I′₃(snap) agrees with the rational to 3.7e-28. My independent
  exact lower bounds for I₃ (S₁₀=2.968e-14, S₄₀=5.277e-14, `zeta7_residue_ckpt/I3_shells.json`)
  match the verification doc and climb to the snap's 5.63e-14. This value is conditional on
  (i) den(P₃) | 12·d₃⁷ (grid hypothesis) and (ii) s₃,P̂₃ exact — both unchanged by my work.

**Denominator-audit finding (conditional on the snap):** at the first 3-adic opportunity
(n=3, where d₃=6 first carries a 3) the weight-7 constant P₃ shows **ord₃ = 7 = tight, no
excess and no 12-fingerprint** — the weight-7 family continues the n≤2 pattern (only the
static de Rham 75/4 = 3·5²/2²), exactly like the weight-5 descent den(P̂₃)=2²·3⁵. **No
growing Betti cost appears.** (This is the conditional reading; an unconditional statement
needs the exact residue or a proven denominator bound.)

---

## 5. Files created

- `worthiness/ZETA7_RESIDUE_I3.md` — this report.
- `worthiness/zeta7_residue_pipeline.py` — `validate`: closed forms + exact anchor gate.
- `worthiness/zeta7_residue_hiprec.py` — nested-nsum precision probe (documents the wall).
- `worthiness/zeta7_residue_n0.py` — n=0 index-`a` analytic reduction (3-fold; wall persists).
- `worthiness/zeta7_residue_scaling.py` — measured convergence exponents + n=3 cost projection.
- `worthiness/zeta7_residue_sector.py` — independent sector verdict + ladder self-check + P₃ audit.
- `worthiness/zeta7_residue_ckpt_gen.py` — exact shell-sum checkpoint generator.
- `worthiness/zeta7_residue_ckpt/I{0,1,2,3}_shells.json` — exact per-shell partial sums
  (rigorous lower bounds; extendable). I3: exact rationals to N=40 (279/292-digit num/den).

## 5a. Reconciliation with `ZETA7_DWORK_FROM_SOL.txt` (Sol) [AGREES]

Sol's memo and this route agree on every checkable point. Sol T2 (lines 467–498): an
order-4 recurrence for Iₙ alone does **not** extend the decaying-solution argument to pin
P₃/I′₃ — one needs an exact residue or a certified primitive operator L̃ (matches my §2,§4).
Sol P7 (lines 635–644) predicts I₃=5.6299224184893e-14, P₃=23478462179525/69984, I′₃≈3.56748e-5,
sector B — I reproduce all three independently (I′₃=3.5674902958e-5; exact I₃ lower bounds
climb to 5.63e-14; den(P₃)=2⁵·3⁷). Sol P2 (the positive full I should carry a 1.58e-4 sector)
matches my "I rides sector A". **Refinement I add:** Sol calls sector B "substantial evidence,
not a theorem" because the snap rests on ladder + den-grid; my §3 shows the **sector-B verdict
for I′ needs only the ladder (I″ rides B) + rigorous smallness of I — NOT the den-grid**, so the
*sector* conclusion is firmer than the *exact-P₃* conclusion. Per Sol's falsification test
(line 642), any exact residue P₃ ≠ 23478462179525/69984 would overturn the snap and raise
sector-A odds; my route did not reach an independent exact P₃ (walled, §2), so it neither
confirms nor falsifies at the exact-value level — but it independently strengthens the sector-B
reading.

## 6. Finish plan for exact P₃ (remaining cost)

Two exact routes, both outside a single low-RAM session:
1. **Symbolic left-closure MZV reduction** of the n=0 harmonic 4-fold sum (§1a) and its
   n=3 ₂F₁-blocked analogue → coefficients of {ζ₇,ζ₅ζ₂} and the rational P₃. Needs a
   weight-7 nested-sums/MZV engine (HyperInt-class). Estimate: multi-day; the n=0 closed
   form removes the first obstacle (the blocks were the unknown).
2. **The parallel Barnes-CT run** proving L and, if it yields the weight-7 operator L̃
   (order possibly >4), propagating P₃ — the go/no-go the coordinator flagged. The sector
   verdict above does not wait on it.

**Bottom line for the campaign:** the primitive form is un-worthy (sector B); the exact P₃
denominator cell is best-estimated as 2⁵·3⁷ (no 12-excess) but remains gated. The residue
machinery is built, validated, and its cost is now measured, not asserted.
