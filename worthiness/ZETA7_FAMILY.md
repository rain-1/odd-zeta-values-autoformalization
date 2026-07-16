# The ζ(7) cellular family on M₀,₁₀: extraction, period decomposition, and a denominator audit

**Scope.** Feasibility-first scouting of the Brown–Zudilin (BZ) ζ(7) cellular
family — the "vanishing in the middle" permutation (10,2,4,1,6,3,8,5,9,7) on
M₀,₁₀, totally symmetric version — to test whether the M₀,₈/ζ(5) denominator
mechanism (`CONJECTURE.md`, `PROOF_MECHANISM.md`) predicts the arithmetic of
its ζ(7)-form. Source: `.../bz/2026-01-26_CellZeta.tex`, lines ~1443–1467.
Scripts: `zeta7_audit.py` (exact ledger + numeric checks). No existing files
modified.

**Headline result (one line).** BZ already print the exact ζ(7)-form for
n = 0,1,2; auditing it against the natural dₙ⁷ law shows the predicted {2,3}
elimination cost does **not** transfer as the M₀,₈ "12 = 2²·3 excess in the
constant term" — at the matched n = 2 the M₀,₁₀ constant carries **no factor 3
at all**; the only {2,3}-flavoured denominator is a *non-growing* 2² sitting in
the geometric ζ(7)-period normalisation 75/4 = 3·5²/2². This is a clean,
falsification-relevant refinement, not a confirmation.

---

## 1. EXTRACT [VERIFIED — transcribed from BZ, lines 1443–1467]

### 1.1 The integral

Totally symmetric M₀,₁₀ family (7-fold, over the ordered simplex
0 < t₁ < ⋯ < t₇ < 1), with

    B(t) = t₁(t₂−t₁)(t₃−t₂)(t₄−t₃)(t₅−t₄)(t₆−t₅)(t₇−t₆)(1−t₇)
    D(t) = (t₃−t₁) t₃ t₅ (t₅−t₂)(t₇−t₂)(t₇−t₄)(1−t₄)(1−t₆)

    Iₙ = ∫_{0<t₁<⋯<t₇<1} ( B(t)/D(t) )ⁿ · dt₁⋯dt₇ / D(t).

(Equivalently Iₙ = ∫ Bⁿ / Dⁿ⁺¹.) An independent Monte-Carlo of the n = 0 case
(`zeta7_audit.py` MC block) gives I₀ ≈ 3.99 against the closed-form 3.555 —
agreement to ~1 significant figure, limited by the boundary singularities
1/(t₃−t₁), 1/(t₇−t₂), … ; enough to rule out a gross transcription error, not a
precision check. [ATTEMPTED]

### 1.2 Exact linear forms for n = 0,1,2 [VERIFIED, verbatim from the paper]

BZ split Iₙ = I′ₙ + I″ₙ·ζ(2), where **I′ₙ ∈ span{1, ζ(5), ζ(7)}** (the
ζ(2)=0 part — the object of interest) and **I″ₙ ∈ span{1, ζ(3), ζ(5)}**:

    I₀ = 75/4·ζ7                                − 9·ζ5·ζ2
    I₁ = (61·75/4·ζ7 − 300·3·ζ5 − 220)         − (61·9·ζ5 − 300·2·ζ3 + 152)·ζ2
    I₂ = (52921·75/4·ζ7 − 261153·3·ζ5 − 6021219/32)
                                               − (52921·9·ζ5 − 261153·2·ζ3 + 535857/4)·ζ2

Numeric consistency [VERIFIED]: Iₙ is a genuinely small linear form —
I₀ = 3.56, I₁ = 3.2·10⁻⁵, I₂ = 1.1·10⁻⁹ — decaying at the rate BZ's
asymptotics require, while the coefficients grow (|ζ7-coeff| = 18.8, 1.1·10³,
9.9·10⁵). This certifies that the transcription of both forms is internally
correct.

### 1.3 DERIVED shared-integer skeleton

Refactoring the printed data exposes a two-sequence ladder (verified exactly,
`zeta7_audit.py`):

    I′ₙ  = (75/4)·qₙ·ζ7  − 3·sₙ·ζ5  − Pₙ
    I″ₙ  =    −9·qₙ·ζ5   + 2·sₙ·ζ3  − P̂ₙ

with integer sequences and rational constants

    qₙ = 1, 61, 52921          (shared: ζ7-coeff of I′ and ζ5-coeff of I″)
    sₙ = 0, 300, 261153        (shared: ζ5-coeff of I′ and ζ3-coeff of I″)
    Pₙ = 0, 220, 6021219/32
    P̂ₙ = 0, 152, 535857/4

This is the M₀,₁₀ analogue of the single BZ sequence Qₙ that, for M₀,₈,
multiplies both ζ(5) (in I′) and ζ(3) (in I″). Here the extra weight (rank 4
vs rank 3) forces **two** ladder sequences: qₙ carries the 7→5 rung, sₙ the
5→3 rung. Each ζ(2)-multiplication drops the weight by 2, which is exactly
why qₙ reappears two weights down. [DERIVED — a structural observation not
stated in BZ.]

### 1.4 Period decomposition [VERIFIED from data — PSLQ discovery unnecessary]

BZ state the motive is rank 4 with semisimple pieces ℚ(0), ℚ(−2), ℚ(−5),
ℚ(−7). The realised period basis of the *full* Iₙ closes on

    {1, ζ(2), ζ(3), ζ(5), ζ(7), ζ(2)ζ(3), ζ(2)ζ(5)}   (7 monomials),

grouped as ℚ(0)→1, ℚ(−2)→ζ(2), ℚ(−5)→ζ(5), ℚ(−7)→ζ(7), with the extension/
off-diagonal entries realised by ζ(2)ζ(3) (weight 5 = 3+2) and ζ(2)ζ(5)
(weight 7 = 5+2), and ζ(3) appearing in the ζ(2)=0 companion I″. **No genuine
weight-5 or weight-7 MZV (ζ(3,2), ζ(5,2), …) appears**: although BZ note ζ₅,ζ₇
are a priori "linear combinations of MZV of weight 5,7", at the totally
symmetric point they collapse to rational multiples of the single zetas ζ(5),
ζ(7) (visible directly: I′₀ = 75/4·ζ(7) exactly). The planned PSLQ basis-
discovery over a weight-≤7 MZV basis is therefore moot here — the paper's
explicit forms already pin the basis, and the collapse-to-single-zetas is itself
the answer to "which 4 combinations appear". [DERIVED]

---

## 2. FEASIBILITY of extending to n ≥ 3 (the crux)

We have exact anchors only at n = 0,1,2 — the same range BZ reached, and they
stop there for a stated reason (line 1471: *"calculating higher weight
integrals for small values of the parameters does not seem practical with
current tools"*). Assessment of each route:

**(a) Barnes / hypergeometric reduction of the PRIMAL integral — gives I′ₙ,
the target; HARD.** For M₀,₈ (5-fold) BZ recognise the inner y-integrals as
₃F₂'s, apply Barnes, and expand a *double* Mellin–Barnes integral into a ℚ-form
in single+double zetas (§"Barnes-type representation", lines 453–575), yielding
the full (Qₙ, P̂ₙ, Pₙ) decomposition. The M₀,₁₀ analogue is a **triple**
Mellin–Barnes integral (more inner ₃F₂ factors, weight 7), expanded into
single+double+triple zetas. This is the *correct* route to the exact I′ₙ, but
it is a genuine multi-day research derivation specific to this integrand
(change of variables → ₃F₂-triple-product → Barnes → residue bookkeeping), and
is precisely what BZ flag as impractical at this weight. **Not reachable within
a scouting budget.** [ATTEMPTED — scoped, not executed.]

**(b) Fast nested sum / very-well-poised DUAL series — computable, but WRONG
object.** BZ show (lines 1206–1252) the cellular family is *dual* to the
very-well-poised series (their eq. 10)

    F̃ₖ(b) = Σ_{μ≥0} (b₀+2μ+2) · Γ(b₀+μ+2)·∏_{j=1}^k Γ(b_j+μ+1)
                     / ( μ! · ∏_{j=1}^k Γ(b₀−b_j+μ+2) ) · (−1)^{(k+1)μ},

which represents a ℚ-linear form in 1 and ζ(i), 2≤i≤k−2, i≡k (mod 2). The
M₀,₈ dual is k = 7 (→ 1,ζ(3),ζ(5)); **the ζ(7) family is k = 9** (→
1,ζ(3),ζ(5),ζ(7)), symmetric point b₁=⋯=b₉=n, b₀ = c·n (c ≥ 2 fixed by the —
unpublished — M₀,₁₀ b-parametrisation; "the case for general k will be
discussed elsewhere"). This series *is* implementable and fast, and one could
PSLQ-recover its exact 1,ζ(3),ζ(5),ζ(7) coefficients for many n and audit
*those* denominators. **But it is the dual integral, a different linear form
from I′ₙ** (BZ use it only for reciprocal asymptotics; e.g. the M₀,₈ dual
F₇ ∈ ℚ+ℚζ(3)+ℤζ(5) already differs from I′ₙ = Qₙζ(5)−Pₙ, which has no ζ(3)).
So route (b) does **not** deliver step 3's target coefficients; it is a
*cross-family control* at best. **Best next low-risk experiment**, but off-
target. [ATTEMPTED — scoped; the exact k=9 series is written above for a
follow-up.]

**(c) Apéry-type recurrence via creative telescoping — blocked by tooling.**
For M₀,₈ BZ obtained an order-3 polynomial recurrence with Koutschan's
`HolonomicFunctions` (Mathematica) from the 5-fold integrand, then propagated
Qₙ,P̂ₙ,Pₙ. With only 3 terms one **cannot** guess an order-≥3 recurrence, and
no telescoping engine (HolonomicFunctions / ore_algebra / Sage) is available in
this environment; a 7-fold creative-telescoping certificate is also
substantially heavier than the 5-fold one BZ ran. **Blocked.** [ATTEMPTED.]

**(d) Direct 7-dim quadrature — infeasible for PSLQ.** PSLQ against a weight-7
basis needs ≳ 50–100 digits; the integrand has boundary singularities
(1/(t₃−t₁), 1/(t₇−t₂), …). Plain Monte-Carlo gave ~1 digit (§1.1); tanh–sinh /
sparse-grid at 7 dimensions to 100 digits is not realistic. **Infeasible.**
[VERIFIED negative — MC evidence in script.]

**Verdict.** The exact target I′ₙ is available only at n = 0,1,2 within budget.
The single computation that would settle the open question below is route (a)
at n = 3 (or Panzer's HyperInt in Maple, if that toolchain is obtained — it is
what produced BZ's n=0,1,2).

---

## 3. DENOMINATOR AUDIT on the exact anchors n = 0,1,2

All exact, `zeta7_audit.py`. dₙ = lcm(1..n): d₀=d₁=1, d₂=2. Natural laws:
dₙ⁷ for the weight-7 form I′ₙ, dₙ⁵ (and dₙ²d₂ₙ) for the weight-5 companion I″ₙ,
by direct analogy with BZ's M₀,₈ display Qₙ, dₙ²d₂ₙP̂ₙ, dₙ⁵Pₙ ∈ ℤ.

### 3.1 The ζ(7)-form I′ₙ, per-prime

| n | ζ7-coeff = 75/4·qₙ | ζ5-coeff = −3sₙ | const −Pₙ | common den | dₙ⁷ | **extra factor K** beyond dₙ⁷ |
|---|---|---|---|---|---|---|
| 0 | 75/4, den 2² | 0 | 0 | 2² | 1 | **2²** |
| 1 | 4575/4, den 2² | −900 | −220 | 2² | 1 | **2²** |
| 2 | 3969075/4, den 2² | −783459 | −6021219/32, den 2⁵ | 2⁵ | 2⁷ | **1** (dₙ⁷ over-clears; slack 2²) |

So: to make K·dₙ⁷·I′ₙ have integer coefficients, K = 2², 2², 1. **The excess
is 2², support {2} only, non-growing, and gone by n = 2.**

### 3.2 The weight-5 companion I″ₙ and the constant terms

| n | den(Pₙ) | vs dₙ⁷ | den(P̂ₙ) | vs dₙ⁵ |
|---|---|---|---|---|
| 0 | 1 | ✓ (K=1) | 1 | ✓ (K=1) |
| 1 | 1 | ✓ (K=1) | 1 | ✓ (K=1) |
| 2 | 2⁵ | ✓, slack 2² | 2² | ✓, slack 2³ |

**The constant terms carry NO excess** — dₙ⁷Pₙ ∈ ℤ and dₙ⁵P̂ₙ ∈ ℤ with room to
spare, no clearing factor needed at all.

### 3.3 The crux contrast with M₀,₈ (matched n = 2) [VERIFIED]

|  | den(P₂) | den(P̂₂) | excess over natural law |
|---|---|---|---|
| **M₀,₈ / ζ(5)** | 1190161/**384**, 384 = **2⁷·3** | 344923/**96**, 96 = **2⁵·3** | **2²·3 = 12** on P; **2** on P̂ — the {2,3} fingerprint |
| **M₀,₁₀ / ζ(7)** | 6021219/**32**, 32 = **2⁵** | 535857/**4**, 4 = **2²** | **none** (slack) |

At the *same* n = 2, the M₀,₈ constant denominators each contain a factor 3 —
and that 3 is **not** from dₙ (d₂ = 2 has no 3): it is the genuine 3-adic
Bernoulli/elimination cost the mechanism predicts. The M₀,₁₀ constant
denominators contain **no 3 whatsoever** (the 3's in these numbers all sit in
the *numerators*: 6021219 = 3·41·48953, 535857 = 3·7·17·19·79). The "12 excess
located in the growing constant term" — the empirical signature of the M₀,₈
family — **does not reproduce** in the M₀,₁₀ ζ(7)-form.

---

## 4. Interpretation vs. the mechanism [DERIVED + SPECULATION, tagged]

**What the mechanism (PROOF_MECHANISM.md, Lemma 1) predicts.** ζ(2)-elimination
costs a factor dividing 24 = 2³·3 (the Bernoulli lattice constant of
ζ(2) = −(2πi)²/24), measured as 12 = 2²·3 in M₀,₈, supported at {2,3}, and
appearing as denominator excess in the eliminated form's coefficients.

**What the data shows for M₀,₁₀ (n ≤ 2).** [VERIFIED]
1. The eliminated ζ(7)-form I′ₙ carries exactly one {2,3}-flavoured
   denominator: a **persistent, non-growing 2²** in the ζ(7)-period
   normalisation 75/4 = 3·5²/2².
2. This 2² is present already at **n = 0**, where I′₀ = 75/4·ζ(7) is literally
   the odd part of the geometric period I₀ — so it is a **period feature, not
   an n-growth elimination cost.** (Contrast M₀,₈: I′₀ = ζ(5) exactly, coeff 1,
   *no* denominator — a clean period.)
3. The growing constant term Pₙ shows **no excess** over dₙ⁷ (in fact slack),
   and **no factor 3** at n = 2 — unlike M₀,₈'s 12.

**Two honest readings of the 2².**
- *(A) geometric-period reading [preferred].* 75/4·ζ(7) is the intrinsic
  period of the ℚ(−7) piece of *this* integral; its 2² is geometry, not cost.
  Under (A), the ζ(2)-elimination in the M₀,₁₀ family leaves **zero {2,3}
  denominator cost** in I′ₙ at n ≤ 2 — a clean *negative* for the mechanism's
  "bounded {2,3} excess in the eliminated form" as stated for constants.
- *(B) uniform-normalisation reading.* If one insists ζ(7) itself is the
  period, the correction factor is **2², support {2}, bounded, non-growing** —
  the mechanism's *shape* (bounded, ⊆{2,3}) survives, but the **3-part is
  absent** and the location moved from the constant to the top coefficient.

Either way, the specific **12 = 2²·3 fingerprint and its constant-term
location do not transfer.** [DERIVED]

**Why n = 3 is decisive, and why n ≤ 2 cannot settle the 3-part.** [SPECULATION,
clearly labelled] In M₀,₈ the 3-adic cost was already visible at n = 2 *without*
dₙ help. Its absence here at n = 2 is a real apples-to-apples difference. But
one cannot yet exclude a 3-adic effect appearing first at **n = 3**: n = 3 is
the smallest n where dₙ = 6 itself acquires a factor 3, so both the "intrinsic
Bernoulli 3" and the "dₙ-driven 3" first have a place to live simultaneously.
The single most informative next datum is therefore the exact I′₃ — obtainable
only via route (a) or HyperInt.

---

## 5. Summary ledger (per-prime, the deliverable table)

For the eliminated ζ(7)-form I′ₙ = (75/4)qₙζ(7) − 3sₙζ(5) − Pₙ, extra clearing
factor K required beyond the natural dₙ⁷ law, per prime:

| n | K₂ (ord₂) | K₃ (ord₃) | K at p≥5 | total K |
|---|---|---|---|---|
| 0 | +2 | 0 | 0 | 2² |
| 1 | +2 | 0 | 0 | 2² |
| 2 | 0 (slack −2) | 0 | 0 | 1 |

Compare M₀,₈ (same table, from `CONJECTURE.md`): K = 2²·3 at the binding
cells, the 3-part attained at n = 2. **The M₀,₁₀ ζ(7)-form's measured
correction is {2}-supported (2²) and geometric (a period normalisation), with
no 3-adic cost and no growth on the available data.**

**Status of the tested prediction:** neither confirmed nor refuted — *refined*.
The mechanism's bounded-{2,3} shape is compatible with the 2²; its distinctive
2²·3 = 12 magnitude and constant-term location are **not** observed. Decisive
test = I′₃ (route (a) / HyperInt), currently beyond budget/tooling.

## 6. Provenance / honesty ledger
- §1.1–1.2, 3.3 numbers: **[VERIFIED]** transcribed from CellZeta.tex 1443–1467
  and 226–271, factored exactly in `zeta7_audit.py`.
- §1.2 smallness of Iₙ, §1.1 MC of I₀: **[VERIFIED / ATTEMPTED]** computed here.
- §1.3 (q,s ladder), §1.4 (basis closure), §3 ledger, §5 table: **[DERIVED]**
  exact-rational, reproducible via `python3 zeta7_audit.py`.
- §2 feasibility verdicts: **[ATTEMPTED/analysis]** — routes scoped, (c)/(d)
  shown blocked/infeasible, (a) identified as the on-target hard route,
  (b: k=9 series) written explicitly for a follow-up cross-family control.
- §4 interpretation: reading (A/B) **[DERIVED]**; the n=3 argument **[SPECULATION]**.
