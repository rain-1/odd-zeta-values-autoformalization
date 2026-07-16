# The lattice-index table across the M₀,ₙ cellular families

**First empirical table of the integral-lattice / denominator invariants of the
Brown–Zudilin / Apéry cellular period families.** Each row is one cellular family;
constants are recorded **agnostically** (exact arithmetic, per prime, measured
first) and only then interpreted. Scope tags throughout: `[PROVEN]`,
`[COMPUTED]` (exact but finite), `[TRANSCRIBED]`, `[DERIVED]`, `[SPECULATION]`.
House rule enforced: the weight-5 *Betti-index* mechanism is **not** forced onto
families with a different elimination structure — the table records what IS, and
its central finding is that **two different kinds of "factor 2" coexist in this
subject and have provably different natures.**

Scripts: `table_row2.py`, `table_row2_residue.py`, `table_row3.py`,
`table_row4.py`; ROW 1 evidence `h2_p2_deRham.py` + `H2_LATTICE.md`; ROW 5
`zeta7_audit.py` + `ZETA7_FAMILY.md`. No existing files modified.

---

## The table

| # | family (space) | motive rank & weights (grᵂ) | even-period elimination the linear forms perform | measured sharp clearing constant (per prime, agnostic) | Bernoulli-part × located-lattice-index split + de Rham residue evidence |
|---|---|---|---|---|---|
| **1** | ζ(5), M₀,₈ (BZ) | rank 3: ℚ(0)⊕ℚ(−2)⊕ℚ(−5) | **ζ(2) → ζ(5)** (I=I′+I″·ζ(2); I′=Qζ(5)−P is the ζ(2)=0 part) | **P: 12 = 2²·3** (excess +2@2, +1@3, 0@p≥5); **P̂: 2 = 2¹** (+1@2, 0@3). Rare non-structural +1@7 at one n=1 cell. | 24 = 2³·3 abstract (ζ(2)=−(2πi)²/24). de Rham iterated residues **all ±1** ⇒ 2-integral ⇒ 24→12 halving at p=2 is a **Betti lattice index 2** (γ₂/2∈L). p=3: index 1 (unrefined vSC 3 of B₂). **I′₀ = ζ(5) (coeff 1, clean).** |
| **2** | ζ(3), M₀,₆ (Beukers/Apéry) | rank 2: ℚ(0)⊕ℚ(−3) (no ℚ(−2) realized) | **NONE.** ζ(2)-coeff ≡ 0 exactly ∀n — even slot **vanishes by parity**, not eliminated | den(2bₙ) ∣ dₙ³ with **negative** (slack) excess at every prime (−2@2, ≤−1@3). Only correction: **static factor 2 on ζ(3)** (coeff = 2aₙ, even) | 2 is **de Rham**, not Betti: **J₀ = 2ζ(3) exactly**, the 2 = symmetric double-log ln(xy)=ln x+ln y (two identical residue summands). No growing Betti cost; the lattice-index language does not capture this 2. |
| **3** | ζ(2), M₀,₅ (Apéry) | rank 2: ℚ(0)⊕ℚ(−2) | **NONE** — this family **IS** the ζ(2)-extension (control case) | den(bₙ) ∣ dₙ² with slack; **clearing constant = 1** | **I₀ = ζ(2) (coeff 1, clean period, no log-doubling).** Pays no Bernoulli cost because it performs no elimination. |
| **4** | ζ(4), VWP (Vasilyev / Marcovecchio–Zudilin E=4) | weight 4 (VWP; form in 1, ζ(4)) | (odd-ζ parity cancels; ζ(4) is the top period) | uₙ ∈ ℤ ∀n; **den(vₙ) ∣ dₙ⁴** for n=1..40, worst excess 0@2 (tight, not over). Literature's leading **2 never needed** | dₙ⁴ is 2-adically **tight** (n=2: den=2⁴=d₂⁴); the printed `2·Φₙ⁻¹·dₙ⁴` carries exactly **one spurious factor 2** — a term-wise VWP half-shift artifact, not a lattice cost. |
| **5** | ζ(7), M₀,₁₀ (BZ) | rank 4: ℚ(0)⊕ℚ(−2)⊕ℚ(−5)⊕ℚ(−7) | **ζ(2) → {ζ(5),ζ(7)}** (two ladder seqs qₙ:7→5, sₙ:5→3) | K beyond dₙ⁷: **2², 2², 1** at n=0,1,2. Support **{2} only**, non-growing, gone by n=2. **No 3-part.** Constant Pₙ: slack. | 2² is **de Rham**: it sits in the ζ(7)-period normalization **I′₀ = (75/4)ζ(7)**, 75/4 = 3·5²/2², present at n=0. **The 12=2²·3 fingerprint does NOT transfer.** `[PARTIAL — awaiting n=3 unlock]` |

---

## The centerpiece (ROW 2): the two "2"s have different natures `[PROVEN / COMPUTED]`

The opener asked whether the coefficient 2 in Rhin–Viola's "ℚ + 2ℤζ(3)"
(Acta Arith. 97 (2001), Thm 2.1) is the **same** object as the p=2 Betti lattice
index measured in the weight-5 family (`H2_LATTICE.md`), or a different phenomenon.
**Verdict: they are provably different.** Routing the ζ(3) valuation chain the same
way as the weight-5 case isolates three distinguishing invariants:

**(i) Where the 2 lives in n.**
- ζ(5): I′₀ = ζ(5) with coefficient **1** — a *clean* period; the factor 2 is
  **invisible at n=0** and appears only in the **growing** constant term Pₙ.
- ζ(3): J₀ = **2ζ(3)** — the factor 2 is **already in the geometric period at n=0**,
  and it is **static** (the ζ(3)-coefficient of Jₙ is 2aₙ for the Apéry integers aₙ,
  even for every n; `table_row2.py`).

**(ii) The p=2 sign of the constant term (opposite!).**
- ζ(5): den(Pₙ) has **excess +2 at p=2** over dₙ⁵ — a genuine 2-adic *cost*
  (`CONJECTURE.md`; attained 28×).
- ζ(3): den(2bₙ) has excess **−2 at p=2** over dₙ³ — the constant is 2-adically
  *slack*. The ζ(3) constant term pays **no** p=2 cost; the opposite sign proves
  the 2 is not a clearing constant of the same kind.

**(iii) The de Rham residue.**
- ζ(5): the exact iterated residues of the integrand along its 7 transverse strata
  are **all ±1** (`h2_p2_deRham.py`, re-run green) → the de Rham class is 2-integral,
  so — by the measured product = 2 — the 2 is forced onto the **Betti** side
  (integral lattice index 2, γ₂/2 ∈ L).
- ζ(3): the 2 **IS** the de Rham residue normalization. The z-pole of
  1/(1−(1−xy)z) sits at z = 1/(1−xy) > 1, *outside* [0,1], so the z-integral is a
  **boundary logarithm** −ln(xy)/(1−xy), not an interior residue; and
  ln(xy) = ln x + ln y contributes **two identical** 1/(k+1)³ summands per mode,
  giving J₀ = Σ 2/(k+1)³ = 2ζ(3) (`table_row2_residue.py`, exact sympy). The 2 is a
  **symmetric double-log / de Rham period-normalization factor**.

**Answer to the opener's question (d).** The 2 of "2ℤζ(3)" is a **de Rham
factor** — specifically the double-log period normalization visible as J₀ = 2ζ(3)
— **not** a Betti lattice index and **not** a per-prime clearing cost. The
lattice-index language, which correctly captures the weight-5 p=2 factor (a
genuine integral-Betti-lattice refinement), **does not capture** the ζ(3) 2: they
are different mathematical objects that happen to share the numeral 2. A proven
"different natures", which the task rated as valuable as a unification.

---

## The synthesis that the table reveals `[DERIVED]`

Two orthogonal families of constants run through these rows; **conflating them is
exactly the historical confusion the table dissolves.**

**A. De Rham period-normalization factors** — the *n=0 geometric period* of each
odd-weight cellular family is (normalization)·ζ(weight):

| family | n=0 geometric period | normalization | nature |
|---|---|---|---|
| ζ(3), M₀,₆ | J₀ = **2**·ζ(3) | 2 = 2¹ | symmetric double-log |
| ζ(5), M₀,₈ | I′₀ = **1**·ζ(5) | 1 | clean |
| ζ(7), M₀,₁₀ | I′₀ = **(75/4)**·ζ(7) | 75/4 = 3·5²/2² | period ratio |

These are **static** (present at n=0), one per family, and are **integrand/residue
features** — the lattice-index language does not describe them. This is why ζ(3)
carries a 2 and ζ(7) a 2² with *no* growing per-prime cost.

**B. Betti elimination-cost lattice indices** — a family pays these **only if its
linear forms actually eliminate an even period**. The measured cost appears in the
*growing* constant term of the *eliminated* form, per prime, bounded by the
Bernoulli constant 24 = 2³·3 of ζ(2) = −(2πi)²/24:

| family | eliminates? | growing per-prime cost |
|---|---|---|
| ζ(2), M₀,₅ | no (it IS the extension) | **1** (control) |
| ζ(3), M₀,₆ | no (parity kills the ζ(2) slot) | **1** (slack) |
| ζ(4), VWP | no (odd-ζ parity) | **1** (dₙ⁴ tight; printed 2 spurious) |
| **ζ(5), M₀,₈** | **yes (ζ(2)→ζ(5))** | **12 = 2²·3** (Betti index 2 @2 · vSC 3 @3) |
| ζ(7), M₀,₁₀ | yes (ζ(2)→ζ(5),ζ(7)) | **none measured** at n≤2; 3-part absent `[PARTIAL]` |

**The weight-5 family is, on the current data, the unique row that pays a genuine
Betti elimination cost** (the "12 fingerprint"). Every non-eliminating family pays
clearing constant 1. The ζ(7) family *does* eliminate but — surprisingly — shows
**no** transferred 2²·3 cost at n≤2 (only its static 75/4 period 2²); whether a
3-adic Betti cost first appears at n=3 is the open unlock.

---

## Per-row evidence

### ROW 1 — ζ(5), M₀,₈ `[TRANSCRIBED from H2_LATTICE.md, CONJECTURE.md; residues re-run]`
- Motive rank 3, grᵂ = ℚ(0)⊕ℚ(−2)⊕ℚ(−5); torsion-free (Keel).
- Iₙ = −2Pₙ + (−4P̂ₙ)ζ(2) + 2Qₙ(ζ(5)+2ζ(3)ζ(2)); the ζ(2)=0 form I′ₙ = Qₙζ(5)−Pₙ.
- Measured (exact, `CONJECTURE.md`, 164 cells): P-side **12 = 2²·3** sharp
  (P₁=87/4, P₂=1190161/384 = ·/2⁷·3); P̂-side **2**. Ceilings +2@2, +1@3, 0@p≥5
  hold at every cell (one non-structural +1@7 at a single n=1 cell, decays at n=2).
- Split: abstract 24 = 2³·3; de Rham iterated residues along the 7 transverse
  strata **all ±1** (`h2_p2_deRham.py`, re-run: v₂=0 for all seven) ⇒ ω is
  2-integral ⇒ the 24→12 halving is a **Betti index 2 at p=2** (γ₂/2∈L); index 1
  at p=3. `[PROVEN de Rham side; Betti side forced by measured product — the one
  item not independently re-derived is the B-relative 2-divisibility, per §5.5 of
  H2_LATTICE.md]`.

### ROW 2 — ζ(3), M₀,₆ `[COMPUTED exact — the opener]`
- Jₙ = ∫∫∫ [x(1−x)y(1−y)z(1−z)]ⁿ/(1−(1−xy)z)ⁿ⁺¹ = **2aₙζ(3) − 2bₙ**, aₙ =
  ΣC(n,k)²C(n+k,k)² (Apéry integers), bₙ with den ∣ dₙ³ (`table_row2.py`).
- Numeric raw 3D integral matches 2(aₙζ(3)−bₙ) to ~1e−21 (n=0,1); J₀ = 2ζ(3).
- **No ζ(2):** PSLQ[Jₙ, ζ(2), ζ(3), 1] returns ζ(2)-coeff **exactly 0** for n=1,2,3
  — the even slot vanishes by parity; **no elimination performed**.
- Ledger (`table_row2.py`): den(2bₙ) ∣ dₙ³ with excess **{2:−2, 3:≤−1}** (slack);
  **clearing constant 1**. The only correction is the **static** 2 on ζ(3).
- Residue mechanism (`table_row2_residue.py`, exact sympy): z-pole outside [0,1] →
  boundary log −ln(xy)/(1−xy); ln(xy)=ln x+ln y → 2/(k+1)³ per mode → J₀=2ζ(3).
  The 2 is de Rham, **not** Betti. `[PROVEN for n=0; COMPUTED for n≤6]`.

### ROW 3 — ζ(2), M₀,₅ `[COMPUTED exact — control]`
- Iₙ = ∫∫ [x(1−x)y(1−y)]ⁿ/(1−xy)ⁿ⁺¹ = ±(aₙζ(2)−bₙ); |aₙ| = 1,3,19,147,1251,…
  (ζ(2)-Apéry numbers, matched exactly, `table_row3.py`), bₙ with den ∣ dₙ².
- I₀ = ζ(2) (coeff **1**, clean — no log-doubling: there is no z-integration to
  produce a symmetric log). Ledger: den(bₙ) ∣ dₙ² with slack; **clearing 1**.
- Interpretation `[hypothesis, recorded not forced]`: this family performs no
  elimination — it *is* the ζ(2)-extension — so it pays no Bernoulli cost. Control.

### ROW 4 — ζ(4), VWP `[COMPUTED exact, n=1..40]`
- Sₙ = uₙζ(4) − vₙ via the self-tested VWP engine (`zn_check.py`, `table_row4.py`).
- **uₙ ∈ ℤ** and **den(vₙ) ∣ dₙ⁴** at **every** n=1..40; worst per-prime excess
  over dₙ⁴ is **0 at p=2** (tight, e.g. n=2: den=2⁴=d₂⁴) and negative elsewhere.
- ⇒ the literature's leading factor **2 is never needed** (n=1..40), with 2-adic
  margin; dₙ⁴ is the tight 2-part and `2·Φₙ⁻¹·dₙ⁴` over-clears by exactly one 2.
  Same term-wise VWP half-shift artifact as ζ(3), ζ(5..11) (`ZN_FACTOR2.md`).
  **Scope: exact but finite; not a proof for all n.**

### ROW 5 — ζ(7), M₀,₁₀ `[TRANSCRIBED from ZETA7_FAMILY.md — PARTIAL]`
- Motive rank 4, grᵂ = ℚ(0)⊕ℚ(−2)⊕ℚ(−5)⊕ℚ(−7). Exact anchors n=0,1,2 only
  (BZ printed; higher n blocked — route (a)/HyperInt needed).
- I′ₙ = (75/4)qₙζ(7) − 3sₙζ(5) − Pₙ; K beyond dₙ⁷ = 2²,2²,1 at n=0,1,2, support
  {2}, non-growing. The 2² sits in **I′₀ = (75/4)ζ(7)** (period normalization,
  75/4 = 3·5²/2²) — a **de Rham** factor present at n=0, like ζ(3)'s 2.
- The M₀,₈ **12 = 2²·3 fingerprint does not transfer**: no 3-part at n=2, constant
  Pₙ slack. **Awaiting the n=3 unlock** to test whether a 3-adic Betti cost appears
  when dₙ first acquires a 3. `[PARTIAL]`.

---

## Adversarial-audit register
- **Finite ≠ theorem.** Rows 2–4 are exact but finite (n≤6, n≤40). No row promotes
  a verified-finite computation to a proof-for-all-n. Row 1's Betti index and Row
  5's n=3 behaviour remain conditional exactly as their source docs state.
- **Identification caveat (Row 4).** The engine object is the KR very-well-poised
  ζ(4) series S_{n,4,2,1,1}(1); its identity with the specific Vasilyev/
  Marcovecchio integral normalization is asserted at the level of "same VWP family,
  same 2-adic factor-2 question", not proven equal cell-by-cell.
- **Parity vs. no-slot (Row 2).** "The ζ(2) slot vanishes by parity" vs. "there is
  no ℚ(−2) in the motive" are not distinguished here; the *observable* recorded is
  ζ(2)-coeff ≡ 0 and clearing constant 1. Either reading gives the same table entry.
- **No mechanism forcing.** The weight-5 Betti-index reading is applied **only** to
  Row 1. Rows 2/5's factors are recorded as de Rham period normalizations because
  that is what the n=0 periods (2ζ(3), 75/4·ζ(7)) exactly show — not by analogy to
  Row 1.
- **Surprise, logged.** The cleanest surprise: the ζ(3) constant term is 2-adically
  *slack* (excess −2) while the ζ(5) constant is *tight-plus-excess* (+2) — the two
  "2"s carry **opposite** p=2 signs on the constant term, which by itself already
  refutes their identification.
