# Odd zeta values: measurements, a denominator conjecture, and a formalized theorem

Experimental and formal mathematics on the irrationality constructions for odd
zeta values (Apéry, Rhin–Viola, Ball–Rivoal, Brown–Zudilin), produced
2026-07-16/17 in a human–AI collaboration. Every claim below carries an
explicit evidence class:

**[FORMAL]** machine-verified in Lean 4 (kernel axiom check) ·
**[THM]** proved, human-readable proof in the repo ·
**[COMP]** exact computation, certified & reproducible ·
**[CONJ]** conjecture with stated evidence ·
**[OPEN]** precisely stated open problem.

---

## Results for the busy mathematician

**1. [FORMAL] At least one of ζ(5), ζ(7), …, ζ(33) is irrational.**
Full Lean 4/Mathlib formalization of Zudilin (SIGMA 2018, arXiv:1801.09895),
in the s=33 variant via Hanson's elementary d_n ≤ 3^n (also formalized from
scratch — current Mathlib has no PNT; s=33 is the paper's own stated
fallback). `#print axioms zeta_odd_irrational` →
`[propext, Classical.choice, Quot.sound]`; zero sorries.
→ `zeta5odd/` (companion paper: `zeta5odd/paper.pdf`).
**Browse the proof interactively:** [dependency-graph blueprint](https://rain-1.github.io/odd-zeta-blueprint/)
— every definition, lemma and theorem is a node (all green = formalized),
linked to its Lean declaration. Source in `zeta5odd/blueprint/`.
To our knowledge the first machine-verified irrationality of this kind beyond ζ(3).

**2. [COMP] sup γ = 0.86597135… for the Brown–Zudilin ζ(5) family** —
the "worthiness" exponent of arXiv:2210.03391 attains its supremum over the
full 7-dimensional projective parameter cone exactly at the authors'
published point (whose symmetric coordinates form an arithmetic
progression). Exhaustive AP-family scan (31,710 projective points),
multi-start and basin-hopping searches. The γ implementation reproduces all
printed values to 8 decimals. → `worthiness/RESULTS.md`, `worthiness/gamma.py`.

**3. [COMP] The printed integrality claims of arXiv:2210.03391 are false as
stated** — including against the paper's own displayed values (e.g.
d₂⁵·P₂ = 1190161/12 ∉ ℤ). The corrected statements carry a factor of exactly
**12 = 2²·3** (resp. 2 for the ζ(3)-companion). → `worthiness/CONJECTURE.md` §3.

**4. [CONJ] The sharp-12 denominator law.** For the family's coefficients,
per prime: ord_p den(Pₙ) ≤ ord_p D_ν + (2 if p=2; 1 if p=3; boundary-prime
fluctuations of size ≤1 at p=m₁ else 0), where D_ν is the group-sharpened
lcm-product with ν_p extended to all primes. Verified in **200+ certified
cells** (exact PSLQ recovery, anchors reproduce all printed rationals);
ceilings attained 46× (p=2) and 30× (p=3); one verified single-orbit p=7
exception, orbit-coherent and non-persistent. Unlike every classical
correction factor we checked (Apéry, KR, Vasilyev — all removable), this one
is **attained**. → `worthiness/CONJECTURE.md`.

**5. [THM]+[COMP] The mechanism: elimination cost = Bernoulli 24 ÷ lattice
index.** An elementary lemma: any integral Betti class killing the
ζ(2)-period column is a multiple of 24γ₁+γ₂ (from ζ(2) = −(2πi)²/24).
The measured 12 = 24/2 then *measures* a lattice index; exact computation
locates it: all seven iterated residues of the integrand along the weight-4
strata equal ±1 (de Rham class primitive), so **the factor 2 is a genuine
index-2 refinement of the integral Betti lattice of the M̄₀,₈ motive**
(γ₂/2 ∈ L); p=3 and p≥5 parts discharged by derivation; the anomalous prime
is pinned to 2 by the involution. Remaining for full
measurement-independence: one integral differential at two named strata
(where a new bi-arrangement non-transversality was found). Apparently the
first computed integral-lattice invariant of a period of M̄₀,₈; the ℚ-theory
(Dupont, Brown) never touches denominators. → `worthiness/PROOF_MECHANISM.md`,
`H2_LATTICE.md`, `H2_SIGNS.md`.

**6. [COMP] Two orthogonal species of constants** (5-family table): static
de Rham period normalizations (Rhin–Viola's classical "ℚ+2ℤζ(3)" factor is
one — J₀ = 2ζ(3) exactly, an elementary double-log doubling, provably
*distinct* from the Betti cost by three invariants) versus growing Betti
elimination costs, paid only by families that eliminate an even period —
of which the BZ ζ(5) family is the unique measured instance.
→ `worthiness/TABLE.md`.

**7. [COMP] Cross-family checks:** the leading factor 2 in
Krattenthaler–Rivoal's conjectured denominator law for Zudilin's
ζ(5)…ζ(11) forms (Mém. AMS 2007, eq. 17.1) is unnecessary for n ≤ 5
(apparently the first direct computation of those coefficients; ~30 bits of
2-adic margin); d_n⁴ is 2-adically tight for the ζ(4) forms to n = 40.
→ `worthiness/ZN_FACTOR2.md`, `TABLE.md`.

**8. [COMP] The weight-7 family (M₀,₁₀, rank-4 motive):** first new exact
data beyond Brown–Zudilin's n ≤ 2. Leading coefficients via the
McCarthy–Osburn–Straub diagonal construction (validated twice: reproduces
the printed 1, 61, 52921 AND, unchanged, the classical Apéry ζ(3) numbers):
**q₃ = 94357501**, q₄ = 235634763001, …, q₀…q₃₀ archived (extension to ~90
terms and the recurrence campaign in progress). Structural theorems from the
campaign: the ζ(2)-eliminated form lies outside the single-sum
very-well-poised class (a sign dichotomy: projections vs simultaneous
approximations); the cell is dihedrally rigid (trivial stabilizer — no
symmetric Barnes reduction exists); the CT obstruction is a full-width
coupling window, circumvented by 41 exact low-coupling re-representations.
Bonus: the classical Apéry ζ(3) recurrence re-derived from cellular windows
by creative telescoping in 2 s; the BZ ζ(5) characteristic polynomial
4λ³−2368λ²−188λ+1 confirmed three independent ways.
→ `worthiness/ZETA7_BARNES.md`, `ZETA7_DUAL.md`, `ZETA7_CT_COUPLING_REPORT.md`.

**9. [OPEN] Named open problems**, precisely stated: the two-variable
well-poised 2n→n refinement (the core of the general denominator theorem,
H1 — three-tier structure and a proven support law surround it); the
integral OS-bicomplex differential at two strata (H2's last step); the
2-adic attainment; the weight-7 elimination-cost test (awaits den(P₃)).
→ `worthiness/H1_COLLAPSE.md`, `H2_SIGNS.md`, `PROOF_SYMMETRIC_v2.md`.

**Papers:** `paper/denominators.pdf` (measurements + conjecture + mechanism,
9 pp, draft) and `zeta5odd/paper.pdf` (the formalization, 7 pp).

---

## Repository map

| Path | Contents |
|---|---|
| `zeta5odd/` | The Lean 4 formalization (Mathlib; `lake build`; root theorem in `Zeta5Odd/Main.lean`) + companion paper + [interactive blueprint](https://rain-1.github.io/odd-zeta-blueprint/) (source in `zeta5odd/blueprint/`) |
| `worthiness/` | All experimental mathematics: γ search, audit pipeline (`audit.py`, `fast_eval.py`), 200+ certified cells (JSONL), conjecture/mechanism/table documents, ζ(7) campaign |
| `paper/` | The measurements paper (LaTeX + PDF) |
| `SURVEY.md` | The original research-directions survey that started this (historical) |

## Method and trust

Coefficients are recovered as exact rationals by PSLQ from certified
high-precision evaluations (residual + precision-stability checks; anchors
reproduce every rational printed in the source papers), or by exact rational
arithmetic where series representations permit. The repository's history
includes an explicit corrections discipline: claims found overstated were
amended in place with the record preserved (see the amendment blocks in
`CONJECTURE.md` and the audit changelogs in `PROOF_SYMMETRIC_v2.md`).
Everything is reproducible from the committed scripts; heavy runs used a
small fleet of machines whose outputs are archived as JSONL.

*Produced by River (direction, key literature steers, adversarial review)
and Claude (Fable 5) orchestrating Claude Opus subagents (computation,
proofs, formalization), 16–17 July 2026.*
