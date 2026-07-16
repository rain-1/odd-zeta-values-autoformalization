# DUPONT_AUDIT.md — literature audit against Dupont, "Odd zeta motive and linear forms in odd zeta values"

**Target.** C. Dupont (with an appendix by D. Zagier), *Odd zeta motive and
linear forms in odd zeta values*, arXiv:1601.00950, Compositio Math. 154
(2018) 342–379. Read from the actual arXiv PDF (pdftotext) and the ar5iv
render, cross-checked. Companion works read: Dupont, *Relative cohomology of
bi-arrangements*, arXiv:1410.6348 (= the "[Dup17]" he cites for future tools);
and the closest citing work, Eskandari–Murty–Nemoto, *Mixed motives and linear
forms in the Catalan constant*, arXiv:2510.20648 v2 (26 Jan 2026).

**Honesty tags.** `[READ]` = quoted/paraphrased from the paper text I extracted.
`[INFERRED]` = my deduction (confidence noted). Conventions mapped explicitly;
where Dupont's object differs from ours I say so rather than pattern-match.

**Bottom line up front.** Dupont's paper is a **ℚ-linear** theory: it constructs
the motives, proves the coefficients `a_k(ω)` are *rational*, and explains
parity vanishing geometrically — but it **never bounds a denominator, never uses
a ℤ-lattice, and never assigns a lattice index.** Two of our claim-families are
genuinely covered by it and must be reworded to cite it (the abstract extension
mechanism; the parity-vanishing observations). The integral/denominator core of
our program (the 12·D_ν law, the measured-sharp constants, the Betti-lattice-
index reading) is **not** in Dupont. **However**, one 2026 citing paper (EMN,
Catalan) *does* clear denominators and prove denominator upper bounds in a
Brown-program motive — so our flat "the integral synthesis is unwritten /
nobody measures denominators" phrasing is now **false as stated** and needs
softening to the sharper, accurate claim.

---

## Part A. Precise statements from Dupont 1601.00950 `[READ]`

**Setup.** `Xₙ = 𝔸ⁿ_ℚ`, `Aₙ = {x₁···xₙ = 1} ∪ {xᵢ = 0}`; the involution is
`τ : (x₁,…,xₙ) ↦ (x₁⁻¹,…,xₙ⁻¹)` (his eq. (4)). All categories — `MHTS`,
`MT(ℚ)`, `MT(ℤ)` — are **ℚ-linear tannakian** (his §1.2, §2.5). This is the
single most important structural fact for our audit.

**Theorem 1.1 (integral formula for the coefficients).** There is a family of
relative n-cycles `(σ₂,…,σₙ)` *with rational coefficients* in
`(ℂ*)ⁿ ∖ {x₁···xₙ=1}` such that for every integrable `ω`,
`∫_{[0,1]ⁿ} ω = a₀(ω) + a₂(ω)ζ(2) + ··· + aₙ(ω)ζ(n)`, with **aₖ(ω) ∈ ℚ**, and for
`k = 2,…,n`:
> `aₖ(ω) = (2πi)^{-k} ∫_{σₖ} ω`.
The homology classes `[σₖ]` are unique (Thm 4.9). The `n=k=2` case is
Rhin–Viola's contour formula for ζ(2) [RV96, Lem. 2.6]. **No denominator bound
is attached** — the word "denominator" occurs twice in the whole paper, both
about the *integrand* `(1−x₁···xₙ)^N`, never about the `aₖ`.

**Theorem 1.2 / Theorem 5.5 (geometric parity vanishing).** `τ.σₖ` is homologous
to `(−1)^{k−1} σₖ`. Hence: (1) if `τ.ω = ω` then `aₖ(ω)=0` for even `k≠0`;
(2) if `τ.ω = −ω` then `aₖ(ω)=0` for odd `k`. The mechanism (Thm 1.4): `τ` acts
on the summand `ℚ(−k)` of `Z^{(n)}/ℚ(0)` by `(−1)^{k−1}`. Explicit criterion
(his (40)): for `ω = P·dx/(1−x₁···xₙ)^N`, `τ.ω = ±ω ⇔
P(x) = ±(−1)^{N+n}(x₁···xₙ)^{N−2}P(x⁻¹)`.

**Theorem 1.3 (the zeta motive).** Short exact sequence in `MT(ℤ)`:
`0 → ℚ(0) → Z^{(n)} → ℚ(−2) ⊕ ⋯ ⊕ ℚ(−n) → 0`, with period matrix
upper-triangular: top row `(1, ζ(2), ζ(3), …, ζ(n))`, diagonal
`(2πi)², (2πi)³, …, (2πi)ⁿ`, all other entries `0`. So `gr^W(Z^{(n)}) =
ℚ(0)⊕ℚ(−2)⊕ℚ(−3)⊕⋯⊕ℚ(−n)` — **consecutive** weights, and every off-diagonal
period is a **single** zeta value.

**Theorem 1.4 + odd zeta motive.** `(Z^{(n)}/ℚ(0))^+ = ⊕_{k odd} ℚ(−k)`;
`Z^{(n),odd} := p⁻¹((Z^{(n)}/ℚ(0))^+)`; `Z^{odd} = lim_→ Z^{(n),odd}` has period
matrix with first row `1, ζ(3), ζ(5), ζ(7), …` and diagonal
`(2πi)³, (2πi)⁵, …`. So for `n=5`, **`gr^W(Z^{(5),odd)) = ℚ(0)⊕ℚ(−3)⊕ℚ(−5)`**
(weights 0,3,5; periods ζ(3), ζ(5)).

**Prop. 4.12.** `Z^{(n)} ∈ MT(ℤ)`.

**§2.5 (extension groups, all ℚ-linear).** `Ext¹_{MT(ℤ)}(ℚ(−1),ℚ(0)) = 0`;
`Ext¹_{MT(ℤ)}(ℚ(−n),ℚ(0)) → Ext¹_{MT(ℚ)}(ℚ(−n),ℚ(0))` iso for `n≠1`;
`Ext¹_{MT(ℤ)}(ℚ(−(2n+1)),ℚ(0)) ≅ ℚ` (odd), `= 0` (even ≥2); higher Ext `= 0`.
Period matrix of the ζ(2n+1)-extension: `[[1, ζ(2n+1)],[0,(2πi)^{2n+1}]]`. These
are **dimension counts of ℚ-vector spaces**, never lattice indices.

**Zagier Appendix A (series↔integral dictionary).** Elementary construction of
the `aₖ(ω)`. With `∆R(k)=R(k+1)−R(k)` the forward difference, `V₀/∆(V₀) ≅ ⊕ℚ`
via residues `βᵣ(R)` (partial-fraction coefficients of `R` at the poles
`(k+1)^{-r}`), and `Σ_{k≥0} R(k) = R₀(0) + Σ_{r≥2} βᵣ(R)ζ(r)`. Lemma A.1:
`Φₙ(x^{a₁−1}···x^{aₙ−1}/(1−x₁···xₙ)^N) = binom(k+N−1, N−1)/((k+a₁)···(k+aₙ))`.
**This is an explicit, elementary coefficient formula** — the ζ(r)-coefficient
is the βᵣ-residue of an explicit one-variable rational function. Zagier proves
this reproduces Thm 1.1's `aₖ` (the "compatibility" of the abstract).

**Related work, explicitly flagged by Dupont `[READ]`.**
* Line "It would be interesting to determine the precise relationship between our
  motives and those defined in [Bro16] in terms of the moduli spaces `M₀,ₙ₊₃`."
  → **Dupont does NOT identify his construction with Brown's M₀,ₙ cellular
  motives.** This is left OPEN. Our BZ family lives in Brown's M₀,₈/M₀,₁₀ world.
* He suggests his ad-hoc long exact sequences "should be replaced by more
  systematic tools such as the Orlik–Solomon bi-complexes from [Dup17]"
  (= arXiv:1410.6348).

## Part B. The bi-arrangement paper (arXiv:1410.6348) `[READ abstract + main thm]`

Main theorem: *the motive of an exact bi-arrangement is computed by its
Orlik–Solomon bi-complex.* A bi-arrangement = two families of hyperplanes plus
coloring of strata; its "motive" is the relative cohomology of the pair. The OS
bi-complex is a **combinatorial** model built from the intersection poset.
**Integrality:** the paper computes the **motive = rational MHS / mixed Tate
object**; the abstract and framework do **not** state an integral (ℤ) refinement
or track torsion `[READ — abstract; INFERRED for body, moderate confidence]`.
The OS bicomplex is defined over ℤ combinatorially, so an integral refinement is
*plausible in principle*, but **as published it computes ℚ-ranks / the ℚ-motive,
not a ℤ-lattice index.**

## Part C. The one citing work that goes integral — EMN 2026 `[READ]`

Eskandari–Murty–Nemoto, arXiv:2510.20648 v2 (Jan 2026), same Brown program,
builds a motive `M` (5-dim, `gr^W = ℚ(0)⊕ℚ(−1)³⊕H¹(A)(−1)`; MT over `ℚ(i)`,
not over ℚ) with the **Catalan constant** `G` as period, extracts `C` via a
symmetry `σ` (exactly the Dupont/Brown "extract a submotive by an involution"
move), and computes the coefficients of linear forms `a_F + b_F G` **explicitly**.
Crucially it **does bound denominators**:
> **Theorem 8.3.1.** For `F ∈ ℤ[x,y]` σ-invariant of degree `N`,
> `∫_∆ F dxdy/(1−x²−y²) = a_F + b_F G` with **`2^N b_F ∈ ℤ`** and
> **`2^{N+2} L_N L_{N/2} a_F ∈ ℤ`** (`L_m = lcm(1,…,m) = d_m`).

And it clears denominators to form "the ℤ-linear form" (§1.1, §7.1). **But**
(Remark 8.3.3) the bound is proved *"at the level of `C_dR` … with no reference
to the underlying motivic context"* — i.e. it is a classical de-Rham/formula
**upper bound** (residue + partial-fraction clearing), *uniform in `F` of given
degree*, explicitly *not sharp* and *not good enough for irrationality*
(Remark 8.3.4). There is **no lattice-index, no measured-sharp constant, no
Betti-primitivity** anywhere. The `2^{N+2}` is a crude clearing of 2's — exactly
the kind of factor our TABLE.md ROW 4 diagnoses as "spurious/slack".

**Net:** EMN is the closest published cousin to our arithmetic ambitions and it
postdates all our claims. It shows Dupont's method *can* be pushed to denominator
upper bounds — but only in the classical upper-bound style, for weight-2 Catalan,
never as a measured-sharp lattice invariant.

---

## Part D. The central mapping fact (protects most of our novelty) `[INFERRED, high confidence]`

**Our rank-3 motive is NOT Dupont's odd zeta motive.**
* Ours (H2_LATTICE, PROOF_MECHANISM): `gr^W = ℚ(0)⊕ℚ(−2)⊕ℚ(−5)` — weights
  **0,2,5** — with top-row period `ζ₅ = ζ(5) + 2ζ(3)ζ(2)` and middle row
  `(0, (2πi)², (2πi)²ζ(3))`. The entry `ζ(3)ζ(2)` is a **product** of zetas.
* Dupont's `Z^{(5),odd)`: `gr^W = ℚ(0)⊕ℚ(−3)⊕ℚ(−5)` — weights **0,3,5** — periods
  the **single** values ζ(3), ζ(5). His full `Z^{(5)}` has weights 0,2,3,4,5 with
  every off-diagonal period a **single** ζ.

No subquotient of Dupont's `Z^{(n)}` can have `ζ(3)ζ(2)` as a period (all its
matrix entries are single zetas; products cannot arise from ℚ-combinations of
them). Therefore **our motive is a genuinely different object** — the Brown
M₀,₈ cellular motive, whose weight-5 part carries the depth-2 product `ζ(3)ζ(2)`.
This is exactly the relationship Dupont flags as **open** (Part A, line 279).
Consequence: Dupont's *specific* motives do not contain ours; what he *does*
supply that we use is the **abstract MT(ℤ) extension machinery** (Ext-vanishing,
splitting, the ζ(2n+1) period normalization), which is standard Deligne–Goncharov
/ Brown theory that he re-packages cleanly.

---

## Part E. Claim-by-claim verdict table

Verdicts: **SAFE** (Dupont doesn't touch it) / **NEEDS REWORDING** (overlaps; cite
& re-scope) / **SUPERSEDED** (he proves it, cite him instead of claiming it).

### PROOF_MECHANISM.md

| # | Our claim | Verdict | Note / suggested rewording |
|---|---|---|---|
| PM-1 | Lemma 1 (elimination cost 24 from ζ(2)=−(2πi)²/24), **integral/lattice** statement | **SAFE** | Dupont has the period `ζ(2), (2πi)²` in his matrix but never reads the ratio `−1/24` as a lattice-elimination cost or divisibility. The integral/lattice content is ours. Optionally cite Dupont Thm 1.3 for the period normalization. |
| PM-2 | §2 extension analysis: `Ext¹_{MT(ℤ)}(ℚ(−2),ℚ(0))=0 ⟹` splitting `σ`; `E = M/σ(ℚ(−2))` a 2-extension of ℚ(−5) by ℚ(0) with period ζ(5); Ext 1-dim | **NEEDS REWORDING** | This abstract mechanism is exactly Dupont §1.2 / §2.5 / Thm 1.3–1.4 (and older Brown). **Cite Dupont** as the clean reference for the extension calculus and the ζ(5)-extension being 1-dim over ℚ. Keep as ours only the part he lacks: the **integral** splitting cost and the `ζ(3)ζ(2)` contamination (which is specific to our M₀,₈ motive, not his). Don't present the Ext-vanishing/splitting as a new observation. |
| PM-3 | The `ζ(3)ζ(2)` contamination of the e₅-coefficient under the σ-shift | **SAFE** | Absent from Dupont — his motive has no product period (Part D). Genuinely ours. |
| PM-4 | H1 "integral de Rham/Barnes bookkeeping bounds denominators by D_ν" | **SAFE (but see H1 below)** | Dupont's Thm 1.1 gives `aₖ ∈ ℚ` with **no** denominator control; H1 remains open and ours. But the Zagier appendix + EMN Thm 8.3.1 are relevant *tools* — reword H1 to acknowledge them. |
| PM-5 | H2 Betti-lattice normalization / index | **SAFE** | Dupont is ℚ-linear; no Betti lattice, no index. Wholly ours. Bi-arrangement paper is a candidate *tool*, not a competing result (see H2 below). |
| PM-6 | §4 "{2,3} because K₃(ℤ)=ℤ/48"; Bernoulli/vSC fingerprint | **SAFE** | Not in Dupont. Keep as heuristic; the K-theory torsion claim is still ours (and still labeled inference in-doc). |
| PM-7 | §4 lit note: "integral-lattice synthesis appears UNWRITTEN in the literature" | **NEEDS REWORDING** | Add EMN 2510.20648 (Jan 2026): they clear denominators and prove denominator upper bounds in a Brown-program motive. Reword to: *"an integral **sharp/lattice-index** synthesis for the odd-zeta cellular families appears unwritten; the only integral denominator work in this circle (EMN 2026, Catalan) gives classical **upper** bounds at the de Rham level, not measured-sharp lattice indices."* |

### CONJECTURE.md

| # | Our claim | Verdict | Note |
|---|---|---|---|
| C-1 | The 12·D_ν(a,n)·I′ ∈ ℤζ(5)+ℤ law, sharp constant 12=2²·3, per-prime ceilings | **SAFE** | Entirely outside Dupont (denominators). No overlap. |
| C-2 | "BZ's published inclusion claims are false by exactly a factor 12" | **SAFE** | Dupont doesn't treat BZ denominators. |
| C-3 | ζ(3)-companion den(P̂ₙ) law | **SAFE** | — |
| C-4 | Interpretation: "setting ζ(2):=0 is a row op against (2πi)², integral normalization carries Bernoulli 24" | **NEEDS REWORDING (light)** | The *period normalization* `ζ(2)=−(2πi)²/24` is visible in Dupont Thm 1.3; the *integral-cost* reading is ours. Fine to cite Thm 1.3 for the period fact. |

### H2_LATTICE.md

| # | Our claim | Verdict | Note |
|---|---|---|---|
| H2-1 | Period matrix conventions, rank-3 subquotient with product period ζ₅=ζ(5)+2ζ(3)ζ(2) | **SAFE** | This is the M₀,₈ motive, provably not Dupont's (Part D). Keep; optionally add a one-line contrast: "unlike Dupont's `Z^{(n)}`, whose periods are single zetas, our weight-5 part carries the product ζ(3)ζ(2)." |
| H2-2 | H⁵(M̄₀,₈∖A, B; ℤ) integral relative-homology computation; index-2 Betti refinement | **SAFE** | Integral; Dupont ℚ-only. The bi-arrangement OS-bicomplex (1410.6348) is a candidate *tool* for the ℚ-ranks, not a done computation of the ℤ-index (see H2 below). |
| H2-3 | de Rham iterated residues all ±1 ⟹ 2-integral | **SAFE** | Ours. (Methodologically analogous to EMN's residue computation of `b_F`, worth citing as precedent for the *method*, not the result.) |
| H2-4 | §5d/§5.5 the residual B-relative 2-divisibility | **SAFE** | Open and ours. |

### TABLE.md

| # | Our claim | Verdict | Note |
|---|---|---|---|
| T-1 | ROW 2/3 "ζ(2)-slot vanishes by parity" (ζ(3), ζ(2) families) | **SUPERSEDED (as a *geometric* statement)** | **This is exactly Dupont Thm 1.2/5.5** — geometric parity vanishing via `τ:(xᵢ)↦(1/xᵢ)`, `τ.σₖ ~ (−1)^{k−1}σₖ`. Our own docs already note (line "of Theorem 1.2 … essentially already present in the literature [Riv00,BR01],[Zud04 §8]") that the *analytic* vanishing is classical, but the **geometric/motivic** interpretation we gesture at IS Dupont's theorem. Reword ROW 2/3 parity remarks to **cite Dupont Thm 1.2** for the geometric reason, and keep as ours only the *denominator/de-Rham-double-log* analysis (the `J₀=2ζ(3)` factor-2 nature), which he does not do. |
| T-2 | ROW 2 "the two 2's have different natures (Betti index vs de Rham double-log)" | **SAFE** | Denominator/lattice content; not in Dupont. The de Rham `2ζ(3)` normalization is ours; the *parity* framing around it should cite Dupont. |
| T-3 | ROW 1/5 measured sharp clearing constants, Betti-index reading | **SAFE** | Integral; not in Dupont. |
| T-4 | ROW 4 ζ(4) "printed leading 2 is spurious/slack" | **SAFE** | Not in Dupont. (Note the parallel: EMN's `2^{N+2}` is precisely such a crude 2-clearing — supports our "spurious 2" thesis; cite as corroboration.) |
| T-5 | Synthesis table "n=0 geometric period normalization is one per family" | **SAFE** | Dupont's `Z^{(n)}` periods are single zetas with clean normalization 1; ours differ by the M₀,ₙ realization. No conflict. |

### RESEARCH_PROGRAM.md

| # | Our claim | Verdict | Note |
|---|---|---|---|
| RP-1 | "The measured object is new … Nobody appears to have systematically *measured* denominators as an experimental object before" | **NEEDS REWORDING** | Keep "systematically measured as an *experimental/sharp* object" — that is defensible. But **drop any absolute "nobody works with denominators of these periods"**: EMN 2026 explicitly bound denominators of period coefficients in a Brown-program motive (Thm 8.3.1) and Rhin–Viola always tracked them. Precise safe claim: *"denominators here have only ever been given as **provable upper bounds** (Rhin–Viola; EMN 2026); the **sharp, per-prime, lattice-indexed** measurement is what is new."* |
| RP-2 | Part II "denominators are lattice phenomena; true denominator governed by de Rham denominators × index of pairing class in the integral Betti lattice" | **SAFE (novel framing)** | Dupont has the pairing `aₖ=(2πi)^{-k}∫_{σₖ}ω` (Thm 1.1) but with **rational** cycles and no lattice; the "index in the integral Betti lattice" is ours. This is the genuinely new conceptual contribution. Optionally cite Thm 1.1 as the ℚ-level ancestor of the pairing. |
| RP-3 | Part I "screening instrument prices the arithmetic side" | **SAFE** | Methodological; not in Dupont. |
| RP-4 | "Fischler's survey wishes for a geometric/motivic interpretation of the small constants" | **SAFE, strengthen** | Dupont (and EMN) are exactly the geometric-interpretation program; cite Dupont as the state of the art that stops at ℚ, positioning our integral reading as the next step. |

### paper/denominators.tex
Not yet read line-by-line in this pass. **Action:** apply the same three rewordings — (i) cite Dupont Thm 1.2 for geometric parity; (ii) cite Dupont §1.2/Thm 1.3–1.4 for the abstract extension calculus wherever the paper presents Ext-vanishing/splitting as if fresh; (iii) replace any "integral synthesis is unwritten / nobody measures denominators" with the EMN-aware sharp phrasing (RP-1). The novelty statements most at risk are exactly those three; the 12·D_ν measurement, the Betti-index reading, and the product-period distinction are safe.

---

## Part F. Answers to the five priority questions

### Q1 — Novelty audit
* **(a) mechanism / rank-3 / ℚ(−2)-splitting / E-subquotient with ζ(5) period.**
  The *abstract* extension mechanism (Ext-vanishing ⟹ split ℚ(−2); the 1-dim
  ζ(5)-extension) is **Dupont §1.2 / §2.5 / Thm 1.3–1.4** (and older Brown/DG) —
  **NEEDS REWORDING**: cite him, don't claim it. The *specific* rank-3 motive is
  **not his** (Part D: our ζ(3)ζ(2) product period rules out any subquotient of
  `Z^{(n)}`); that, and the *integral* cost of the splitting, are **SAFE/ours**.
* **(b) ROW 2/3 parity vanishing.** The **geometric** interpretation is
  **Dupont Thm 1.2/5.5** — **SUPERSEDED as geometry**; cite him. The
  denominator-nature analysis around it (de Rham double-log 2) is ours.
* **(c) "first integral measurement / integral synthesis unwritten".** Dupont is
  ℚ-linear (no denominators, no lattice). **But EMN 2026 works integrally**
  (clears denominators, proves denominator upper bounds in a Brown motive). So
  our absolute phrasing is **false as stated → NEEDS REWORDING** to: *sharp,
  per-prime, lattice-indexed* measurement is new; *upper-bound* integral work
  exists (Rhin–Viola classically; EMN 2026). Verdict: **our paper's novelty
  statements need rewriting, but the core contribution survives** re-scoped.

### Q2 — Tools for H1 (denominator control)
Dupont's own formula (Thm 1.1, `aₖ=(2πi)^{-k}∫_{σₖ}ω`) gives **no** denominator
handle — the `σₖ` have *rational* (unbounded-denominator) coefficients. **The
real H1 tool is the Zagier Appendix A**, not the motive: it computes `aₖ` as the
**partial-fraction residue `βᵣ`** of the explicit one-variable rational function
`binom(k+N−1,N−1)/((k+a₁)···(k+aₙ))` (Lemma A.1). Denominators of such
partial-fraction residues are governed by products of the differences `(aᵢ−aⱼ)`
and by `L_N = d_N` — **exactly the `d_{mᵢn}` / lcm structure in D_ν**. This is a
plausible **replacement for the Barnes-residue bookkeeping**: it is elementary,
one-dimensional, and its denominators are directly readable. **EMN Thm 8.3.1** is
a **worked template** of precisely this route (they turn the analogous residue
computation into a `2^{N+2}L_N L_{N/2}` bound). *Recommendation:* try the Zagier-
appendix βᵣ route for H1 before/instead of Barnes; it is the same arithmetic in a
cleaner variable, and EMN show it yields explicit `2^a · d_N^b` bounds. Caveat:
like EMN it will give an **upper** bound; getting our **sharp** 12 still needs the
Betti-lattice (H2) input — the appendix cannot see the lattice index.

### Q3 — Tools for H2 (the H⁵(M̄₀,₈∖A, B) lattice)
Dupont's main paper does **not** compute this — different space (his is
`(ℂ*)ⁿ∖{∏x=1}`, ours is M₀,₈), and ℚ-only. The **bi-arrangement paper
(1410.6348)** is the right-shaped tool: its Orlik–Solomon **bi-complex** computes
the relative cohomology (the "motive") of exactly a pair (arrangement complement,
sub-arrangement with coloring) — the genus of our `H⁵(M̄₀,₈∖A, B)`. **But as
published it computes the ℚ-motive / ℚ-ranks, not the ℤ-lattice index** `[READ
abstract; INFERRED body]`. So it can **shortcut the ℚ-rank and MHS bookkeeping**
of H2 (and possibly organize the boundary-sign long exact sequences that our
`H2_LATTICE §5.5` sets up by hand — Dupont explicitly offers the bicomplex as the
"systematic replacement" for such ad-hoc sequences). It would **not** by itself
deliver the integral index `γ₂/2 ∈ L`: the OS bicomplex would need an integral
refinement (combinatorially natural but not carried out in the paper) to see the
factor 2. **Recommendation:** use the OS bicomplex to get the relative-cohomology
ranks and the boundary maps cleanly, then do the ℤ-refinement (SNF over ℤ of the
bicomplex differentials) ourselves — that is the precise, finite form of the
"B-relative boundary-sign computation flagged in H2_LATTICE §5.5/CR-4."

### Q4 — The Zagier appendix vs our dual-series exclusion
The appendix proves **series↔integral compatibility**: the linear form's
coefficients computed from the integral (Thm 1.1) equal those from the series
(the `βᵣ` residues). It is a statement about **which linear form / which
coefficients**, over ℚ. It does **not** address the ζ(7)-family **sign
obstruction** (projections vs simultaneous approximations) — it has no
inequality/positivity content and no notion of "admissible direction". So it does
**not** directly bear on our dual-series *exclusion* results. Indirect value: it
gives a clean, exact re-derivation of the coefficients of any candidate dual
series, which could let us *recompute* the obstructed signs elementarily and
double-check the exclusion — a verification tool, not a resolution. **Verdict:
does not undermine or replace the dual-series exclusion; usable as a cross-check.**

### Q5 — The ζ(7) family / rank-4 cellular motive
Dupont's framework says **nothing specific** about weight-7 rank-4 **cellular**
(M₀,₁₀) motives, the (10,2,4,1,6,3,8,5,9,7) cell, or a `q₃` coefficient — his
`Z^{(7),odd)` (`gr^W = ℚ(0)⊕ℚ(−3)⊕ℚ(−5)⊕ℚ(−7)`, single-zeta periods) is again a
**different, simpler** object than the BZ M₀,₁₀ motive (whose weight-7 part
carries products, cf. ROW 5 `I′₀=(75/4)ζ(7)` and the ζ(5) rung). What *does*
transfer: (i) his **parity vanishing** (Thm 1.2) governs which coefficients are
forced to zero in any ζ(7)-type integral of the right symmetry — usable to
predict/verify vanishing rungs; (ii) the **Zagier βᵣ formula** extends verbatim
to weight 7 and gives an elementary route to the `q₃` coefficient (as a βᵣ
residue), independent of HyperInt — potentially unlocking `n≥3` where our exact
route is blocked. **Recommendation:** try the Zagier-appendix βᵣ computation for
the ζ(7) coefficients at `n=3` — it may be the cheapest path to the flagged
"n=3 unlock" for ROW 5. It will **not** by itself give the arithmetic/lattice
constant, only the exact rational coefficients (from which we then measure).

---

## Part G. Concrete edit list (report only — no docs modified)

1. **TABLE.md ROW 2/3, denominators.tex parity passage:** cite **Dupont Thm 1.2/5.5**
   for the geometric parity-vanishing; keep the de-Rham-double-log analysis as ours.
2. **PROOF_MECHANISM.md §2, denominators.tex extension passage:** cite **Dupont
   §1.2 / Thm 1.3–1.4** (and Brown/DG) for the abstract Ext-vanishing/splitting;
   present as ours only the *integral* cost and the *ζ(3)ζ(2) product* structure,
   adding one sentence that our motive is provably **not** a subquotient of
   Dupont's `Z^{(n)}` (single-zeta periods) — Part D.
3. **PROOF_MECHANISM.md §4 lit-note, RESEARCH_PROGRAM.md RP-1, denominators.tex
   novelty statements:** replace "integral synthesis unwritten / nobody measures
   denominators" with the EMN-aware phrasing: *upper-bound* integral denominator
   work exists (Rhin–Viola; **EMN arXiv:2510.20648, Jan 2026**, Thm 8.3.1); the
   **sharp, per-prime, lattice-indexed** measurement is what is new.
4. **H1 (PROOF_MECHANISM §5(i)):** add the **Zagier-appendix βᵣ route** as an
   alternative to Barnes bookkeeping, with EMN Thm 8.3.1 as the worked template.
5. **H2 (PROOF_MECHANISM §5(ii), H2_LATTICE §5.5/CR-4):** note the **OS bicomplex
   (1410.6348)** as the systematic tool for the ℚ-ranks + boundary maps, with the
   ℤ-refinement (SNF over ℤ) as our remaining step.
6. Add all four references to the bibliography: Dupont 1601.00950; Dupont
   1410.6348; EMN 2510.20648; (and note Dupont's open question on the M₀,ₙ
   relationship, which our M₀,₈/M₀,₁₀ work partially answers — a positioning win).

**Net effect on the paper's standing:** three novelty sentences must be
re-scoped (parity geometry → cite Dupont; extension calculus → cite Dupont/Brown;
"nobody integral" → cite EMN). The **substantive core is intact and, once
re-scoped, sharper**: we measure *sharp per-prime lattice indices* for the
*Brown-cellular* odd-zeta motives — objects Dupont explicitly leaves outside his
construction, and denominators EMN only upper-bound. Dupont's paper is best cited
as the **clean ℚ-linear ancestor** whose integral completion, for the cellular
families, is our contribution.
