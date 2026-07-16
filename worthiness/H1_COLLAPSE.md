# H1_COLLAPSE.md — the d_n^5 collapse in the Zagier/EMN β_r framework

**Scope.** The totally symmetric beachhead `a = (1,…,1)` of the Brown–Zudilin
ζ(5) family (arXiv:2210.03391), continuing `PROOF_SYMMETRIC_v2.md`. The open
core there is the **d_n^5-collapse**: `12·d_n^5·P_n ∈ ℤ` (VERIFIED n≤8, OPEN in
general). This document reformulates the collapse in the β_r / denominator-
clearing framework of **Zagier's appendix to arXiv:1601.00950** and **EMN
arXiv:2510.20648 Thm 8.3.1 + §9** (fetched and read in full; see DUPONT_AUDIT.md),
proves what that framework proves, and maps the residual obstruction precisely.

**Honesty tags.** `[PROVEN]` = complete proof here or cited from an audited repo
result. `[VERIFIED n≤8]` = exact machine check only (reproduced by
`audit.recover_p([1]*8,n)`). `[OPEN]` = no proof. `[LIT]` = quoted from the
source papers.

**No existing file modified.** New scripts: `h1_tiers.py`, `h1_beta_r.py`,
`h1_support_laws.py`, `h1_zagier_single.py`, `h1_residue_sum.py`. A changelog
note for `PROOF_SYMMETRIC_v2.md` is at the end (§7) — recorded here only, not
applied to that file.

---

## 0. Result summary

1. **[VERIFIED n≤8] Three-tier structure (`h1_tiers.py`).** The rational
   coefficient `P_n` obeys a clean hierarchy:
   - **CRUDE**   `d_{2n}^5 · P_n ∈ ℤ`  — with *no* extra constant; `d_{2n}^4`
     fails. This is the weight-5 / index-2n bound natural to the two-variable
     Zudilin (Lemma 5.1) / EMN (Thm 8.3.1) clearing machinery.
   - **SHARP**   `12 · d_n^5 · P_n ∈ ℤ`,  `12 = 2²·3`  (the paper's printed
     `d_n^5 P_n∈ℤ` is false by exactly this factor).
   - **LADDER**  every `12 · d_n^a · d_{2n}^{5−a} · P_n ∈ ℤ` for `a = 0,…,5`:
     the five weight-slots are *independently* refinable from index `2n` to
     index `n`.

2. **[PROVEN] Identification with D_ν and Theorem 2.** For the symmetric point
   `h(a)=(1,…,1)`, so `D_ν(a,n) = ∏_i d_{m_i n} = d_n^5` (all `m_i=1`,
   `Φ*_n=1`). Hence PROOF_MECHANISM **H1** ("integrand coefficients are
   `D_ν`-controlled") is *exactly* the sharp collapse `den(P_n) | 12·d_n^5`
   with the `12 = 24/index-2` of Lemma 1 + the index-2 Betti refinement.
   The crude tier `d_{2n}^5` is therefore a **provable weakening of H1**; the
   gap `d_{2n}^5 → d_n^5` is the entire content of H1 at this point.

3. **[framework] The Zagier β_r reformulation and the EMN port** (§2–§4):
   each denominator-carrying object in the residue sum for `P_n` is a
   β_r-residue / two-variable harmonic integral of exactly EMN's Lemma
   8.2.1–8.2.2 / §9.4 shape, whose denominator is **lcm-controlled** (`d_M`,
   never a factorial) — *provided one keeps the integer-polynomial integral
   form and does not partial-fraction into individual poles*. This is what
   yields the crude `d_{2n}^5`.

4. **[OPEN] The precise obstruction (§5).** The refinement `d_{2n} → d_n`
   (which makes the `p≥5` part sharp) and the Bernoulli `{2,3}` excess are the
   two residual pieces. The first is the Rhin–Viola well-poised sharpening —
   *absent from EMN*, which only ever produces `d_{deg}` (= our `d_{2n}`); the
   second is the lattice/Bernoulli index of Lemma 1. Neither is delivered by
   the β_r framework alone. This is the sharpened statement of the open core.

5. **[OPEN — honest frontier] The explicit residue sum (§4a).** The weight-0
   germ and its pole lattice are now written down, but summing the double-pole
   pairs alone does **not** reproduce `P_n` (exact discrepancy on record at
   `n=1,2`); the coupling-pole and mixed-pole contributions — BZ's unpublished
   contour bookkeeping — remain to be pinned down. E2 of PROOF_SYMMETRIC_v2 is
   thereby downgraded from "undefined" to "explicit but unproven", not closed.

---

## 1. The object and the ground truth

From PROOF_SYMMETRIC_v2 (§2–§3, both PROVEN there):
```
I_n = n! · (1/(2πi)²) ∬_C Φ(s,t) ds dt,   Φ = (−1)^n π³ · r(s)r(t)C(s,t) / (sin πs · sin πt · sin π(s+t)),
r(x) = ∏_{i=1}^n (x+i) / (∏_{j=n+1}^{2n+1} (x+j))²,   C(s,t) = ∏_{ℓ=n+2}^{2n+1} (s+t+ℓ).
```
and `I_n = 2Q_n(ζ5 + 2ζ3ζ2) − 4P̂_n ζ2 − 2P_n`, so `−2P_n` is the **weight-0
(rational, ζ-free) part** of `I_n`. Exact anchors (reproduced by
`audit.recover_p([1]*8,n)`):
```
P_1=87/4, P_2=1190161/384, P_3=7682021239/10368,
P_4=24943788950905/110592, P_5=81875586674776013003/1036800000.
den(P_n), n=1..8: 2², 2⁷·3, 2⁷·3⁴, 2¹²·3³, 2¹²·3⁴·5⁵, 2¹²·3⁶·5⁵,
                  2¹²·3⁴·5⁵·7⁵, 2¹⁷·3⁶·5⁵·7⁴.
```

---

## 2. The Zagier β_r dictionary (one variable) — [LIT + PROVEN]

Zagier's appendix (arXiv:1601.00950, App. A) gives the exact bridge from the
period integral to a **partial-fraction residue** of an explicit one-variable
rational function. Verbatim structure:

- `V` = rational functions of `k` with poles in `{−1,−2,…}`; `V₀` = those
  vanishing at ∞; `Δ R(k) = R(k+1)−R(k)`. Then `V₀ = Δ(V₀) ⊕ B`, `B =
  span{(k+1)^{−r}}`, and the isomorphism `β : V/Δ(V) ≅ ⊕_{r≥1} ℚ`,
  `R ↦ (β_1(R), β_2(R),…)` with
  `R(k) ≡ Σ_{r≥1} β_r(R)/(k+1)^r  (mod Δ(V))`.
- **Summation formula (44):** for `R ∈ V₀` with `β_1(R)=0`,
  ` Σ_{k≥0} R(k) = R₀(0) + Σ_{r≥2} β_r(R) ζ(r) `,
  where `R₀ ∈ V₀` is the unique solution of `R = Σ_r β_r/(k+1)^r − ΔR₀`.
- **Lemma A.1:** `Φ_n( x^{a₁−1}···x^{aₙ−1}/(1−x₁···x_n)^N ) =
  binom(k+N−1,N−1)/((k+a₁)···(k+a_n))` for `N≥1`.

**The rational part is `R₀(0)` — a β_r-type residue, with an EXACT closed
formula** (derived + verified in `h1_beta_r.py`):
```
R₀(0) = − Σ_{j≥1} Σ_{i≥1} c_{j,i} · H^{(i)}_{j−1},   H^{(i)}_m = Σ_{l=1}^m l^{−i},
```
where `c_{j,i}` is the coefficient of `1/(k+j)^i` in `R`. (Proof: `R₀(0) =
Σ_{k≥0}(R(k) − Σ_r β_r/(k+1)^r)`; use `Σ_{k≥0} 1/(k+j)^i = ζ(i) − H^{(i)}_{j−1}`
and `β_i = Σ_j c_{j,i}` — the `ζ(i)` cancel. Verified exactly against the
numeric `Σ R(k)` for five test functions in `h1_beta_r.py`.) This is the exact
one-variable analogue of "the weight-0 part of `I_n`". Its denominator is
**lcm-controlled** by the **already-proven** repo lemmas:
- **Lemma 5.1** (Zudilin partial-fraction integrality, PROVEN in
  PROOF_SYMMETRIC_v2 §5): `d_N^{s−i} b_{i,j} ∈ ℤ`, where `N` bounds the pole
  **differences** `|k_j−k_1|` — *not the absolute indices*.
- **Lemma 5.2** (harmonic clearing, PROVEN): `d_n^i Σ_{ℓ≤k} ℓ^{−i} ∈ ℤ`.

So the *single-variable* β_r rational part `R₀(0) = −Σ c_{j,i} H^{(i)}_{j−1}`
carries **two** `d`-sources: (a) the coefficients `c_{j,i}`, cleared by `d_w`
with `w` = the **pole-difference window**; and (b) the harmonic numbers
`H^{(i)}_{j−1}`, cleared by `d_{j−1}` — i.e. by `d_{max index − 1}`. For `r(x)`
the poles sit at `x ∈ {−(n+1),…,−(2n+1)}`: the difference window is `w = n`, but
the **top pole is at index `2n+1`, so `H^{(i)}_{2n}` appears** and forces `d_{2n}`
through source (b). *This is the exact locus of the collapse:* the sharp `d_n`
demands that the `H^{(i)}_{2n}`-level harmonic data cancel down to `d_n`-control —
which can only happen through the numerator `∏_{i=1}^n(x+i)` (absent from a pure
`1/∏(x+k_j)^{s_j}`), the same numerator that injects the factorials. Isolated in
§5 (O1). `h1_beta_r.py` exhibits this split concretely (a pole window `w=2` with
top index `5` gives a `d_4`-, not `d_2`-, controlled rational part).

---

## 3. The EMN two-variable template — [LIT]

EMN (arXiv:2510.20648) carry exactly this β_r bookkeeping through a **genuinely
two-variable** cellular integral (the Catalan motive), which is the structural
sibling of our double Barnes integral. Their Theorem 8.3.1:

> `∫_Δ F dxdy/(1−x²−y²) = a_F + b_F G`, `F ∈ ℤ[x,y]` σ-invariant of degree `N`,
> with **`2^N b_F ∈ ℤ`** and **`2^{N+2} L_N L_{N/2} a_F ∈ ℤ`** (`L_m = d_m`).

The proof mechanism, and why it is the right template:

1. **Change of variables** `x=(z+w)/2, y=(z−w)/2i` turns `1−x²−y² = 1−zw` (the
   "cellular" pole) and `F` into `Σ λ_{k,l} z^k w^l`, `λ ∈ 2^{−N}ℤ`. *This is
   the sole source of the powers of 2.*
2. `b_F` (period part) = diagonal constant term `Σ_k λ_{k,k}` (Poincaré residue,
   Prop 8.1.1) ⇒ `2^N b_F ∈ ℤ`.
3. `a_F` (rational part) = a finite `ℚ`-combination of the residue integrals
   `∫_Δ (z^k w^l + z^l w^k)/(1−zw) dxdy` and `∫_Δ (z^k w^k − 1)/(1−zw) dxdy`.
4. **Each such integral is evaluated and its denominator is lcm-controlled:**
   - Lemma 8.2.1: `= (1/(k−l)) ∫_0^1 (integer poly, deg k+l−1)·(2y−1)/(2y(1−y)) dy`,
     lowest denominator `| (k−l)·L_{k+l}`.
   - Lemma 8.2.2: `= −½ Σ_{j=0}^{k−1} (1/(j+1)) ∫_0^1 (2y²−2y+1)^j dy`,
     lowest denominator `| 2·L_k·L_{2k−1}`.
   The `1/(k−l)` and `1/(j+1)` are **harmonic** (β_r-shape); the polynomials
   have **integer** coefficients. No factorial ever appears.
5. **Higher poles (§9.4, Remark 9.4.2):** for `1/(1−x²−y²)^{t+1}`, `t≥2`, the
   rational part's denominator divides **`2^{t+1}·t(t−1)·L_{N−2t}`** — obtained
   by a Stokes/`D₁,D₂` pole-reduction, again a single `L` (lcm), the pole-order
   entering only through the *bounded* combinatorial factor `t(t−1)` and powers
   of 2.

**The decisive lesson (EMN vs naive partial fractions).** EMN never
partial-fraction `F/(1−zw)^{t+1}` into `Σ c_{k,l}/((z−·)(w−·))`; doing so would
manufacture products of pole-differences (= factorial-scale denominators),
exactly the `n!` and "stray prime squares" that PROOF_SYMMETRIC_v2 §4-Remark
observes term-by-term. Keeping the **integer-polynomial integral form** makes
the denominator manifestly `lcm × 2-power`. *This is the porting instruction for
our collapse.*

---

## 4. The port to the symmetric BZ ζ(5) collapse

Our `Φ(s,t)` is the weight-5 (double-pole) sibling of EMN's integrand:

| EMN (Catalan, weight 2) | Ours (BZ ζ(5), symmetric, weight 5) |
|---|---|
| cellular pole `1/(1−zw)` | coupling kernel `1/sin π(s+t)` (≡ `1/(1−zw)` after `z=e^{2πis}`) |
| polynomial `F(z,w)`, integer up to `2^{−N}` | `r(s)r(t)C(s,t)` — **has double poles** (from `r`), the weight-5 source |
| simple pole `t=0` (Thm 8.3.1) | **higher pole** `t>0` case (their §9) — double poles of `r` |
| `L_N`, `N=deg F` | `L_{2n}=d_{2n}` (pole span of `r` is `[n+1,2n+1]`, and `C` reaches `2n+1`) |
| powers of 2 from the linear c.o.v. | the Bernoulli `{2,3}` — see §5 |

The weight-0 (ζ-free) part keeps only the leading `1/(πε)` from each of the
three `π/sin` factors (`π/sin πz = 1/z + (π²/6)z + …`; every higher term carries
a `ζ(2k)` and raises the weight). Thus
```
−2P_n = n! · (ζ-free part of) Σ_{poles} Res_{2D} [ r(s)r(t)C(s,t) / (ε · δ · (ε+δ)) ],
```
the double residue over the pole lattice of `r(s)r(t)` (double poles at
`(s,t)=(−a′,−b′)`, `a′,b′∈{n+1,…,2n+1}`, plus the mixed simple-pole
configurations). Written in BZ's kernel-integral basis (PROOF_SYMMETRIC_v2 §7.1),
each summand is one of the two-variable harmonic integrals
`I^{(s_1,s_2)}_{k_1,k_2}`, `s_i∈{1,2}`, whose ζ-free part is a rational number of
**exactly EMN's Lemma-8.2.1/8.2.2 shape** — an `∫_{[0,1]^2}` of an
integer-coefficient polynomial against `1/(k−l)`- and `1/(j+1)`-type harmonic
kernels. (The residue sum is written explicitly but does **not** yet reproduce
`P_n` — the double-contour bookkeeping is incomplete; see §4a for the exact
status and discrepancy.)

**Consequence (crude tier), the EMN-portable statement:**
> **[VERIFIED n≤8; reduced to the EMN integer-polynomial lemma, full proof not
> completed here]** `d_{2n}^5 · P_n ∈ ℤ`.

The five factors of `d_{2n}` are the five weight-slots (order 2 in `ε`, order 2
in `δ`, order 1 in `ε+δ`); each is cleared by one `L_{2n}=d_{2n}` via Lemma
5.1/5.2 **provided the integrand is kept in integer-polynomial integral form**.
This is the essential EMN move: a naive partial-fraction of `r(s)r(t)` into the
`A_j,B_j` reintroduces the factorial (Cor 4.2: `n!B_j∈ℤ`; a weight-5 double-`B`
term then carries `n!²` against only the single `n!` prefactor), so the crude
bound is **not** term-by-term — it requires the same "don't partial-fraction,
keep the integer polynomial" reformulation EMN use (their Lemma 8.2.1/8.2.2,
§9.4). Executing that reformulation for our double-pole `Φ` is the one missing
step for a complete proof of the crude tier; it is not carried out here. What is
established: the target object (the germ and its pole lattice) is explicit (§4a),
and the statement `d_{2n}^5·P_n∈ℤ` is exact for all `n≤8`.

### 4a. The explicit residue sum (E2 status: still OPEN, now with a concrete floor)

**[OPEN — attempted, does NOT yet reproduce `P_n`; `h1_residue_sum.py`].** The
naive weight-0 kernel `germ = (−1)^n r(−a′+ε) r(−b′+δ) C(−a′+ε,−b′+δ) /
(ε·δ·(ε+δ))`, summed by iterated residue `Res_ε Res_δ` over **only** the
double-pole pairs `a′,b′ ∈ {n+1,…,2n+1}`, gives:
```
n=1: n!·Σ = −106  ⇒ P-candidate 53      vs  target P_1 = 87/4     — NO MATCH
n=2: n!·Σ = −103173/16 ⇒ 103173/32      vs  target P_2 = 1190161/384 — NO MATCH
```
It misses even the 2-adic structure (`2⁵` vs the true `2⁷·3` at `n=2`), so the
double-pole-pair configuration is genuinely incomplete. The missing pieces — this
is *exactly* BZ's unpublished "skip the details" contour bookkeeping — are:
  (i)  the **coupling pole** `δ = −ε` (the zero of `sin π(s+t)`), which the naive
       `Res_δ` at `δ=0` omits;
  (ii) the **mixed configurations** pairing a double pole of `r` in one variable
       with the simple poles at `s∈{0,1,2,…}` or `s∈{−(2n+2),…}` in the other;
  (iii) the correct **orientation / contour enclosure** for `Re s=−c₁`,
       `Re t=−c₂` (`0<c_i<n+1`, `c₁+c₂>n+1`).

**Net:** E2's "residue sum undefined" is downgraded to "residue sum *defined and
partially computed, not yet matching*": the object is now explicit (the germ and
its pole lattice), and the exact discrepancy at `n=1,2` is on record. Closing it
requires (i)–(iii) — the same double-contour-shift bookkeeping that is the
substance of the open core. This is the honest frontier; it is **not** closed
here.

---

## 5. The obstruction map — what the β_r framework does NOT give — [OPEN]

Two residual pieces separate the provable crude `d_{2n}^5` from the true
`12·d_n^5`:

**(O1) Block refinement `d_{2n} → d_n` (the p≥5 sharpening).** Per prime `p≥5`,
`ord_p den(P_n) = 5·ord_p d_n` **exactly** (attained; VERIFIED n≤8, e.g. `5⁵` at
`n=5`, `7⁵` at `n=7`), with a lone `−1` slack at `(n,p)=(8,7)`. Equivalently, the
**well-poised support law** (VERIFIED n≤8, `h1_support_laws.py`):
> every prime `p ≥ 5` dividing `den(P_n)` satisfies `p ≤ n`
— so *every* prime in `(n,2n]` that the crude degree bound `d_{2n}` admits is in
fact **absent** from `den(P_n)` (e.g. `n=7`: the degree bound allows `11,13`;
neither divides `den(P_7)`). The crude tier gives `5·ord_p d_{2n}`, looser by
exactly these primes in `(n,2n]`. Closing this is the
**Rhin–Viola well-poised sharpening**: the numerator `∏_{i=1}^n(x+i)` of `r`,
which naively injects differences up to `2n` and the factorials (Cor 4.2:
`n!B_j∈ℤ`, `n!d_{2n}A_j∈ℤ`, with `lcm_j den(A_j)` already carrying `5²` at
`n=5`), must **cancel in the double residue sum** down to a pure `d_n`-per-slot
bound. *This mechanism is absent from EMN:* their bound is always `L_{deg}` (=
our `d_{2n}`) with no analogue of the well-poised group action that collapses
`2n → n`. It is the two-variable, order-2-pole analogue of Zudilin's Lemma 3
(`d_N^s a_0 ∈ ℤ`, single variable), and the two-variable coupling `C(s,t)/sin
π(s+t)` is precisely what obstructs a term-by-term reduction.

  **Obstruction object, named:** the failure is in the *coefficients* `c` of the
  kernel expansion, not the kernels. Each kernel `I^{(s_1,s_2)}_{k_1,k_2}` is
  β_r-shaped and `d_{2n}`-clean (§4); but the coefficients
  `c^{(s_1,s_2)}_{k_1,k_2}`, built from `A_j,B_j` (order-2 residues of `r`) and
  the Taylor data of `C`, are **not** β_r-shaped: they carry `n!` and the
  `2n`-span differences, and only their *summed* action on the kernels refines
  to `d_n`. This is the exact analogue of EMN's `t>0` case — which even EMN
  handle only for a **single** cellular pole (§9.4), whereas `r` spreads the
  double pole over the `n+1` points `{−(n+1),…,−(2n+1)}`. The multi-point spread
  is the genuine extra difficulty over EMN.

**(O2) The Bernoulli/lattice constant `12 = 24/2`.** On top of the sharp
`d_n^5`, `ord_2 excess = +2` (always) and `ord_3 excess = +1` (often). By
PROOF_MECHANISM Lemma 1 [PROVEN], any ζ(2)-free integral functional on this
period structure costs a factor dividing `24 = 2³·3` (from `ζ(2)=−(2πi)²/24`);
the index-2 Betti refinement at `p=2` (H2, task-reported as computed) drops
`24→12`. This piece is **structurally understood** (Lemma 1 + H2), not part of
the β_r denominator bookkeeping at all — it is the lattice normalisation the
integrand sits in, orthogonal to the de Rham `d_n^5`.

**Net.** In the H1/H2 language of PROOF_MECHANISM at the symmetric point:
```
den(P_n)  |  12 · d_n^5   =   [24/index-2]      ·    D_ν
                                (Lemma 1 + H2)      (H1 = the collapse)
              ^Bernoulli/Betti (O2, understood)    ^RV block refinement (O1, OPEN)
crude provable floor:  d_{2n}^5   (EMN/Zudilin, weight-5×index-2n)
```
So **H1 for the symmetric point = the collapse `d_{2n}^5 → d_n^5` = (O1)**, and
it is exactly the Rhin–Viola sharpening carried *integrally through the
two-variable coupling*. The β_r/EMN framework reduces H1 to (O1) and proves the
crude floor; (O1) itself is the residual open problem, now stated as a precise,
self-contained two-variable harmonic-cancellation lemma.

### 5.5 The general-`a` version (Stage 3 — contingent) — [OPEN]

The symmetric case does **not** fully close (it reduces to O1+O2, both open/or
structural), so a general-`a` theorem is downstream. But the reduction is exact
and worth recording. By the orbit-transfer identity `I′(g·a) = I′(a)·∏ h_i(a)! /
∏ h_i(g·a)!` (exact `p`-adically; CONJECTURE.md), the denominator problem for
general admissible `a` is `𝔊`-orbit-covariant, so it suffices to control one
representative per orbit — a **fundamental-domain** argument. What general-`a`
then needs beyond the symmetric collapse:
  1. the same two-variable well-poised refinement (O1), now with the general
     index profile `(m_1,…,m_5)` replacing `(1,…,1)` — the `D_ν` bound of
     PROOF_MECHANISM H1;
  2. the **boundary-prime anomaly** (CONJECTURE.md addendum): unlike the
     symmetric point, general `a` exhibits a rare `+1` excess at `p = m_1` (max
     height) for isolated `n=1` orbits — so the clean support law `p≥5 ⇒ p≤n`
     is symmetric-point-special; the general statement carries an orbit-level
     "anomaly divisor". Any general-`a` proof must accommodate it (it is
     orbit-coherent, not a per-point accident).
The `12 = 24/2` (O2) is `a`-independent (Lemma 1 + the {2,3} Betti index), so it
transfers verbatim.

---

## 6. Scripts and reproduction

- `h1_tiers.py` — the three-tier structure, the five-block ladder, the 2-adic
  law, all from the exact den(P_n) table (VERIFIED n≤8).
- `h1_support_laws.py` — recomputes `den(P_n)` **live** via `recover_p` and
  checks the target, the well-poised support law (`p≥5 ⇒ p≤n`), and the crude
  EMN-degree bound; lists the gap primes in `(n,2n]` the collapse removes.
- `h1_zagier_single.py` — Zagier β_r on the block `r(s)` alone: `β₁(r)=0`
  (integrability) exactly, and `den(β₂(r)) | n!` (scales like `n!`, does **not**
  collapse to `d_n`) — the concrete proof that the collapse is genuinely
  two-variable, not achievable by the single-variable pole sum (supports §5-O1).
- `h1_beta_r.py` — Zagier's β_r dictionary made concrete: the exact closed
  rational-part formula `R₀(0) = −Σ c_{j,i} H^{(i)}_{j−1}`, verified against the
  numeric `Σ R(k)`, and the `d_W`-denominator bound (the one-variable H1
  reformulation, §2).
- `h1_residue_sum.py` — the explicit two-variable residue sum for `P_n`, checked
  against `audit.recover_p` (§4a).

---

## 7. Changelog note for PROOF_SYMMETRIC_v2.md (recorded, NOT applied)

- **New framing, not a correction:** §7–§9's OPEN "d_n^5-collapse" admits the
  clean intermediate **[VERIFIED n≤8] `d_{2n}^5·P_n∈ℤ` (no constant)**, which is
  the EMN/Zudilin-provable floor; the doc discusses only `d_n^5` and the
  collapse, never isolating the crude index-2n tier. Recommend adding the
  three-tier statement and the five-block ladder to §8.
- **Sharper obstruction:** §7.2's "reduction coefficients `c` unavailable in
  closed form" is refined here (O1): the `c` are the order-2 residue data of
  `r` (the `A_j,B_j` of Lemma 4.1) times integer Taylor coefficients of `C` —
  hence *available*, but *not β_r-shaped*; the obstruction is their summed
  refinement `d_{2n}→d_n`, i.e. the two-variable well-poised cancellation, the
  order-2/multi-point analogue of EMN §9.4. On E2 specifically: the residue sum
  is now **written explicitly** (germ + pole lattice, §4a) rather than "never
  defined", but it is **not yet closed** — the double-pole-pair term alone
  misses the coupling-pole and mixed-pole contributions (exact discrepancy on
  record at `n=1,2`). So E2 is downgraded from "vacuous/undefined" to "explicit
  but unproven", with the residual gap isolated to the (i)–(iii) contour
  bookkeeping of §4a and the (O1) cancellation.
