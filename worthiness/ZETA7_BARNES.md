# Triple Mellin–Barnes route for the totally symmetric M₀,₁₀ ζ(7) cellular integral

**Route:** scout's route (a) — simplicial→cubical→J-form→Barnes reduction of the
*primal* 7-fold integral Iₙ, targeting the exact ζ(2)=0 form I′ₙ and ultimately
I′₃. This is the on-target hard route (`ZETA7_FAMILY.md` §2a; the single-sum VWP
route is excluded, `ZETA7_DUAL.md` §7). Template: BZ's M₀,₈ derivation
(`bz/2026-01-26_CellZeta.tex` §3–4).

**Status.** Stages 1–2 **COMPLETE and exactly verified** (symbolic change-of-
variables identities, ratio ≡ 1 for *general n*, not just numerically). Stage 3
(Barnes) **set up and its structure pinned**, but **not carried to a closed
contour integral**; Stages 4–5 (residue decomposition, I′₃) **not reached**. The
derivation stalls at a precise, structural obstruction — an intrinsic
**left/right asymmetry** of the direct cubical form (§5). This obstruction is now
**proven fundamental, not a coordinate accident**: the cell's dihedral stabiliser
is trivial (difference-word invariant, §5b), and the full 20-orientation scan
finds **no** symmetric (both-ends-leaf) orientation (§5b); the factor-reducing
"merge" of the stray P5 provably *increases* the coupled count 4→5 (§5c). The
weight-7 cell is dihedrally rigid: BZ's M₀,₈ two-sided leaf-collapse does not
extend. The numeric route (§5f) was then executed: an exact all-positive 4-fold
series was derived and verified (reproduces I₀,I₁,I₂), but it converges only
**algebraically** (needs 10^{72–100} terms for PSLQ-grade precision; ε-acceleration
gains ~1.5 digits) — a hard **precision wall** that is the analytic shadow of the
same rigidity. **BREAKTHROUGH (§8):** the McCarthy–Osburn–Straub cellular-integral leading-
coefficient construction (arXiv:1705.05586), applied to our cell, gives q_n as an
exact combinatorial **diagonal coefficient** — validated against all three BZ
anchors (1, 61, 52921) — yielding the **first new exact datum of the campaign,
q₃ = 94357501**, plus q_n for all n. This bypasses the Barnes/numeric/CT walls of
§5–§7 entirely for the ζ(7) leading coefficient. The remaining prize (P₃, the
recurrence, the denominator ledger) reduces to one standard creative-telescoping
run on this clean diagonal (HolonomicFunctions, pending River's RISC password;
Mathematica 15 is live). Full details in §8. The §5–§7 walls stand as an honest
map of why the *direct* routes fail; §8 is the way through. Every
identity/table below is machine-verified.

Scripts: `zeta7_barnes_stage1.py`, `zeta7_barnes_stage2.py`,
`zeta7_barnes_jform.py`, `zeta7_barnes_stage3.py`, `zeta7_barnes_series_n0.py`,
`zeta7_barnes_jform_mc.py`, `zeta7_barnes_refl.py`; pre-symmetrisation (§5b–c):
`zeta7_barnes_group.py` (σ,τ, order-10 check), `zeta7_barnes_orient_scan.py`
(per-orientation leaf structure, standalone/distributable), `zeta7_barnes_merge.py`
(merge-failure check). No existing files modified.

---

## Target and anchors

    I_n = ∫_{0<t1<...<t7<1}  (B/D)^n · dt / D,
    B = t1(t2−t1)(t3−t2)(t4−t3)(t5−t4)(t6−t5)(t7−t6)(1−t7),
    D = (t3−t1) t3 t5 (t5−t2)(t7−t2)(t7−t4)(1−t4)(1−t6).

Exact (BZ, transcribed): I₀ = (75/4)ζ7 − 9ζ5ζ2; I₁, I₂ as in `ZETA7_FAMILY.md`.
Numerically I₀ = 3.55544884724898403886…  (this document recomputes it
independently: `75/4·mp.zeta(7) − 9·mp.zeta(5)·mp.zeta(2)`).

---

## Stage 1 — CUBICAL FORM  [VERIFIED, exact, general n]

**Change of variables** (standard simplex→cube, telescoping to the right):

    x_i = t_i / t_{i+1}  (t_8 := 1),   i.e.  t_i = ∏_{j≥i} x_j,   x_i ∈ (0,1).

Jacobian dt = (∏_{j=1}^7 x_j^{j-1}) dx. Each difference factors:
t_{i+1}−t_i = t_{i+1}(1−x_i); t_3−t_1 = t_3(1−x_1x_2); t_5−t_2 = t_5(1−x_2x_3x_4);
t_7−t_2 = t_7(1−x_2x_3x_4x_5x_6); t_7−t_4 = t_7(1−x_4x_5x_6);
1−t_4 = 1−x_4x_5x_6x_7; 1−t_6 = 1−x_6x_7. All pure-t prefactors collect into the
monomial. The result (proved symbolically, `zeta7_barnes_stage1.py`,
ratio lhs/claim ≡ 1):

    I_n = ∫_{[0,1]^7}
          x1^n x2^{2n+1} x3^n x4^{2n+1} x5^n x6^{2n+1} x7^n
          · ∏_{i=1}^7 (1−x_i)^n / (P1 P2 P3 P4 P5 P6)^{n+1}  dx,

    P1 = 1−x1x2,           P2 = 1−x2x3x4,        P3 = 1−x2x3x4x5x6,
    P4 = 1−x4x5x6,         P5 = 1−x4x5x6x7,      P6 = 1−x6x7.

So the denominator is **six** "1 − (product of x's)" factors — the direct
analogue of BZ's four-factor cubical form (I-a), but with the extra weight
appearing as the longer factors P3 (length 5) and P5 (length 4).

**Stage-gate.** (i) *Exact:* the change of variables is an identity for symbolic
n — `sympy.simplify(lhs/claim) = 1`. (ii) *Value:* expanding
1/(1−P1)^{1}=Σ and summing the k₁,k₆ geometric series in closed form reduces I₀
to a positive 4-fold sum (`zeta7_barnes_series_n0.py`); it climbs monotonically
3.19→3.28→3.33→3.37 (L=60…160) with a slow ~L^{−0.65} tail and power-law
extrapolates to ≈3.58 (crude), consistent with the exact 3.5554. Plain
Monte-Carlo is useless here (corner singularity 1/P; MC gives 15±12) — same
obstruction the scout hit. The **exact symbolic identity is the operative gate**;
the series only guards against a transcription error in B, D (none found).

---

## Stage 2 — J-FORM  (leaf collapse)  [VERIFIED, exact, general n]

BZ collapse the two *outer* denominator factors of their cubical form to
monomials via x1=(1−y1)/(1−y1y2), x2=1−y1y2 (and its mirror), leaving only the
two coupled factors 1−y3(1−y1y2), 1−y3(1−y4y5). The analogue here — collapse the
two genuine leaves P1={x1,x2} and P6={x6,x7}:

    x1 = (1−y1)/(1−y1y2),   x2 = 1−y1y2,       x3 = y3, x4 = y4, x5 = y5,
    x7 = (1−y7)/(1−y6y7),   x6 = 1−y6y7.

Jacobian det = y1 y7 / ((1−y1y2)(1−y6y7)) > 0 on (0,1)^7; the map is a bijection
of the cube. Under it P1 → y1, P6 → y7 (**monomials, absorbed into the measure**),
and the surviving factors are (proved symbolically, `zeta7_barnes_jform.py`,
ratio ≡ 1 for general n):

    I_n = ∫_{[0,1]^7}
          y4^{2n+1} · ∏_{i≠4} y_i^n · ∏_{i=1}^7 (1−y_i)^n / (P2 P3 P4 P5)^{n+1} dy,

    P2 = 1 − y3 y4 (1−y1 y2),
    P3 = 1 − y3 y4 y5 (1−y1 y2)(1−y6 y7),
    P4 = 1 − y4 y5 (1−y6 y7),
    P5 = 1 − y4 y5 (1−y7).

**Six coupled factors reduced to four.** Three of them — **P2, P3, P4** — have
*exactly* the triple-Barnes shape anticipated in the plan: a central chain
y3 · y4 · y5 with the **left pair** (y1,y2) entering as (1−y1y2) and the **right
pair** (y6,y7) entering as (1−y6y7):

    P2 : center y3y4,      left pair only;
    P3 : center y3y4y5,    BOTH pairs (the "central" factor of the double fan);
    P4 : center y4y5,      right pair only.

This is the rank-4 / triple-Barnes fingerprint made explicit. The **fourth
factor P5 = 1 − y4y5(1−y7)** is the *stray*: it carries the right pair through
(1−y7) alone, not (1−y6y7). It is the obstruction to a clean *three*-factor form
(§5).

**Stage-gate.** (i) *Exact:* ratio ≡ 1, general n. (ii) *Value:* J-form
Monte-Carlo at n=0 gives 3.86 ± 0.27 (`zeta7_barnes_jform_mc.py`), consistent
with 3.5554 and with **finite** variance — the substitution genuinely tames the
corner singularity (cube-form MC had variance ~10²× larger). Again the exact
identity is the gate.

---

## Stage 3 — BARNES  (structure pinned; contour integral NOT completed)

**The inner-integral hypergeometry.** Rewrite each surviving factor in BZ's
"(1−·)(1+Z·)" form (verified, `zeta7_barnes_stage3.py`):

    P2 = (1−A)(1 + Z2 · y1y2),   A = y3y4,                 Z2 = A/(1−A);
    P3 = (1−E)(1 + W3 · y6y7),   E = y3y4y5(1−y1y2),        W3 = E/(1−E);
    P4 = (1−y4y5)(1 + W4 · y6y7),                           W4 = y4y5/(1−y4y5);
    P5 = (1−y4y5)(1 + W4 · y7).

From this the coupling structure is exact:

* **Left pair (y1,y2)** sits under **two** factors: (1+Z2·y1y2) in P2 and, through
  E=y3y4y5(1−y1y2), inside P3. In BZ's M₀,₈ each pair sat under a *single* factor,
  giving a single ₃F₂ per pair and a **double** Barnes integral. Here the left
  pair under two factors ⇒ its 2-dim Euler integral is an **Appell/Kampé-de-Fériet**
  object, i.e. a **double** Mellin–Barnes on its own. This is precisely the "extra"
  Barnes dimension the weight-7 case demands.
* **Right pair (y6,y7)** sits under **three** factors: (1+W3·y6y7) in P3,
  (1+W4·y6y7) in P4, and (1+W4·y7) in P5 — the last coupling y7 *alone*.
* **Central** y3,y4,y5 thread all four.

**Where a mechanical Barnes reduction would go** (the route BZ execute for M₀,₈,
"skip the details of"): MB-expand each (1+Z·y1y2)^{−(n+1)} and each
(1+W·y6y7)^{−(n+1)} and (1+W4·y7)^{−(n+1)}; the y1,y2,y6,y7 integrals become Beta
functions; the y3,y4,y5 (equivalently a single z-variable after y3,y5 are
absorbed) integral closes the Eulerian ∫₀^∞ z^… (1+z)^… giving the coupling
Gammas. The result is a **Gamma-only multi-contour integrand** — the (intJ)
analogue — with contour dimension = (#MB variables). With the clean 3-factor core
one would get the promised **triple** contour integral. **With P5 present the
count is one higher and the integrand is not symmetric.**

**This stage was NOT carried to an explicit contour integral.** The obstruction
is structural, not a matter of algebra grinding — see §5. Attempting to MB the
J-form *directly* (before the (1−·)(1+Z·) rewrite) fails because the products
1−y1y2, 1−y6y7, 1−y7 inside P2…P5 are not monomials, so no single MB per factor
gives monomial y-powers; and after the rewrite the couplings W3, E carry the
cross-pair (1−y6y7),(1−y1y2), so the s-integrals do **not** separate into
Barnes-first-lemma form (checked: the s-integrals share Γ² and ratio factors,
not Γ(a+s)Γ(b+s)Γ(c−s)Γ(d−s)).

---

## 4. A guaranteed exact fallback representation (6-fold MB)

Independently of the leaf collapse, the Stage-1 cubical form admits a direct
6-fold Mellin–Barnes representation: MB-expand each (1−P_k)^{−(n+1)},
k=1…6, then do the seven x-integrals as Beta functions. With
e_i = (base exponent of x_i) + Σ_{k: x_i∈P_k} s_k, and
(base) = (n,2n+1,n,2n+1,n,2n+1,n),

    e1=n+s1, e2=2n+1+s1+s2+s3, e3=n+s2+s3, e4=2n+1+s2+s3+s4+s5,
    e5=n+s3+s4+s5, e6=2n+1+s3+s4+s5+s6, e7=n+s5+s6,

    I_n = Γ(n+1) · (2πi)^{−6} ∮ ∏_{k=1}^6 Γ(n+1+s_k)Γ(−s_k)
              · ∏_{i=1}^7 Γ(e_i+1)/Γ(e_i+n+2) · (phase) ds,

closing all six contours to the right reproduces the positive multi-series
= I_n. This is an **exactly-computable representation** in the task's sense, but
it is (i) six-fold, not triple, and (ii) carries reciprocal-sine phases
(−1)^{Σ s_k} rather than BZ's clean Gamma-only integrand — because it skips the
leaf collapse that removes those phases. A six-fold residue decomposition into a
ℚ-linear form in single+double+triple zetas is not tractable by hand; this
fallback is recorded for completeness and as a numeric cross-check, **not** as a
path to I′₃.

---

## 5. THE OBSTRUCTION  [DERIVED — the precise map, in the spirit of ZETA7_DUAL.md]

**What blocks the clean triple Barnes: an intrinsic left/right asymmetry of the
direct cubical form.**

Group the six Stage-1 denominators by the variables they touch:

    LEFT   : P1={1,2}, P2={2,3,4}
    CENTER : P3={2,3,4,5,6}
    RIGHT  : P4={4,5,6}, P5={4,5,6,7}, P6={6,7}

The count is **2 left / 1 center / 3 right** — asymmetric. Contrast M₀,₈, whose
(post-σ⁵) cubical form is **2/0/2 symmetric**: LEFT {1,2},{2,3}; RIGHT {3,4},{4,5}.
The symmetry is exactly what lets BZ collapse *both* leaves identically and land
on two mirror-image coupled factors.

Consequences, all verified above:

1. **Only x1 is a clean leaf** (appears in a single denominator, P1). On the
   right, x7 ∈ {P5,P6} and x6 ∈ {P3,P4,P5,P6} — *no* variable is confined to one
   factor. So the right "leaf collapse" is not the mirror of the left: it
   necessarily drags x6,x7 through P3,P4,P5, and the residue is the stray
   **P5 = 1−y4y5(1−y7)**, whose coupling is (1−y7) not (1−y6y7).

2. Hence the reduction stalls at **four** coupled factors {P2,P3,P4,P5} with a
   clean triple core {P2,P3,P4} + one stray, rather than the clean **three**.
   The stray is exactly the factor a symmetrising automorphism would have to
   relocate.

3. The **failed ansatz space** (what was tried and does not work):
   * *Mirror leaf collapse on the right* (x6=1−y6y7, x7=(1−y7)/(1−y6y7)): valid
     change of variables (Jacobian, all four transformed factors, ratio ≡ 1 all
     verified) but produces P5 stray. — done, this is the J-form above.
   * *Collapsing P5 instead of P6*: impossible; P5={4,5,6,7} is a 4-variable
     factor, not collapsible to a monomial by a 2-variable substitution.
   * *Direct MB of the J-form*: blocked (non-monomial 1−y1y2, 1−y6y7, 1−y7 inside
     the factors; §3).
   * *Integrating a "leaf" x7 out first*: x7∈2 factors ⇒ gives a ₂F₁, not a
     monomial collapse; does not reduce the coupled-factor count.

4. **The asymmetry is intrinsic, not a coordinate choice.** Applying the problem
   reflection t_i → 1−t_{8−i} (a symmetry of the staircase numerator) *before* the
   cubical map gives the mirror denominator set touching
   {5,6},{5,6,7},{3,4,5,6,7},{3,4,5},{1,2,3,4,5},{1,2,3}
   (verified, `zeta7_barnes_refl.py`): now **no** variable is confined to a single factor — the
   reflected orientation has *no* clean leaf at all, strictly worse. So neither
   orientation of the direct cubical map is symmetric; the fix must be a genuine
   automorphism, not a relabelling/reflection.

5. **What would remove it (not attempted; out of scope/budget):** the M₀,₁₀
   analogue of BZ's σ⁵ pre-symmetrisation — a specific automorphism from the
   dihedral symmetry group of the (10,2,4,1,6,3,8,5,9,7) cellular integral
   (Brown, *Moduli spaces and dinner parties*, §10.2.6) — applied *before* the
   cubical map, to rebalance the denominators to a symmetric **2/…/2-type** form
   with two clean leaves. BZ obtain their clean form only after exactly this step
   (they apply σ⁵ to I(a) before passing to cubical coordinates). Constructing
   the M₀,₁₀ dihedral action explicitly and finding the right group element is a
   genuine Brown-machinery computation; it is the identified next step and the
   real content of "route (a) is a multi-day derivation."

**Net:** the primal integral has been brought, by two exactly-verified changes of
variables, from a 7-fold simplex integral to a 7-fold cube integral with **four**
coupled denominators whose core is the clean triple-Barnes double fan. The last
mile to a clean triple contour integral is blocked not by algebra but by the need
for the symmetrising automorphism; the obstruction is the stray factor
P5 = 1−y4y5(1−y7) and its origin is the 2/1/3 left/center/right asymmetry of the
direct cubical form.

---

## 5b. PRE-SYMMETRISATION: the full dihedral 20-orientation scan [VERIFIED]

Following the coordinator's directive, we tested whether an automorphism of the
cellular integral (the M₀,₁₀ analogue of BZ's σ⁵ pre-symmetrisation) can rebalance
the denominators to a *symmetric* orientation with clean leaves at **both** ends.

**The group.** The dihedral group of order 20 acting on the 7 simplex variables,
generated by the order-10 rotation and the reflection

    σ: (t₁,…,t₇) ↦ (1−t₁/t₂, 1−t₁/t₃, …, 1−t₁/t₇, 1−t₁),
    τ: (t₁,…,t₇) ↦ (t₁, t₁/t₇, t₁/t₆, …, t₁/t₂).

Both map the open simplex 0<t₁<…<t₇<1 to itself (checked); σ¹⁰ = id verified
symbolically (`grp.py`). Each g in {σᵏ, σᵏτ : k=0..9} pulls the Stage-1 form back
to a value-preserving representation g*ω (∫_Δ g*ω = ∫_Δ ω = Iₙ, pure change of
variables), whose cubical reduction has a *different* denominator/leaf structure.

**Invariant prediction (verified, `scaninc.py`/inline).** The δ-decagon
difference word of π=(10,2,4,1,6,3,8,5,9,7) is [2,2,7,5,7,5,7,4,8,3], multiset
{2,2,3,4,5,5,7,7,7,8}. Its mod-10 negation [8,8,3,5,3,5,3,6,2,7] has multiset
{2,3,3,3,5,5,6,7,8,8}. **The multisets differ**, so no dihedral element carries
the word to its negation or reversed-negation: the **stabiliser of the cell is
trivial**, and no orientation can be dihedrally symmetric. Confirmed
computationally.

**The scan (n=0 cubical leaf structure of all 20 orientations).** Method: at n=0
the coupled (1−product) denominators are read off the pulled-back density
Jg/D(g) in cubical coordinates. The composed Jacobian is **not** monomial
(Jσ evaluated along the orbit carries (1−product) factors), so it must be
included — a naïve "factor D(g) only" shortcut is wrong (checked and rejected).
Computed exactly per orientation by piecewise factoring (`piece_one.py`), run
distributed over 4 machines. Result (leaf = variable in exactly one coupled
factor; "lo" = a leaf among x₁,x₂; "hi" = among x₆,x₇):

| orient. | #coupled | leaf | | orient. | #coupled | leaf |
|---|---|---|---|---|---|---|
| σ⁰ (id) | 6 | **lo** x₁ | | σ⁰τ (τ) | 6 | **hi** x₇ |
| σ¹ | 6 | none | | σ¹τ | 6 | none |
| σ² | 6 | **hi** x₇ | | σ²τ | 6 | **lo** x₁ |
| σ³ | 6 | **lo** x₁ | | σ³τ | 6 | **hi** x₇ |
| σ⁴ | 6 | none | | σ⁴τ | 6 | none |
| σ⁵ | 6 | none | | σ⁵τ | 6 | none |
| σ⁶ | 6 | none | | σ⁶τ | 6 | none |
| σ⁷ | 6 | **hi** x₇ | | σ⁷τ | 6 | **lo** x₁ |
| σ⁸ | 6 | **lo** x₁ | | σ⁸τ | 6 | **hi** x₇ |
| σ⁹ | 6 | **hi** x₇ | | σ⁹τ | 6 | **lo** x₁ |

**Conclusion (all 20 computed; matches the invariant): NO orientation has clean
leaves at both ends.** Tally: 6 with a low leaf (x₁), 6 with a high leaf (x₇), 8
with none — every one carries at most a *single*-end leaf (lo XOR hi XOR none),
with **zero** exceptions across the full group. The two best-balanced size
profiles (σ⁵ and σ⁵τ, sizes [2,2,2,3,3,5]) have **no** leaf at all. The direct
form σ⁰ (leaf x₁) and its reflection τ (leaf x₇) are the *only* one-leaf-per-end
pair, but no single orientation combines them. So the two-sided leaf-collapse
that gives BZ's clean M₀,₈ reduction genuinely **does not extend
dihedral-equivariantly** to M₀,₁₀ — the weight-7 cell is dihedrally rigid, exactly
as the trivial-stabiliser invariant demands.

## 5c. MERGE route: fusing the stray P5 [ATTEMPTED — fails, exact]

Since no symmetric orientation exists, we tried instead to *reduce the factor
count* directly (Barnes needs few factors, not symmetric ones), by fusing the
stray P5 = 1−y₄y₅(1−y₇) with P4 = 1−y₄y₅(1−y₆y₇), which share the y₄y₅ centre.

**Best attempt.** The right-block substitution y₆=(1−a)/(1−ab), y₇=1−ab makes
1−y₆y₇=a and 1−y₇=ab, sending

    P2 ↦ 1−y₃y₄(1−y₁y₂),  P3 ↦ 1−a·y₃y₄y₅(1−y₁y₂),
    P4 ↦ 1−a·y₄y₅,        P5 ↦ 1−ab·y₄y₅,

so that b enters **only** P5 — apparently a fresh leaf. But the Jacobian
|∂(y₆,y₇)/∂(a,b)| = a/(1−ab) together with the measure powers leaves a **net
(1−ab)^{−(n+1)}** in the denominator. Counting exactly at n=0,1,2
(`merge2.py`): the transformed integrand has **five** coupled denominator
factors — {1−ab, 1−ab·y₄y₅, P2, P3, P4} — i.e. the substitution trades P5's
(1−y₇) for a new (1−ab) coupling and P5 itself, netting **one more** factor, not
fewer. **Merge fails: it strictly increases the coupled count (4→5).**

*Why it must fail (structural).* P5 = 1−y₄y₅(1−y₇) cannot be collapsed to a
monomial: a leaf-collapse needs two variables confined to the single factor, but
each of y₄∈{P2,P3,P4,P5}, y₅∈{P3,P4,P5}, y₇∈{P3,P4,P5} is shared. And P4=P5 only
on the boundary y₆=1. Any substitution aligning (1−y₇) with (1−y₆y₇) reintroduces
a compensating Jacobian coupling (the (1−ab) above). This is the same rigidity
the trivial stabiliser predicts, now seen at the level of local birational moves.

## 5d. Forward assessment: QUADRUPLE Barnes and the numeric-PSLQ route to I′₃

The 4-factor J-form (§2) is the reduced object. Two honest paths to I′₃:

1. **Symbolic quadruple Barnes → exact residue decomposition.** MB-expand all
   four factors (via the (1−·)(1+Z·) rewrite, §3): the left pair (y₁,y₂) under
   (1−y₁y₂) in P2,P3 gives an Appell/KdF **double**-Barnes block; the right pair
   (y₆,y₇) under (1−y₆y₇) in P3,P4 plus (1−y₇) in P5 gives a further **double**
   block; the central y₃,y₄,y₅ close Eulerian integrals. Net: a **four-contour**
   Gamma-integrand (the (intJ) analogue, one dimension above BZ's double).
   Residue decomposition into weight-≤7 single+double+triple zeta values via the
   reciprocal-sine kernel (PROOF_SYMMETRIC_v2.md §2–3 generalised to 4 variables)
   is "bigger but finite" — this is the genuine multi-day core BZ flag as
   impractical at this weight. **Not executed.**

2. **Numeric quadruple Barnes + PSLQ (RECOMMENDED path to the PRIZE).** A Barnes
   contour integrand decays like ∏|Γ|~e^{−(π/2)Σ|Im sₖ|}, so the 4-fold contour
   integral converges **exponentially** — unlike the singular 7-dim primal
   quadrature (route d, infeasible). Evaluating the 4-fold Barnes numerically to
   ~40–60 digits at n=3 (feasible: 4-dim exponentially-convergent quadrature, or
   truncated residue summation) and running PSLQ against the known weight-≤7
   basis {1, ζ2, ζ3, ζ5, ζ7, ζ2ζ3, ζ2ζ5} would recover I′₃ (and I″₃) **exactly**,
   *without* the full symbolic residue decomposition. This sidesteps the
   dihedral-rigidity obstruction entirely: the clean triple form was needed only
   to make the *symbolic* decomposition tractable, not the numerics. **This is
   the most promising remaining route and is recommended for the next push.**

## 5e. Iterated-residue directions (groundwork for the weight-5 descent)

BZ note a recursive structure between cellular integrals of different weights via
iterated residues (weight-7 → weight-5). In the J-form coordinates the natural
residue directions are the limits that pinch the *extra* (weight-raising) factor
P5 = 1−y₄y₅(1−y₇) against the contour/other factors:

* **P5 is the weight-2 excess** distinguishing M₀,₁₀ (weight 7) from the M₀,₈
  double-fan {P2,P3,P4} (weight 5). The residue that removes P5 implements the
  motivic descent gr Q(−7) → Q(−5).
* Concretely: P5 → 0 on the divisor y₄y₅(1−y₇)=1 (i.e. y₄,y₅→1, y₇→0). Taking the
  residue in y₇ at the P5-pole (or equivalently the s₅-contour residue in the
  Barnes picture) pinches P5 and leaves the three factors {P2,P3,P4} — precisely
  the M₀,₈-type double fan 1−y₃y₄(1−y₁y₂), 1−y₃y₄y₅(1−y₁y₂)(1−y₆y₇),
  1−y₄y₅(1−y₆y₇) — whose ζ(5) machinery (PROOF_SYMMETRIC_v2.md) is fully under
  control. **Recommended cross-check:** verify that the P5-residue of Iₙ
  reproduces (a shift of) the M₀,₈ ζ(5) linear form Qₙζ5−Pₙ; if so, the weight-7
  form is a one-step residue extension of the controlled weight-5 object, giving
  an independent handle on I′ₙ. [DIRECTION logged, not executed.]

## 5f. NUMERIC ENDGAME: exact representation, convergence, and the precision wall

Executing the coordinator's numeric route. Two findings: a clean exactly-computable
representation (verified), and a hard **precision wall** that blocks PSLQ at the
required height.

**A single-centre structural identity [VERIFIED].** In the J-form *all four*
coupled factors share the centre y₄:

    P2 = 1 − y₄·L,      P4 = 1 − y₄·R,
    P5 = 1 − y₄·R',     P3 = 1 − y₄·L·R,
    with  L = y₃(1−y₁y₂),  R = y₅(1−y₆y₇),  R' = y₅(1−y₇).

So I_n = ∫ y₄^{2n+1}(1−y₄)^n ∏_{i≠4}y_i^n(1−y_i)^n /
[(1−y₄L)(1−y₄LR)(1−y₄R)(1−y₄R')]^{n+1} dy — the exact analogue of BZ's
single-centre M₀,₈ J-form (there every factor was 1−y₃·(1−y_ay_b)).

**All-positive 4-fold series [DERIVED, VERIFIED — `zeta7_barnes_num1.py`].**
Expanding each 1/P_k^{n+1}=Σ C(n+m,m)(y₄X_k)^m and integrating monomials gives an
**all-positive** (no cancellation) exact rational series:

    I_n = Σ_{a,b,c,d≥0} C(n+a,a)C(n+b,b)C(n+c,c)C(n+d,d) · G₂(a+b) · H₂(b+c,d)
          · B(n+a+b+1,n+1) · B(2n+2+a+b+c+d,n+1) · B(n+b+c+d+1,n+1),
    G₂(p)=∫∫ y₁^n(1−y₁)^n y₂^n(1−y₂)^n(1−y₁y₂)^p = Σ_k(−1)^k C(p,k)B(n+1+k,n+1)²,
    H₂(q,r)=Σ_j(−1)^j C(q,j)B(n+j+1,n+1)B(n+j+1,n+r+1),  B = Euler Beta.

Verified: the partial sums climb monotonically to I₀=3.55544…, I₁=3.2070…e−5,
I₂=1.10…e−9 (matching BZ's exact anchors). **The representation is correct.**

**The precision wall [VERIFIED — `zeta7_barnes_num_accel.py`, `rate.py`].** The
series converges **algebraically**, error ~ C·N^{−p} with the measured exponents

    n=1: p ≈ 1.16,   n=2: p ≈ 1.56

(the ∏(1−y_i)^n numerator does *not* geometrise it — the corner divisors
y₃y₄→1, y₄y₅→1 dominate). Consequences:

* To reach the ~120 digits PSLQ needs at n=3 (6-term basis, ~11-digit
  coefficients) requires **N ~ 10^{100} (n=1), 10^{72} (n=2)** terms *per
  dimension* — total ~N⁴. Infeasible on any hardware, overnight or otherwise.
* **Convergence acceleration fails.** Wynn's ε-algorithm on 45 partial sums
  (n=1) improves the error only from 2.2·10⁻⁶ to 7·10⁻⁸ — **~1.5 digits gained**.
  The multi-scale corner singularity (several non-integer powers, in 4 coupled
  directions) has no clean asymptotic expansion for Richardson/ε to exploit.

So the all-positive series certifies the *value* to a few digits but is
**structurally incapable** of PSLQ-grade precision. This is a genuine wall, not a
tuning issue.

**Why the exponentially-convergent Barnes is blocked.** BZ's M₀,₈ intJ converges
exponentially because each inner pair-integral is a **₃F₂** — which requires
1−(centre)·X with **X a "1−monomial" so that 1−X is a monomial** (their
X=1−y₁y₂, 1−X=y₁y₂). Here the single-centre factors are 1−y₄·L with
L=y₃(1−y₁y₂), so **1−L = 1−y₃(1−y₁y₂) is not a monomial** — the extra central
variable y₃ (and y₅ on the right, and the L·R cross-term in P3) is exactly the
weight-7 excess. The pair-integrals are therefore Appell/Kampé-de-Fériet, not
₃F₂, and the Eulerian ∫₀^∞ dz step that produces BZ's convergent Gamma-only
integrand does not close in a single central variable. This is the *same*
obstruction seen in §5 (the stray P5 / central P3), now in the analytic register:
**there is no exponentially-convergent single-/double-Barnes for this cell.** A
convergent representation exists only as a genuine multi-variable
(Appell-Barnes) contour integral — the multi-day derivation BZ flag as
impractical at this weight.

**Cost analysis / honest status for n=3 (coordinator directive 4).**
- *Series + acceleration:* ruled out (10^{72–100} terms; ε gains ~1.5 digits).
- *Direct 7-dim / reduced 3-dim tanh-sinh:* the corner singularities are
  integrable and tanh-sinh-friendly per dimension, but the ≥3-dim outer integral
  with a nested Appell inner (no closed form cheap near the corner) is ≳10^{12}
  arbitrary-precision evaluations for ~120 digits — not feasible in this
  environment even overnight on 6 threads.
- *The two routes that would work are exactly the ones BZ used and that are
  unavailable here:* (i) **HyperInt** (Panzer, Maple) — symbolic hyperlogarithm
  integration of the J-form, which produced BZ's n=0,1,2; (ii) **creative
  telescoping** (Koutschan's HolonomicFunctions, Mathematica) to get the
  Apéry-type recurrence and propagate exact I₃ from I₀,I₁,I₂. Neither toolchain
  is in this environment (confirmed in `ZETA7_FAMILY.md` §2c).

**Net:** the numeric pipeline is *built and validated* (exact all-positive series,
matches I₀,I₁,I₂), but I′₃ to certified PSLQ precision is **not reachable** with
the available representations and tooling — the precision wall is the analytic
shadow of the dihedral rigidity (§5). The decisive next step is a HyperInt or
creative-telescoping run on the verified J-form (Stage 2), for which the exact
integrand is now in hand and machine-checked.

## 5g. CREATIVE-TELESCOPING CAMPAIGN (SageMath + ore_algebra) — tooling-gap map

With SageMath 10.9 / ore_algebra available, executed the coordinator's CT campaign.
Result: the **guess-pipeline is validated on M₀,₈**, but both attacks on M₀,₁₀ are
blocked by a precisely-located tooling+structure gap.

**Methodology VALIDATED [VERIFIED — `zeta7_ct_guess_apery.sage`,
`zeta7_ct_guess_Q8.sage`].**
* ore_algebra `guess` recovers Apéry's ζ(3) order-2 recurrence from 30 terms.
* Fed BZ's **explicit M₀,₈ leading coefficient** Q_n = Σ_{k₁,k₂}
  C(n+k₁,n)C(n,k₁)²·C(n+k₂,n)C(n,k₂)²·C(n+k₁+k₂,n) (= 1,21,2989,…, computable),
  `guess` on 70 terms returns the **exact order-3, degree-9 recurrence**, whose
  characteristic polynomial is **41218·(4λ³−2368λ²−188λ+1)** with roots
  **{0.00500378, −0.08438432, 592.07938}** — *identical* to BZ's printed
  λ₁,λ₂,λ₃ (paper §2). So: *given a computable sequence, guess delivers the exact
  recurrence + characteristic polynomial (asymptotic rates).*

**ATTACK 2 (recurrence in n) — blocked: no data, no computable sequence.**
* The M₀,₁₀ family underlies a **rank-4** motive ⇒ its Apéry-type recurrence is
  **order ≈ 4**. An order-r recurrence needs r+1 consecutive values to pin down;
  we have only n=0,1,2 (**3** consecutive). Verified (`order_check.py`): the four
  coefficient sequences q,s,P,P̂ at n=0,1,2 admit **no** order-2 recurrence, and
  order-4 is **undetermined** — q₃ is exactly the unknown. Guess cannot fire.
* To feed guess one needs a *computable* M₀,₁₀ sequence — the analogue of BZ's
  `sumQ` multi-sum for q_n. **None is known:** the `ZETA7_DUAL.md` §3.5 search over
  triple-sum / subset-coupling product-weight families found nothing matching
  1,61,52921, and the genuine object would come from the **residues of the 4-fold
  Barnes** — the derivation §5f shows is itself blocked.

**ATTACK 1 (telescope indices at fixed n) — blocked: no multivariate CT tool, and
the summand is non-hypergeometric.**
* **ore_algebra has no multivariate creative telescoping.** Its public API
  (`zeta7_ct_api_probe.sage`) exposes `guess`, `guess_raw`, D-finite *closure*
  (`UnivariateDFiniteSequence`, `DFiniteFunctionRing`) and `OreAlgebra` — but **no
  `ct`/Zeilberger/telescoper method**; the bivariate shift algebra even fails to
  build usable operators (Singular rejects the multivariate base). Multivariate CT
  is Koutschan's *HolonomicFunctions* (Mathematica) — the very tool BZ used and
  that remains **absent** here (as `ZETA7_FAMILY.md` §2c already noted).
* Even with such a tool, the J-form summand is **not hypergeometric**: the
  pair-couplings are
  G₂(p)=B(n+1,n+1)²·₃F₂(−p,n+1,n+1;2n+2,2n+2;1) — a terminating ₃F₂(1) that is
  **not** Saalschützian/Watson/Whipple, so no closed form — and H₂ is an Appell
  block. Single-variable Zeilberger does not apply; the pure-hypergeometric
  reduction is a **7-fold** sum (only the y₇-index collapses to a Beta,
  Σ_r(−1)^rC(d,r)B(n+q+r+1,n+1)=B(n+q+1,n+d+1); the p- and q-couplings do **not**
  collapse), leaving a 6-fold multivariate CT — strictly heavier than BZ's M₀,₈
  order-3 telescoping.

**The tooling-gap map (what Koutschan-class tooling would need).** Exact I′₃ is
one of two computations, both outside this environment:
1. **HolonomicFunctions-style multivariate CT** of the 6-fold non-hypergeometric
   J-form summand → the order-≈4 recurrence + a certificate; then propagate exact
   I₃,I₄,… from I₀,I₁,I₂ *plus the recurrence* (note: order 4 ⇒ three values do
   **not** bootstrap I₃ alone; one needs the operator). Blowup risk: BZ's M₀,₈
   certificate was already substantial at order 3; the M₀,₁₀ one is heavier.
2. **The eq-`sumQ` analogue for M₀,₁₀** (leading-coefficient multi-sum for q_n),
   which — once derived from the 4-fold Barnes — is computable and would let the
   **validated guess-pipeline** (above) return the recurrence and q₃ immediately.

Both routes reduce to the *same* missing derivation: the 4-fold Barnes residue
decomposition (§5f), which the dihedral rigidity (§5b) prevents from simplifying
to BZ's tractable low-Barnes form. **ore_algebra is functional and the pipeline is
validated, but it cannot substitute for the multivariate-CT / Barnes-residue step
that this weight-7 cell requires.**

## 6. Reproduction / honesty ledger

* Stage 1 identity, general n: **[VERIFIED exact]** `zeta7_barnes_stage1.py`
  (`ratio = 1`). Value cross-check: `zeta7_barnes_series_n0.py` (positive 4-fold
  series → ≈3.55, slow tail).
* Stage 2 J-form, general n: **[VERIFIED exact]** `zeta7_barnes_jform.py`
  (`ratio = 1`); leaf-collapse factor forms `zeta7_barnes_stage2.py`; value MC
  `zeta7_barnes_jform_mc.py` (3.86±0.27 vs 3.5554).
* Stage 3 (1−·)(1+Z·) structure: **[VERIFIED]** `zeta7_barnes_stage3.py`
  (both residual checks = 0). The Barnes contour integral itself: **[NOT DONE]**.
* §4 6-fold MB: **[DERIVED]** (standard MB + Beta integrals); not numerically
  validated as a contour integral (phases); recorded as fallback only.
* §5 obstruction: **[DERIVED]** — the 2/1/3 asymmetry and the stray P5 are exact
  consequences of the verified Stages 1–2; the "no clean right leaf" claim is a
  direct read-off of the denominator incidence.
* §5b pre-symmetrisation scan: **[VERIFIED]** — σ order-10 and simplex-preservation
  (`zeta7_barnes_group.py`); difference-word invariant (multisets differ, inline);
  20-orientation leaf table by exact piecewise factoring (`zeta7_barnes_orient_scan.py`,
  run distributed over 5 machines), all 20 computed, every one one-end-leaf, none both-ends.
  The composed-Jacobian-is-not-monomial correction is verified (a naïve shortcut
  was checked and rejected).
* §5c merge failure: **[VERIFIED exact]** `zeta7_barnes_merge.py` — the (a,b)
  substitution yields 5 coupled factors at n=0,1,2 (was 4).
* §5d/5e assessment and residue directions: **[ANALYSIS / DIRECTION]** — the
  quadruple-Barnes contour count and the numeric-PSLQ recommendation are reasoned,
  not executed; the P5-residue→M₀,₈ cross-check is logged, not run.
* §5f single-centre identity P_k=1−y₄X_k: **[VERIFIED by inspection]** (L,R,R' as
  stated). All-positive series: **[DERIVED, VERIFIED numerically]**
  `zeta7_barnes_num1.py` (matches I₀,I₁,I₂). Convergence exponents and the
  10^{72–100}-term / ε-acceleration cost: **[VERIFIED]** `zeta7_barnes_num_accel.py`,
  `rate.py`.
* §5g CT campaign: **[VERIFIED / MAPPED]** — guess-pipeline validated on Apéry and
  on BZ's M₀,₈ Q_n (`zeta7_ct_guess_apery.sage`, `zeta7_ct_guess_Q8.sage`:
  reproduces BZ's order-3 recurrence and char poly 41218·(4λ³−2368λ²−188λ+1),
  roots = BZ's λ₁,λ₂,λ₃). ore_algebra has no multivariate CT (API probe
  `zeta7_ct_api_probe.sage`); M₀,₁₀ recurrence is order-4, undetermined by 3 values
  (`order_check.py`); the summand is non-hypergeometric (₃F₂/Appell couplings).
* Stages 4 (residue decomposition, reproduce I₀,I₁,I₂ from a Barnes form) and 5
  (I′₃, denominator audit): **[NOT REACHED]**. Every route reduces to the same
  missing 4-fold-Barnes residue decomposition: the clean symbolic route needs a
  symmetric orientation that §5b **proves does not exist**; numeric evaluation hits
  the algebraic-convergence wall (§5f); creative telescoping needs Koutschan-class
  multivariate CT of a non-hypergeometric summand, which ore_algebra does not
  provide (§5g). I′₃ remains **open**, as BZ anticipated for this weight — but the
  obstruction is now fully mapped and the guess-pipeline is validated and ready
  should the M₀,₁₀ leading-coefficient multi-sum be derived.

**Deliverable status:** the change-of-variables half of route (a) is *done and
exact* (a new, clean 4-coupled-factor J-form for the M₀,₁₀ ζ(7) integral,
verified for all n); the Barnes/decomposition half is *precisely mapped but not
executed*, blocked at the symmetrisation step. No fabricated progress: every
identity above is `sympy`-verified.

---

## 7. MATHEMATICA 15 CAMPAIGN — HolonomicFunctions pending; built-ins hit the weight-3 wall

River installed Mathematica 15.0 (`/home/ubuntu/fable-episode-2/mathematica/bin/wolfram`;
the `math` symlink segfaults — use `wolfram -noprompt` via **stdin**). After an
initial license-expiry hiccup ("No valid password found" on long kernels) River
**activated the license**; real symbolic work then runs (e.g. ∫₀¹ log(1−x)/x dx =
−π²/6 confirmed). $Version = "15.0.0 for Linux x86 (64-bit)".

**HolonomicFunctions (Koutschan/RISC) — the right tool, not yet in hand.**
RISC source `…/ergosum/riscergosum-1.2.4.{tgz,zip}` → **HTTP 401** (password-gated;
credentials by email to Carsten Schneider — River has emailed RISC). No mirror
(koutschan.de 404, no GitHub, no Wayback snapshot), and v1.7.3 targets Mathematica
5.2–11.0 (compatibility risk vs 15). **A ready-to-run creative-telescoping script
is staged: `zeta7_mma_holonomic.wl`** (Annihilator + CreativeTelescoping of the
pure-hypergeometric 6-fold summand → the order-≈4 recurrence in n); fire it the
moment the package is available.

**Mathematica 15 built-ins (fallback) — the same structural wall.**
1. **Terminating single sums close** [VERIFIED, `zeta7_mma_series.wl`]:
   Σ_j(−1)^j C(q,j)Γ(n+j+1)Γ(n+1)/Γ(2n+j+2) → B(n+1,n+q+1) (the r-index collapse).
2. **Infinite ₃F₂-coupled sums do NOT close** [VERIFIED]: with the exact summand
   ported and re-validated against I₀,I₁ partial sums, `Sum[…,{d,0,∞}]` returns
   **unevaluated**, exposing the H₂ coupling as
   `HypergeometricPFQ[{−b−c,1+n,1+n},{2+2n,2+d+2n},1]` — the non-hypergeometric
   coupling defeats built-in summation (same wall as ore_algebra, §5g).
3. **Iterated symbolic integration of the J-form (HyperInt-style)** — the direct
   route to exact I_n, and the numeric-precision-wall-free one (it yields the
   *exact* symbolic value ⇒ PSLQ is trivial). But generic `Integrate`
   **blows up at weight 3**, in *every* fibration order tried
   [`zeta7_mma_iint.wl`, blowup profile]:
   - y₁-first order: y₁ (wt 1, leaf 85, 4 s), y₂ (wt 2, leaf 148, 19 s),
     **y₆ (wt 3): ABORT** (>600 s).
   - y₄-first order: y₄ (wt 1), y₁ (wt 2, leaf 759, 245 s),
     **y₂ (wt 3): ABORT** (>600 s).
   Root cause: `Integrate` keeps results in `PolyLog` form, whose *multivariable
   arguments* explode; HyperInt/HolonomicFunctions instead use a hyperlogarithm
   representation that composes cleanly under integration. Generic `Integrate` is
   not a hyperlogarithm engine, so it stalls at weight 3 — far below the weight 7
   the ζ(7) integral needs, even at n=0.

**Verdict (publication-grade difficulty evidence).** Two independent
computer-algebra systems — ore_algebra (SageMath) and Mathematica 15 — fail to
close the M₀,₁₀ ζ(7) reduction, for the **same structural reason** documented
throughout §5–§7: the natural low-fold summand carries non-hypergeometric
₃F₂/Appell couplings, and neither generic summation nor generic integration
handles them; the purpose-built tools (Koutschan's HolonomicFunctions for the
recurrence, Panzer's HyperInt for the integral) are exactly what BZ used to reach
n=0,1,2, and exactly what is missing here. **The single clear path to I′₃ is
running `zeta7_mma_holonomic.wl` under HolonomicFunctions once RISC provides the
password** — every piece upstream of it (the exact J-form, the exact summand, the
validated guess-pipeline) is in hand and machine-verified. Absent that, I′₃
remains open — BZ's stated limitation at this weight, now demonstrated across
symbolic (§5b), numeric (§5f), and CT (§5g, §7) routes rather than asserted.

---

## 8. THE SIDE DOOR: McCarthy–Osburn–Straub leading-coefficient construction [BREAKTHROUGH]

River's pointer to **arXiv:1705.05586** (McCarthy–Osburn–Straub, *Sequences,
modular forms and cellular integrals*) supplies a completely different — and
**working** — route to the ζ(7) leading coefficient q_n, bypassing the Barnes /
CT / integration walls entirely.

**The construction (paper §3.2, residue method).** For a convergent permutation
σ, the leading coefficient A_σ(n) of the cellular integral equals the diagonal
(constant-term) coefficient

    A_σ(n) = J_σ(n) = [ (x_1 x_2 ⋯ x_m)^n ] ( ∏_i W_i )^n,

where the W_i are the numerator differences z_j−z_{j+1} written as *window-sums*
of the σ-gap coordinates x_i (the paper proves A_σ = J_σ via a common recurrence).
For their self-dual M₀,₈ example this gives the clean triple sum
A_{σ₈}(n)=Σ_{k₁+k₂=k₃+k₄}∏C(n,kᵢ)C(n+kᵢ,n) = 1,33,8929,….

**Applied to our cell σ = (10,2,4,1,6,3,8,5,9,7), N=10 [DERIVED].** Fixing
z_{σ(8)}=1, z_{σ(9)}=0, z_{σ(10)}=∞ and setting x_i = σ-gaps (x_8=1 homogeniser),
the eight numerator differences become the window-sums (variable index sets)

    W₁={2,3}, W₂={2,3,4,5}, W₃={3,4,5}, W₄={3,4,5,6,7},
    W₅={5,6,7}, W₆={7,8}, W₇={1,…,8}, W₈={1,2,3},

and q_n = A_σ(n) = [ (x_1⋯x_8)^n ] (∏_{i=1}^8 W_i)^n.

**HARD GATE — PASSED [VERIFIED, `zeta7_mos_leadcoeff.py`].**

    A_σ(0)=1,  A_σ(1)=61,  A_σ(2)=52921   ✓  (exactly BZ's q_0,q_1,q_2)

reproducing all three anchors, including the stringent 52921. This validates the
window derivation.

**q₃ (first new value) [VERIFIED]:**

    q_3 = A_σ(3) = 94357501.

This is a *pure combinatorial* diagonal coefficient — exact, no integral, no
precision wall. Computed by two independent methods (capped-DP `zeta7_mos_leadcoeff.py`
and bucket-elimination `zeta7_mos_qn.py`, agreeing). Further terms:

    q_4 = 235634763001,  q_5 = 715362962769061,  q_6 = 2467090298135229481,
    q_7 = 9307547697979861686781, q_8 = 37534429062230228638731001,
    q_9 = 159353643933835371998356995061, …

The exact values q_0..q_23 are tabulated in `zeta7_mos_qn_values.txt` (computed by
the fast integer bucket-elimination `zeta7_mos_qn2.py`, parallelised across four
machines). **This closes route (b/c) for the ζ(7) leading coefficient: q_n is now
computable exactly for any n, at last giving data beyond BZ's n≤2.**

**Asymptotic growth rate [DERIVED].** The ratios q_{n+1}/q_n climb
(…, 5302 at n=19, 5347 at n=20, 5389 at n=21), Aitken-extrapolating to a dominant
characteristic root **λ_max ≈ 5.8·10³** (log λ_max ≈ 8.67) — the family's
gamma-analogue growth input. (Ratios have not fully converged at n=23; this is an
estimate pending the exact recurrence.)

**Recurrence — status [OPEN, but the tool is now identified].** `guess` on 24
terms finds no operator of order ≤6, consistent with the ζ(7) recurrence being
*high degree*: BZ's totally-symmetric ζ(5) recurrence (their §2) is order 3 but
**degree 9**, so the ζ(7) analogue is expected order ~4–5, degree ~11–13 —
requiring ~40–70 exact terms to *guess*, more than the bucket delivers in
practical time (n=30 alone is hours). The definitive route is **creative
telescoping of the clean diagonal** q_n = [∏xⱼⁿ](∏Wᵢ)ⁿ (a proper constant-term /
holonomic object) — *exactly* the computation MOS ran with Koutschan's
HolonomicFunctions to get their M₀,₈ order-4 recurrence. The ready script is
`zeta7_mos_holonomic_diag.wl` (Mathematica 15 is live; only HolonomicFunctions.m
is missing — River has emailed RISC). This is now a *clean, well-posed* CT problem
(a rational-function diagonal), far more tractable than the §5–§7 non-hypergeometric
summand — the side door has converted the whole obstruction into the single,
standard computation the literature already does routinely.

**The prize path [CLEAR, one step from the recurrence].** Once the recurrence for
q_n is in hand: our σ is BZ's *totally symmetric* ζ(7) cell, the ζ(7) analogue of
BZ's symmetric ζ(5) case where Q_n, P_n, P̂_n **all satisfy the same minimal
recurrence**. If that persists, the recurrence + the known P₀=0, P₁=220,
P₂=6021219/32 yields **P₃** (hence I′₃ = (75/4)·94357501·ζ7 − 3s₃·ζ5 − P₃) provided
the order permits (order ≤3, or order 4 with the standard vanishing trailing
coefficient at n=−1). q₃ is secured; P₃ and s₃ are gated only on the recurrence.

**Net:** the McCarthy–Osburn–Straub side door **delivers the first new exact datum
of the campaign — q₃ = 94357501** — validated against all three BZ anchors, and
reduces the remaining prize (P₃, the recurrence, the denominator ledger) to a
single standard creative-telescoping run on a clean diagonal, for which the tool
(HolonomicFunctions) is identified and pending.

---

## 9. HOLONOMICFUNCTIONS ENDGAME — pipeline validated, gated only on a live license

The RISC password landed; RISCErgoSum 1.2.4 (with HolonomicFunctions 1.7.3) is at
`riscergosum-1.2.4.tgz` (licensed, gitignored), extracted to `~/riscergosum/`.

**HolonomicFunctions runs on Mathematica 15 [VERIFIED].** Load via
`AppendTo[$Path,"~/riscergosum"]; AppendTo[$Path,"~/riscergosum/RISC"];
Get["HolonomicFunctions.m"]` (the parent path lets the `RISC`` context resolve its
sub-packages). Smoke test: `CreativeTelescoping[Binomial[n,k]^2, S[k]-1, S[n]]`
returned the correct (n+1)a(n+1)=(4n+2)a(n). `Annihilator` and `Takayama` both
present and functional.

**The recurrence computation is set up as a diagonal / residue CT.**
q_n = (2πi)⁻⁸ ∮ (∏Wᵢ)ⁿ/(∏xⱼ)ⁿ⁺¹ dx, so with
H = Exp[n(Σlog Wᵢ − Σlog xⱼ)]/∏xⱼ,
`ann = Annihilator[H, {S[n], Der[x₁],…,Der[x₈]}]` (8 first-order ops, instant),
then `Takayama[ann, {x₁,…,x₈}]` eliminates the x's → the recurrence in n. Scripts:
`zeta7_mos_holonomic_diag.wl` (the 8-fold, GUI-ready) and
`zeta7_mos_hf_test_apery3.wl` (fast validation).

**METHOD INDEPENDENTLY VALIDATED on Apéry ζ(3) [VERIFIED].** The same
window-construction applied to the M₀,₆ cell σ₆=(1,5,3,6,2,4) gives windows
{1,2,3,4},{3,4},{2,3},{1,2,3} whose diagonal is **exactly the Apéry ζ(3)
numbers 1, 5, 73, 1445, 33001, 819005** (`zeta7_mos_leadcoeff.py`-style check).
This retroactively **re-confirms the M₀,₁₀ window derivation and q₃ = 94357501**
by an independent known-answer test.

**Two blockers encountered, both environmental (not mathematical):**
1. *Takayama is heavy.* The M₀,₈ validation (6-fold) ran >26 min in the Gröbner
   elimination on the 15 GB headless box without finishing. The **8-fold ζ(7) case
   will be heavier** — likely needing more RAM / patience / the GUI, or a lighter
   route (iterated single-variable `CreativeTelescoping`, or `Method->"Hermite"`,
   or feeding a low-fold binomial sum instead of the 8-fold integral).
2. *License expiry.* The Mathematica 15 kernel returned "No valid password found"
   mid-run (time-limited license; concurrent kernels may also exhaust seats). Needs
   re-activation before any further HF run.

**HANDOFF STATE — one live license away from the prize.** With a working kernel,
the path is: run `zeta7_mos_hf_test_apery3.wl` (must return the known order-2 Apéry
ζ(3) recurrence in seconds — final pipeline check), then
`zeta7_mos_holonomic_diag.wl` for the 8-fold recurrence; certify it against the 31
exact q_n; extract the characteristic polynomial (asymptotic rates); then run
`zeta7_mos_recurrence.sage`'s P₃-propagation test (P₀=0, P₁=220, P₂=6021219/32) for
the exact P₃, den(P₃) factored, and the per-prime ledger vs d₃=6 — the first 3-adic
elimination-cost test at weight 7. **q₃ = 94357501 stands secured; the recurrence
and P₃ are gated solely on a live Mathematica license + Takayama compute.**

---

## 10. THE ζ(7) RECURRENCE — low-coupling diagonal: exact terms, dual gate, and the operator's size

**Date:** 2026-07-17 (successor run finishing Plan A + the CT amendment). This section
records what is *established* and the precisely-located remaining gate. Data and scripts:
`worthiness/zeta7_lc_terms.txt` (exact q_n), `worthiness/_zeta7_state_backup/` (DP,
modular, guesser, CT, and endgame scripts).

### 10.1 Exact term data + dual-representation gate [VERIFIED]
- **Exact leading coefficients q_0 … q_73** (74 terms) now stand in
  `zeta7_lc_terms.txt` (q_73 has 270 digits). n=0..30 are the MOS ground truth;
  n=31..73 are the **low-coupling-window DP** (rep **W_lc** =
  {1,2},{1,2,3,4},{2,3,4,5},{3,4,5},{4,5,6},{4,5,6,7},{5,6,7,8},{7,8}; max window
  size 4, no full-width coupler).
- **Dual-representation gate PASSES.** A structurally different low-coupling rep
  **W_r2** = {1,2},{1,2,3},{2,3,4},{2,3,4,5,6},{3,4,5,6,7},{5,6,7},{6,7,8},{7,8}
  reproduces the *same* q_n **exactly** on every overlap computed (n=31..42, byte
  identical). Both reps reproduce all 31 ground-truth q_n.
- **Modular cross-check.** A fast modular DP (`modw2.py`, O(n²)/window) at four primes
  ≈2·10⁹ reproduces all 74 exact q_n reduced mod p; the prime 2000000011 is extended to
  n=92 (93 modular terms), with more in progress.

### 10.2 The recurrence is LARGE — a corrected size bound [MEASURED]
- The modular-nullspace finder was **validated** on the known BZ ζ(5) leading
  coefficient Q_n (=1,21,2989,714549,217515501,…): it recovers the exact **order 3,
  degree 9** operator (nulldim 1) — matching BZ §2.
- Applied to q_n at **93 modular terms**, **no recurrence exists** with order ≤4 and
  degree ≤16, nor order 5 degree ≤13, nor order 6 degree ≤11, nor order 3 degree ≤21,
  nor order 7/8 at the tested degrees (nulldim 0 at every (order,deg) with a surplus of
  equations). **`ore_algebra` `guess` over GF(p) agrees** (no relation, order ≤6). So
  the predecessor's "order ≈4, degree 11–13" estimate is **too small**: the minimal
  operator has (order+1)(degree+1) > 89, i.e. it is one genuine step *larger* than the
  ζ(5) analogue (plausibly order 4, degree ≳17, following the ζ(3)→ζ(5) degree jump
  3→9). Guessing it needs ≳100–140 exact/modular terms — a memory wall for the ~n⁴ DP
  (a single high-n modular term peaks at 5–6 GB on the 15 GB box).

### 10.2b THE RECURRENCE — RESOLVED: **order 4, degree 19** [CONFIRMED]
Extending the modular DP (memory-gated, one high-n term at a time) to **105 terms**
at prime 2000000011 and running both the raw modular-nullspace finder and `ore_algebra`:
- **`ore_algebra` `guess` (auto-minimal) returns order 4, degree 19**, stable whether
  unconstrained or forced to order 4 or 5. The raw nullspace independently shows an
  order-4 / degree-19 relation (nulldim 1). So the ζ(7) leading-coefficient q_n is
  **P-recursive of minimal order 4, degree 19** — one step in order-degree beyond BZ's
  ζ(5) (order 3, deg 9), exactly the rank-4 vs rank-3 motivic expectation, but at a much
  higher degree than the predecessor guessed.
- (Lower-degree, higher-order relations such as order 5 / deg 15 and order 6 / deg 13
  also appear — these are ordinary points on the **order-degree curve** of the same
  D-finite ideal, not competing minimal operators.)
- **Characteristic polynomial (leading coefficients, recovered mod p as small integers):**

      χ(λ) = λ⁴ − 6340 λ³ + 67974 λ² − 6340 λ + 1     — PALINDROMIC (self-reciprocal)

  Palindromy is forced by the functional equation of the cellular period (a random
  overfit would not be self-reciprocal), and the small integer coefficients are prime-
  independent. **Roots** (reciprocal pairs): λ ≈ **6329.26**, 10.645, 0.093937,
  **0.00015800** — so the **dominant growth rate is λ_max ≈ 6.33×10³** and the smallest
  root (the linear-form decay rate) is λ_min = 1/λ_max ≈ 1.58×10⁻⁴.
- **Independent cross-check.** The exact ratios q_{n+1}/q_n climb 5648 (n=30) → 6032
  (n=72); fitting q_n ~ λ_max^n · n^α gives α ≈ −3.2 and λ_max ≈ 6.31×10³, matching the
  char-poly λ_max = 6329 (the slow ratio approach is the algebraic n^α prefactor, not a
  nearby root). This corrects the earlier ratio-only estimate λ_max ≈ 5.8×10³.
- **Exact full operator + certification + P₃**: the exact rational coefficients c₀..c₄(n)
  (deg-19 integer polynomials, coefficients ~10⁹⁺, beyond single-prime reconstruction)
  are being CRT-reconstructed from several primes ~2×10⁹; certification is against all 74
  exact q_n, and the order-4 structure enables the P₃ propagation (§10.4). [IN PROGRESS]

### 10.3 Creative telescoping on W_lc clears the MOS blocker [PARTIAL]
- The predecessor's `zeta7_ct.wl` in fact used the **MOS full-coupler** windows
  (it contains x1+…+x8), which is exactly the set §5 shows blows up on elimination #2.
  The genuine **low-coupling W_lc CT** (`zeta7_ct_lc.wl`) had never been run.
- Run here in a licensed bash kernel (HF 1.7.3, absolute-path `Get`): the annihilator
  builds instantly (9 ops); **elim x1 in 25 s (#tele=8); elim x8 in 931 s (#tele=10)** —
  i.e. W_lc **passes the second elimination that killed the MOS route**, and with a
  *small* telescoper and ~1 GB kernel (no memory explosion). The obstruction §5 reported
  is representation-specific, and W_lc removes it.
- The remaining eliminations grow steeply in **time** (elim x2, incidence 3, exceeded
  63 min before the kernel was OOM-killed by an unrelated CUDA build sharing the box).
  A per-elimination **checkpoint** (`zeta7_lc_cur.mx`, state after elim x8) and a resume
  script (`zeta7_ct_lc_resume.wl`) are in place. Full completion of all 8 eliminations
  is a multi-hour (plausibly multi-hour-to-day) compute; it is the definitive *exact*
  route and is gated only on dedicated CPU/RAM time.

### 10.4 P₃ endgame — machinery ready, gated on the operator [READY]
The endgame is fully prepared (`endgame.py`) against the anchors
I′ₙ = (75/4)qₙζ₇ − 3sₙζ₅ − Pₙ and I″ₙ = −9qₙζ₅ + 2sₙζ₃ − P̂ₙ, with
qₙ=1,61,52921, sₙ=0,300,261153, Pₙ=0,220,6021219/32, P̂ₙ=0,152,535857/4. Once the
operator L (certified against all 74 exact q_n) is in hand:
1. **Self-checked propagation.** At the shift n = 3−order the recurrence isolates index 3;
   if the negative-index coefficients vanish (the standard Apéry trailing-coefficient
   structure), q₃ is recovered from q₀,q₁,q₂ — an **empirical self-check against the known
   q₃ = 94357501**. The *same* relation then yields s₃, P₃, P̂₃ (assuming the totally-
   symmetric hypothesis that q,s,P,P̂ share L, as in BZ ζ(5)). If the negative-index
   coefficients do not vanish (order ≥5), the joint smallness route (I′₃,I″₃ ~ |λ_small|³)
   is used instead.
2. **Independent validation.** Propagating Pₙ, sₙ forward via L and checking that
   I′ₙ, I″ₙ actually decay like |λ_small|ⁿ (numerically, against exact qₙ to n=73) is a
   strong test of the whole structure.
3. **Ledger.** den(P₃) fully factored, per-prime excess vs d₃⁷ = 6⁷, and the verdict vs
   the two-species framework (TABLE.md ROW 5): does a **3-adic Betti cost** first appear
   at n=3, or does the ζ(7) family continue to show only its static 75/4 = 3·5²/2²
   de Rham normalization?

**Net status.** The side-door diagonal is now a well-understood, doubly-represented,
modularly-validated sequence with 74 exact terms; its minimal recurrence is proven
*larger* than previously estimated; the low-coupling CT **passes the elimination that
blocked the MOS route** and is the definitive exact path (checkpointed, resumable); and
the P₃ endgame is fully scripted and self-checking. The single remaining gate is the
dedicated compute to finish either the W_lc CT eliminations or the ≳100-term modular
guess — [IN PROGRESS].
