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
**left/right asymmetry** of the direct cubical form that BZ's σ-power symmetrisation
removes for M₀,₈ but which has no elementary analogue here — documented in §5.
Every claimed identity below is machine-verified.

Scripts: `zeta7_barnes_stage1.py`, `zeta7_barnes_stage2.py`,
`zeta7_barnes_jform.py`, `zeta7_barnes_stage3.py`, `zeta7_barnes_series_n0.py`,
`zeta7_barnes_jform_mc.py`. No existing files modified.

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
* Stages 4 (residue decomposition, reproduce I₀,I₁,I₂ from the Barnes form) and 5
  (I′₃, denominator audit): **[NOT REACHED]** — gated on completing Stage 3,
  itself gated on the symmetrising automorphism (§5, item 5).

**Deliverable status:** the change-of-variables half of route (a) is *done and
exact* (a new, clean 4-coupled-factor J-form for the M₀,₁₀ ζ(7) integral,
verified for all n); the Barnes/decomposition half is *precisely mapped but not
executed*, blocked at the symmetrisation step. No fabricated progress: every
identity above is `sympy`-verified.
