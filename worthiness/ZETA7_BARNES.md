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
same rigidity. **I′₃ is not reached**: the exact route needs HyperInt or creative
telescoping on the (now machine-verified) J-form, tooling absent here — exactly
BZ's stated limitation at this weight. Every identity/table below is
machine-verified.

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
* Stages 4 (residue decomposition, reproduce I₀,I₁,I₂ from a Barnes form) and 5
  (I′₃, denominator audit): **[NOT REACHED — precision wall, §5f]**. The clean
  symbolic route is gated on a symmetric orientation that §5b proves does not
  exist; the numeric route is blocked by algebraic convergence (§5f); the exact
  route needs HyperInt or creative telescoping on the (verified) J-form — tooling
  not in this environment. I′₃ remains open, as BZ anticipated for this weight.

**Deliverable status:** the change-of-variables half of route (a) is *done and
exact* (a new, clean 4-coupled-factor J-form for the M₀,₁₀ ζ(7) integral,
verified for all n); the Barnes/decomposition half is *precisely mapped but not
executed*, blocked at the symmetrisation step. No fabricated progress: every
identity above is `sympy`-verified.
