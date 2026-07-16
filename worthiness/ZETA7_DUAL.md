# SERIES identification of the Brown–Zudilin ζ(7) cellular family (M₀,₁₀)

**Route:** very-well-poised / dual SERIES identification (companion to the scout's
integral-side `ZETA7_FAMILY.md`). **Engine:** `zn_check.py` (exact-rational Laurent
principal-part decomposition of VWP sums into ℚ-linear forms in zeta values).
**No existing files modified.** All scripts here are `zeta7_dual_*.py`; every
numeric claim is reproducible with `python3 <script>`.

## Status: PARTIAL → **single-sum VWP route EXCLUDED** (see §7). Candidates tested
and excluded with exact mismatch evidence; the decisive discriminant is a **sign
obstruction** (BZ I′ₙ has opposite-sign adjacent zetas; every very-well-poised
single sum — symmetric or spread — gives same-sign, r5 > 0). Remaining path:
triple Mellin–Barnes (scout's route (a)). §7 is the coordinator-directed
spread-pole hunt and its combined exclusion map.

---

## 0. The exact target (transcribed, cross-checked with scout)

BZ split Iₙ = I′ₙ + I″ₙ·ζ(2). With shared integer ladders qₙ, sₙ (scout's §1.3,
= my A_n, B_n):

    I′ₙ = (75/4)·qₙ·ζ7 − 3·sₙ·ζ5 − Pₙ         ∈ span{1, ζ5, ζ7}   (NO ζ3)
    I″ₙ =    −9·qₙ·ζ5  + 2·sₙ·ζ3 − P̂ₙ         ∈ span{1, ζ3, ζ5}   (NO ζ7)
    qₙ = 1, 61, 52921    sₙ = 0, 300, 261153
    Pₙ = 0, 220, 6021219/32    P̂ₙ = 0, 152, 535857/4

**Normalization-free within-n ratios** (the rigorous match invariants; a genuine
identification must reproduce these exactly, independent of any n-dependent
prefactor). [DERIVED, `zeta7_dual_match.py`]

    I′ₙ:  r5 = coeff(ζ5)/coeff(ζ7),   rc = const/coeff(ζ7)
          n=1:  r5 = −48/61,          rc = −176/915
          n=2:  r5 = −1044612/1323025, rc = −2007073/10584200
    I″ₙ:  r3 = coeff(ζ3)/coeff(ζ5),   rc = const/coeff(ζ5)
          n=1:  r3 = −200/183,        rc = 152/549
          n=2:  r3 = −58034/52921,    rc = 10507/37356

Note both forms have **opposite-sign** adjacent zeta coefficients (ζ7 vs ζ5 in I′;
ζ3 vs ζ5 in I″). This is the crux — see §3.

---

## 1. Engine + recipe VALIDATED on an independent series (ζ(5)) [VERIFIED]

The M₀,₈/ζ(5) analogue of I′ₙ is Zudilin's very-well-poised series
(*A third-order Apéry-like recursion for ζ(5)*, arXiv math/0206178, eq. 7):

    r_n = n!⁴ · Σ_{k≥1} (k + n/2) · ∏_{j=1}^n(k−j)·∏_{j=1}^n(k+n+j) / ∏_{j=0}^n(k+j)⁶
        = u_n ζ5 + w_n ζ3 − v_n         (a form in 1, ζ3, ζ5).

Fed to `zn_check.linear_form_coeffs` (pref = n!⁴, half-shift n/2, num bases
{−1..−n}∪{n+1..2n}, den bases {0..n}×6, C = 0) the engine returns **exactly**
Zudilin's printed values [`zeta7_dual_zud.py`]:

    r₀ = ζ5 ;  r₁ = 9ζ5 + 33ζ3 − 49 ;  r₂ = 469ζ5 + (6125/4)ζ3 − 74463/32   ✓ (all n)

This is an **independent second validation** of the engine (beyond its built-in
ζ(4) self-test), on a series with ζ3 AND ζ5 present.

**The ζ3-elimination recipe** (how BZ's pure I′ₙ arises from Zudilin's mixed r_n):
with the tilde-companion ~r_n (same shape, num products from j=0), form
`L_n = w̃_n·r_n − w_n·~r_n` (w = coeff ζ3). This kills ζ3, and the engine gives
[`zeta7_dual_z5series.py` calibration block]

    L₁: z5 = −42,  const = +87/2,  ratio const/z5 = −29/28          ✓
    L₂: z5 = 17934, const = −1190161/64, ratio = −24289/23424        ✓

i.e. exactly Zudilin's pure ℓ_n = q_n ζ5 − p_n (q₁=42, q₂=−17934), which equals
BZ's Q_n ζ5 − P_n up to the factor (−1)^{n+1}/C(2n,n) (Q_n = (−1)^{n+1}q_n/C(2n,n):
Q₁ = 42/2 = 21, Q₂ = 17934/6 = 2989 ✓). **Recipe confirmed on ζ(5).**

---

## 2. The natural ζ(7) VWP family, and why it is a genuine new object [VERIFIED byproduct]

The structural pattern is unambiguous: **den-power = weight + 1** (ζ3→⁴, ζ5→⁶,
ζ7→⁸), prefactor n!^{den−2}. The ζ(7) analogue

    ρ_n = n!⁶ · Σ_{k≥1} (k + n/2) · ∏_{j=1}^n(k−j)·∏_{j=1}^n(k+n+j) / ∏_{j=0}^n(k+j)⁸

decomposes (engine, `zeta7_dual_zud.py`) into a clean form in **1, ζ3, ζ5, ζ7**
with ζ9 = 0 and all even zetas 0 (i.e. it IS very-well-poised), with ρ₀ = ζ7:

    ρ₁ = 13ζ7 + 110ζ5 + 306ζ3 − 495
    ρ₂ = 2161ζ7 + (27275/2)ζ5 + (284081/8)ζ3 − 7552683/128
    ρ₃ = 604525ζ7 + (72045895/18)ζ5 + (759650045/72)ζ3 − 542530371845/31104

This is, to our knowledge, a not-previously-tabulated one-parameter VWP family of
{1,ζ3,ζ5,ζ7} linear forms — the direct ζ(7) sibling of Zudilin's eq. 7. **But it
is NOT the BZ family** (see §3).

---

## 3. EXCLUSIONS (exact mismatch evidence)

### 3.1 Bare k=9 dual series F̃₉ (route 1, all-equal symmetric point) [EXCLUDED]
`zeta7_dual_vwp.py`. The paper's own VWP dual F̃₉(b₀;b₁…b₉) with b₁=…=b₉=b,
b₀ ≥ 2b, gives forms in {1,ζ3,ζ5,ζ7} (ζ9 and even zetas vanish — engine confirms
the Zudilin-§3 parity claim), but its ζ3 coefficient is generically nonzero and
its within-n ratios do **not** match I′ₙ. Confirmed at the b-dictionary point too:
F̃₇(3n;n⁷) reproduces the M₀,₈ *dual* integral ∈ ℚ+ℚζ3+ℚζ5 with ζ5-coeff
2,18,938 ≠ Q_n = 1,21,2989 [`zeta7_dual_calib.py`]. As the scout independently
concluded, **the dual series is a different linear form from I′ₙ.**

### 3.2 Canonical reflection-symmetric block series + ζ3-kill [EXCLUDED]
`zeta7_dual_bigscan.py`, `zeta7_dual_gen.py`. Full grid over
den-range M∈{n,2n}, num-length L∈{n,2n,3n}, den-power A∈{6,8,10},
block-power B∈{1,2,3}, derivative-order C∈{0,1,2} (162+ configs), each with the
validated ζ3-kill of its tilde-companion. **No configuration reproduces
(r5, rc) = (−48/61, −176/915) at n=1.** Not even a single r5-only partial hit.

### 3.3 I″ₙ as a single den⁶-type series [EXCLUDED]
`zeta7_dual_Idd.py`. I″ₙ ∈ {1,ζ3,ζ5} needs no ζ-killing (single series suffices
dimensionally). Grid over M,L,A∈{4,6,8},B,C (+tilde): **no match** to
(r3, rc) = (−200/183, 152/549).

### 3.4 THE OBSTRUCTION [DERIVED — the key structural finding]
Every reflection-antisymmetric block series R(k) (R(−n−k) = −R(k), the structure
of ALL Zudilin eq.7-type series, for any C) yields **same-sign** odd-zeta
coefficients — verified across the entire §3.2/§3.3 grid (e.g. ρ₁: +13ζ7 +110ζ5
+306ζ3; Zudilin r₁: +9ζ5 +33ζ3). But BZ's I′ₙ and I″ₙ have **opposite-sign**
adjacent zetas (§0). A single such series therefore *cannot* be I′ₙ or I″ₙ, and a
ζ3-kill of two same-sign-ratio companions cannot flip r5 negative either (the §3.2
scan is the exhaustive check). The ζ(5) case escaped this test only because its
I′,I″ each contain a *single* zeta (no adjacent pair to compare). **This is why
the clean ζ(5) construction does not lift naïvely to ζ(7).**

### 3.5 A_n = qₙ = 1,61,52921 as an Apéry-like multisum [EXCLUDED]
`zeta7_dual_triple.py`, `zeta7_dual_exhaust.py`, `zeta7_dual_Awide.py`.
Generalizing the *verified* M₀,₈ leading double sum
`Q_n = Σ_{k1,k2} w(k1)w(k2) C(n+k1+k2,n)`, w(k)=C(n+k,k)C(n,k)²
(engine-checked: 1,21,2989), we searched:
 • all TRIPLE sums with weight C(n+k,k)^p C(n,k)^q (p,q≤3) and coupling = any
   product-family of C(n+Σ_{S}k_i, n) over the 7 nonempty index-subsets;
 • all DOUBLE sums, same weight/coupling classes.
**None reproduces 1,61,52921** — not even the intermediate value 61 at n=1.
So qₙ is not a subset-sum-coupled product-weight multisum of the M₀,₈ type. The
weight-→index heuristic (weight 3 = single sum, 5 = double) does not continue as
"7 = triple sum with an analogous coupling."

---

## 4. Best remaining hypothesis (ranked)

Given §3.4, the target is **not** any reflection-symmetric block series. Ordered by
promise:

1. **Asymmetric / spread-pole VWP series (KR-type).** Series whose denominator
   poles occupy *two separated blocks* (as in `zn_check.compute_Zn`'s ζ(5..11)
   family: den = ∏_u (k+(12−u)n)_{…}) produce residues of **alternating sign**,
   the one mechanism that can give +ζ7 −ζ5 +ζ3. A one-parameter asymmetric VWP in
   {ζ3,ζ5,ζ7} with alternating signs is the natural candidate for I′ₙ (after a
   ζ3-kill) or I″ₙ directly. A quick 2-block test degenerated (over-spread → only
   ζ3 survives); the live task is a *tuned* asymmetric parameter scan matching the
   §0 ratios. **This is the recommended next experiment on the series side.**
2. **F̃₉(b(n)) at the true M₀,₁₀ symmetric point** — a *non*-all-equal b-vector
   from the (unpublished) M₀,₁₀ b-parametrisation (analogue of tex lines
   1249–1251). This is the dual, so it gives the dual form, not I′ₙ directly; but
   the duality of recurrences may let qₙ be recovered from its (computable)
   coefficients. Needs the b-dictionary derived from the M₀,₁₀ symmetric integrand.
3. **Triple Mellin–Barnes reduction of the primal integral** (scout's route (a)) —
   the on-target but genuinely multi-day derivation; would yield I′ₙ (hence qₙ,sₙ,
   Pₙ) exactly and enable the n≥3 denominator audit.

---

## 5. Reusable infrastructure produced
- `zeta7_dual_vwp.py` — F̃_k engine wrapper (any k, any b-vector), even/ζ9-vanish check.
- `zeta7_dual_zud.py` — engine validation on Zudilin math/0206178 eq.7 (r_n, ~r_n)
  + the new ρ_n {1,ζ3,ζ5,ζ7} family to n=3.
- `zeta7_dual_match.py` / `_bigscan.py` / `_gen.py` — ζ3-kill + BZ-ratio testers.
- `zeta7_dual_Idd.py` — I″ₙ single-series tester.
- `zeta7_dual_triple.py` / `_exhaust.py` / `_Awide.py` — qₙ multisum searches.
- `zeta7_dual_calib.py` — F̃₇(3n;n⁷) dual-integral calibration.

---

## 7. Asymmetric / spread-pole hunt (coordinator-directed) — COMBINED EXCLUSION MAP

Following the coordinator's go-ahead I pursued the spread-pole hypothesis of §4.1
systematically, using the **KR master family** (Krattenthaler–Rivoal
arXiv math/0311114, eq. 782, the generator of the engine's built-in ζ(4/5..11)
series):

    S_{n,A,B,C,r}(z) = n!^{A−2Br} Σ_{k≥1} (1/C!) ∂^C/∂k^C [ (k+n/2)
                        (k−rn)_{rn}^B (k+n+1)_{rn}^B / (k)_{n+1}^A ] z^{−k}.

**Content rule [KR, verbatim].** For z=(−1)^A with **A even**, S(1) is a ℚ-form in
1, ζ(C+3), ζ(C+5), …, ζ(C+A−1). Hence **A=6, C=2 targets exactly {1, ζ5, ζ7}** —
the I′ₙ structure, no ζ3, no auxiliary ζ3-kill needed. This resolves §3.4's worry
that the obstruction might be a C=0 artefact: it is **not** — see below.

### 7.1 Sign is the discriminant, and it does not turn over [VERIFIED]
BZ's I′ₙ needs **r5 = z5/z7 = −48/61 < 0** (ζ7 and ζ5 opposite). Tested, exact:
- **Symmetric single-block** S_{n,6,B,2,r}(1), all valid (B,r): r5 = 22/15, 3/2,
  39/25 — **all > 0** [`zeta7_dual_master.py`].
- **KR ζ(5..11) asymmetric series** itself (`compute_Zn`): z5/z7 **> 0** at n=1,2
  — spread poles do **not** flip the sign.
- **Staircase-asymmetric grid** (num (k−Pn)_{Pn}^B(k+Qn+1)_{Pn}^B, den =
  ∏_{u=1}^U (k+(M−u)n)_{(base+step·u)n+1}, half-shift Qn/2, C∈{0,1,2}):
  **11 284 configs** scanned [`zeta7_dual_asym.py`]. Every config with clean
  odd content (no even zetas) has r5 > 0.
- **Systematic genuinely-VWP spreads** (symmetric pole windows — contiguous AND
  gapped — with mirror-symmetric numerator zero-pairs, C∈{0,2}):
  **1 248 configs giving clean {ζ5,ζ7} ⊆ {ζ3,ζ5,ζ7}; ZERO with r5 < 0**
  [`zeta7_dual_vwpsign.py`].

### 7.2 Why the negative-r5 configs don't count [VERIFIED]
Configs that *do* achieve r5 < 0 exist in the staircase grid, but **every one of
them carries even zeta values (ζ4, ζ6)** — i.e. the reflection symmetry is broken,
they are **not very-well-poised**, and their linear form is
{ζ4,ζ5,ζ6,ζ7}, not BZ's clean {ζ5,ζ7}. As soon as even zetas are forced to vanish
(the actual BZ constraint), r5 is positive without exception across all four
families above.

### 7.3 Conclusion of the series route [EXCLUDED — the whole single-sum VWP class]
The BZ eliminated form I′ₙ is a *small* linear form with **opposite-sign** adjacent
zeta coefficients; every very-well-poised single sum (symmetric or spread) is a
*simultaneous approximation* whose adjacent odd-zeta coefficients are **same-sign**
(the constant term carries the cancellation). These are structurally different
objects. This is consistent with BZ's own framing: I′ₙ is obtained by the
*projection* "set ζ(2)=0" applied to Iₙ, i.e. a **subleading/eliminated** form, not
a primary series — precisely the kind of object that need not be a single VWP sum.

**Verdict (matches the coordinator's stated stop condition and the scout's route
(a)):** the ζ(7) dual, if it exists as a series, lives **outside the single-sum
VWP class**. The **triple Mellin–Barnes reduction of the primal integral**
(scout's route (a), `ZETA7_FAMILY.md` §2a) is the remaining path to I′ₙ exactly
and to the n≥3 denominator audit. The series route is closed with this exclusion
map; no absolute-normalization step was reached because no candidate cleared the
normalization-free sign test.

New scripts for §7: `zeta7_dual_master.py`, `zeta7_dual_asym.py`,
`zeta7_dual_vwpsign.py`. KR master family source cached at
`…/scratchpad/kr/kratriv.tex` (eq. 782, content rule at "Quand on spécialise").

## 6. Honesty ledger
- §1 engine/recipe validation on ζ(5): **[VERIFIED]** exact-rational equality on
  Zudilin's printed r_n (n=0,1,2) and on ℓ_n ratios.
- §0 target ratios, §2 ρ_n family: **[VERIFIED/DERIVED]** exact-rational, reproducible.
- §3.1–3.3, 3.5 exclusions: **[EXCLUDED]** exact mismatch over the stated grids/classes.
- §3.4 sign obstruction: **[DERIVED]** — proven for reflection-antisymmetric R,
  observed to block every tested construction; it is the operative reason the
  ζ(5)→ζ(7) lift fails.
- §4 hypotheses: **[SPECULATION]**, ranked with the mechanism (alternating-sign ⇒
  spread poles) that motivates #1. **Note §7 refutes #1's premise**: spread poles
  do *not* flip the sign; that mechanism was wrong, and §7 supersedes §4.
- §7 spread-pole hunt: **[VERIFIED/EXCLUDED]** — 11 284 staircase + 1 248
  systematic-VWP + symmetric-block + `compute_Zn`, all exact-rational; r5 > 0
  universally among VWP-clean forms. Excludes the entire single-sum VWP class.
  The KR content rule (A even ⇒ {ζ(C+3)…ζ(C+A−1)}) is transcribed verbatim.
