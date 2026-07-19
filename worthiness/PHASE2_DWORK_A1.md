# Phase-2 (DWORK): denominator-free vector form + the a=1 band

Worker note, 2026-07-19 (Opus, executing Sol's proof program STEPs 1–3).
Companion to `PHASE2_BAND_V.md` (V1–V5), `PHASE2_BAND_BLUEPRINT.md`, `LEMMA_CB.md`.

Exact `Fraction`/integer arithmetic throughout. **HONESTY STANDARD: every claim
below marked VERIFIED is a finite exact-arithmetic check over an explicitly
stated grid — evidence, never a theorem. Claims marked PROVED cite a prior
theorem. The a=1 band is NOT proved; its precise reduced statement is given.**

Scripts (new, runnable, usage lines at top):
- `dwork_vecform.py`   — STEP 1 (vector form) + STEP 3 (coupled pair). Run: `python3 dwork_vecform.py 60`.
- `dwork_a1_band.py`   — STEP 2 (a=1 decomposition, block tools, reduced statement). Run: `python3 dwork_a1_band.py 29 60`.

---

## 0. Notation (source of truth: `lemma_cb_explore.py`)

For each level `n`, the 2×3 Zudilin period matrix is `[[u,w,v],[ũ,w̃,ṽ]]`
(`u=Σa_{5,j}`, `w=Σa_{3,j}`, `v=Σ_{i,j}a_{i,j}H_j^{(i)}`, tildes via the companion
map `ã_{i,j}=j(n−j)a_{i,j}+(2j−n)a_{i+1,j}−a_{i+2,j}`). Its three 2×2 minors are

    q_n    = u w̃ − ũ w          ((1,2)-minor)  — the ζ(5) determinant
    p_n    = w̃ v − w ṽ          ((1,3)-minor)  — the ζ(3)-eliminated numerator
    p̃_n    = u ṽ − ũ v          ((2,3)-minor)  — the third companion

Write **V_n := (q_n, p_n, p̃_n)** (= ±row₁×row₂, the period vector). Set
`a := ⌊n/p⌋`, `κ := ord_p C(2n,n)`, `L := ord_p(d_n) = ⌊log_p n⌋`.

**Fact (q_n ∈ ℤ).** `q_n` is an *integer* for every `n` (VERIFIED n≤60; it is
`±C(2n,n)·Q_n` with `Q_n` the Brown–Zudilin integer cellular double-binomial
coefficient — the (FREE) fact of `LEMMA_CB §3.1b`). `p_n, p̃_n ∈ (1/2 d_n^5)ℤ`
with `A_n := 2 d_n^5 p_n ∈ ℤ` (Zudilin). The base minors:
`q_1=42, p_1=87/2, p̃_1=101/2`, giving `p_1/q_1 = 29/28`, `p̃_1/q_1 = 101/84`;
`q_2=−17934`, `q_3=14290980`.

---

## 1. STEP 1 — the denominator-free vector form (VERIFIED)

The measured (DWORK) descent (`PHASE2_BAND_V` V5) is stated on the **ratios**
`ρ_n=p_n/q_n`, `σ_n=p̃_n/q_n` with rational constants `p_a/q_a=29/28`,
`p̃_a/q_a=101/84`, whose **denominators carry the "exceptional" primes**
(`7 | 28 = den(29/28)`, because `q_1 = 42 = 2·3·7`). Dividing by `q_a` is the
source of the exceptional-prime headache.

**Cross-multiply by the integer `q_a`.** Define the p-adic integers

    X_p := q_a · p^5 · p_n − p_a · q_n          (VEC)
    X_s := q_a · p^3 · p̃_n − p̃_a · q_n         (VEC~)

**Uniform floor law (VERIFIED — 432 rows, single Frobenius step a=⌊n/p⌋<p,
all primes 5≤p≤60, n≤60, `dwork_vecform.py`):**

>   **ord_p(X_p) ≥ ord_p(q_a) + 2   and   ord_p(X_s) ≥ ord_p(q_a) + 2.**

Zero violations. The floor is TIGHT (`= ord_p(q_a)+2`) at `p=7` and `p=11`;
surplus `+3` at all `p≥13`.

**This is the reframing the campaign asked for.** The exceptional primes `p|q_a`
are **not a singularity**: they enter only through `ord_p(q_a)>0`, i.e. the
cross-multiplier `q_a` becomes a **non-primitive lattice vector mod p** (a lattice
change), and the single floor law absorbs them uniformly. No separate exceptional
normalization; no rational-number denominators (`28`, `84`) appear anywhere.
At `p=7`, `q_1=42` contributes `ord_7(q_1)=1` and indeed `ord_7(X_p)=3=1+2` — the
`7` sits inside the integer `q_1`, exactly as a lattice index, and is carried
correctly.

### 1.1 Pure-integer (lattice) incarnation (VERIFIED)

With `A_m := 2 d_m^5 p_m ∈ ℤ`, `q_m ∈ ℤ`, and `d_a | d_n` (so `e := d_n/d_a ∈ ℤ`),
the quantity

    I := q_a · p^5 · A_n − e^5 · A_a · q_n   ∈  ℤ

is a genuine integer, and (VERIFIED — 244 rows, p≥5, n≤44, single step, TIGHT):

>   **p^{5L + ord_p(q_a) + 2}  |  I.**

No rationals at all: a pure integer divisibility, with exceptional primes carried
by the integer factor `q_a`.

### 1.2 Relation to (DWORK) and to the target

(VEC) is exactly `q_n q_a·(p^5 ρ_n − ρ_a)`, so it is the cross-multiplied form of
`p^5 ρ_n ≡ ρ_a (mod p^k)`. For **non-exceptional** `p` (p∤q_a), dividing (VEC) by
`q_a` recovers `p^5 ρ_n ≡ ρ_a (mod p^2)`, whence (using ord_p p_a=0, ord_p q_n≥κ)
`ord_p(p_n) ≥ min(2,κ) − 5`, giving the (CB) target `ord_p(p_n) ≥ κ−5` for the
band `κ≤2`. For **exceptional** `p`, the clean closure additionally uses the
`q_n`-compensation `ord_p(q_n) > κ` (`PHASE2_BAND_V` V5.3): the combined target
`ord_p(p_n) ≥ κ−5L` is VERIFIED with 0 failures (all p≥5, n≤60), but it is *not*
derivable from (VEC) alone at exceptional `p` — see §5, correction (iii).

---

## 2. STEP 2 — the a=1 band (n = p+r):  reduced statement

Target (Sol's minimal theorem, eq. 15/16 of `ZETA7_DWORK_FROM_SOL.txt`), the
a=1 slice of (VEC):

    (VEC-a1)   ord_p( q_1 p^5 p_n − p_1 q_n ) ≥ ord_p(q_1) + 2 ,   n = p+r, 0≤r<p,

and the `p̃` companion (VEC~-a1). VERIFIED (124 rows, all p, n≤60): zero
violations of the uniform `ord_p(q_1)+2` floor.

### 2.1 Head-window decomposition (VERIFIED exact)

`H_j^{(i)} = Ĥ_j^{(i)} + [j≥p]p^{−i}` (`Ĥ` p-integral; the only multiple of `p`
in `[1,n]` is `p`). With `S_i^head := Σ_{j=0}^r a_{i,j}` and reflection P1
(`S_i^tail = (−1)^{i+1}S_i^head`),

    v = Sing + resid,    Sing := Σ_{i=1}^6 (−1)^{i+1} p^{−i} S_i^head,
    resid = Σ_{i,j} a_{i,j} Ĥ_j^{(i)}.

VERIFIED (exact equality, all band rows): the H-tail singular part is removed
exactly; **ord_p(resid) ≥ −2** across the band. (Ladder note — a correction —
in §5(i).)

### 2.2 What is PROVED / VERIFIED / OPEN for the a=1 band

| Ingredient | Status |
|---|---|
| `q_n ∈ ℤ` (BZ cellular integrality) | **PROVED** (cite BZ) + VERIFIED n≤60 |
| `v = Sing + resid` exact; `ord(resid) ≥ −2` | **VERIFIED** exact, band |
| (VEC-a1)/(VEC~-a1) uniform floor `ord ≥ ord(q_1)+2` | **VERIFIED**, 124 rows, 0 fail |
| factorial p-block identity `(Ap+b)! = Φ(A,b)` (Sol eq 3–4) | **VERIFIED** exact, 380 cases (A≤3) |
| full-block inputs `v_p(H_{p−1}^{(t)})` (Sol eq 12), reversal id (eq 13) | **VERIFIED** p≥11 (eq 13 to working precision p^5) |
| **the deep head-window congruence (HW), = the "two missing digits"** | **OPEN** |

**The single remaining obligation (OPEN).** For clean `p≥11`, every
`r∈[⌈p/2⌉,p−1]`:

    (HW)   p^5·Sing − (29/28)·u − (101/84)·p^2·w  ≡  0   (mod p^3)

(and (HW~)). Equivalently the denominator-free (VEC-a1). The three normalized
digits split (Sol §1.7, matching `PHASE2_BAND_V` V4C):
- **p^0 digit**: forced by the window `E_M` relations — VERIFIED, but `E_M`
  forces *only* this digit (`lemma_cb_band_v4` part C, honest NEGATIVE).
- **p^1 digit**: predicted to vanish via the reversal identity (eq 13) coupling
  `H_1/H_2` and `H_3/H_4` — NOT carried out to a closed proof.
- **p^2 digit**: predicted to vanish via the p^3 block-binomial
  (Ljunggren/Jacobsthal, Sol eq 14) combined with the Bell derivative terms
  `D_1D_2, D_3` — NOT carried out.

These last two vanishings are a **concrete finite symbolic calculation per
residue class `r`** (two `j`-blocks, factorial-block index `A≤3`, Bell
derivatives to order 5). It is **not** completed here. Sol's parallel note
reaches the same boundary: "This is a concrete calculation, not yet a theorem."

So the a=1 band is: **theorem modulo the two-digit head-window vanishing (HW),
which the `E_M` machinery provably cannot supply and which requires the
Wolstenholme-block reversal (eq 13) + block-binomial (eq 14) inputs verified
above.** The block tools needed are now all present and checked; the remaining
work is the assembly, which is a bounded computation, not a search.

---

## 3. STEP 3 — the coupled pair (p_n, p̃_n): a diagonal Frobenius twist (VERIFIED)

Scale the period point projectively by `T := diag(1, p^5, p^3)`:

    T·V_n = (q_n, p^5 p_n, p^3 p̃_n)   is p-adically PARALLEL to   V_a = (q_a,p_a,p̃_a).

Parallelism ⟺ all three 2×2 minors are small. Two are (VEC),(VEC~); the third,

    (COUP)  X_23 := p_a p^3 p̃_n − p̃_a p^5 p_n,   ord_p(X_23) ≥ ord_p(q_a)+2  (p≥11),

is a **consequence** of the first two (rank-1 identity: the three minors belong to
a matrix with p-adically dependent rows). VERIFIED (202 rows). The SAME scalar
`λ = q_n/q_a` governs **both** off-diagonal slots (VERIFIED: `ord(λ_i−1)` large in
both), so the operative "Frobenius matrix" is the **diagonal twist `T`**, not a
genuinely triangular 2×2 — the (p_n, p̃_n) coupling is automatic/projective.

**Caveat (agreeing with Sol §1.9).** This is a statement about the projective
period point, NOT yet a proved rank-3 Frobenius *matrix* theorem: upgrading it
requires a congruence for the `q`-coordinate (plain Lucas for `q_n` FAILS — V5.4)
or the two-digit **cocycle law** (matrix from `abp^2+sp+r` = product of r-step and
s-step matrices). Not attempted here.

---

## 4. Grids (explicit)

- STEP 1 (VEC/VEC~ floor): p prime in [5,60], n∈[p,60], single step `a=⌊n/p⌋<p` — 432 rows.
- STEP 1 (integer lattice `I`): p∈[5,43], n∈[p,44], single step — 244 rows.
- STEP 2 (a=1): p∈[5,29], n∈[p,60] (full a=1 range r∈[0,p−1]) — 124 rows;
  decomposition on the κ=1 band core; block identity Φ for p≤23, A≤3 (380 cases);
  Wolstenholme/reversal p∈[11,43].
- STEP 3: p∈[5,40], single step — 202 rows.
- Combined target `ord_p(p_n) ≥ κ−5L`: p∈[5,60], n≤60, 0 failures (via `dwork_vecform` + V5).

Finite checks are evidence; nothing here is settled beyond the stated grids.

---

## 5. Corrections to recorded campaign claims

**(i) `PHASE2_BAND_V.md`, V1 — ladder `ord_p(S_i^head)=i−5` "clean primes p≥11,
uniform".** INACCURATE at `p=11`. The V1 script's own output shows at `p=11`
(e.g. n=17,18,…,21) the ladder is `[S_2..S_6] = [−2,−1,−1,0,1]`, i.e. `S_2, S_3`
are **one order shallower** than `i−5=[−3,−2,−1,0,1]`, and `ord(resid)` reaches
`−1` and even `0` (n=18), not `−2`. The clean `i−5` ladder and `resid=−2` hold
only for **p≥13**. `p=11` is a boundary/edge case. This does **not** affect any
vector-form result: (VEC-a1) holds at `p=11` with 0 violations (floor tight at
`+2`). It only corrects the descriptive ladder statement. (Verified in
`dwork_a1_band.py` (A), cross-checked by re-running `lemma_cb_band_v1.py 17 24`.)

**(ii) `PHASE2_BAND_BLUEPRINT.md` breakthrough addendum — DWORK stated as
`p_n/q_n ≡ (p_a/q_a)·p^{−5} mod p^θ`.** The denominator-carrying `p_a/q_a=29/28`
makes `7` exceptional. The **denominator-free** restatement (VEC) removes this:
`ord_p(q_a p^5 p_n − p_a q_n) ≥ ord_p(q_a)+2`, uniform in the exceptional primes.
Not a contradiction — a cleaner equivalent form (recommended as the primary
statement; matches Sol eq 15/16).

**(iii) `PHASE2_BAND_V.md`, V5.1 floor law `k ≥ 2−κ` and Sol eq 15
`v_p(Δ_5) ≥ v_p(q_1 q_n)+1`.** Both are correct in the **clean band (p≥11, κ=1)**,
but the `q_n`-scaled form (`+1` above `v_p(q_1 q_n)`) is **too strong at
exceptional/edge p** where `q_n` is over-divisible: it has 4 violations on the
full a=1 grid, all at `p=7` (n=8,9,11,12; `ord_p(q_n)∈{2,3}`, so
`v_p(q_1 q_n)+1` over-predicts). The **cross-prime-uniform** floor is the
`q_1`-only form `ord_p(Δ) ≥ ord_p(q_1)+2` (0 violations everywhere). Recommend
adopting the `q_1`-only floor as the uniform statement. (This is Sol's own
prediction P5 confirmed: at `p=7` the `q`-coordinate supplies compensation.)

---

## 6. Reconciliation with Sol's `ZETA7_DWORK_FROM_SOL.txt`

Sol's note (sec T1) and this derivation **agree on the architecture**:

- **STEP 1 object.** Sol's `Δ_5 = q_1 p^5 p_n − p_1 q_n` (eq 15) is exactly my
  `X_p`. AGREE this is the right denominator-free object. **Refinement:** Sol's
  floor `v_p(Δ_5) ≥ v_p(q_1 q_n)+1` (eq 15) coincides with mine in the clean
  band but over-predicts at exceptional `p=7`; the uniform floor is
  `ord_p(q_1)+2` (§5(iii)). Sol's eq 15 for `p|q_1q_n` says "keep the integer
  determinant, never invert `q_n` mod p" — my integer lattice form §1.1 is
  precisely that.
- **The block tools Sol prescribes are all present and VERIFIED:** the factorial
  p-block identity `(Ap+b)!=Φ(A,b)` (eq 3–4) is exact; the full-block harmonic
  inputs (eq 12) and reversal identity (eq 13) hold to working precision.
  Sol's predicted mechanism for the two missing digits (p^1 via eq 13 coupling,
  p^2 via eq 14 + Bell terms) is the OPEN assembly.
- **STEP 3.** Sol §1.9 independently reaches my conclusion: the ratio congruences
  give the diagonal weights `diag(1,p^5,p^3)` and the projective prediction
  (Sol eq 19 = my parallelism), but do **not** yet prove a Frobenius *matrix*
  theorem — needs a q-congruence or the cocycle law. AGREE fully; I did not
  claim a matrix theorem.
- **Did Sol's predicted ingredients match what I needed?** Yes for the
  *reduction* (his Δ_5/Δ_3, the two-block split, the Wolstenholme reversal and
  block-binomial menu are exactly the operative tools, and each I could check
  exactly). **No disagreement of substance.** The one quantitative correction is
  the floor normalization (q_1-only, not q_1·q_n) at exceptional primes, which
  Sol's own P5 anticipates. Neither of us closes the two-digit vanishing (HW):
  it remains the single open finite calculation.

---

## 7. Bottom line

- **STEP 1 (vector form): delivered and VERIFIED.** `(VEC)/(VEC~)`:
  `ord_p(q_a p^5 p_n − p_a q_n) ≥ ord_p(q_a)+2`, uniform over all p≥5 including
  the exceptional `p|q_a` (which become a lattice change, tight at p=7,11); plus
  the pure-integer lattice divisibility `p^{5L+ord q_a+2} | I`. This is the
  requested denominator-free reframing.
- **STEP 2 (a=1 band): reduced, not proved.** Reduced to the single explicit
  head-window congruence `(HW)` / `(VEC-a1)`; the decomposition and all Sol-block
  tools are verified; the `E_M` machinery provably supplies only the p^0 digit;
  the remaining two-digit vanishing (Wolstenholme reversal + block-binomial) is a
  bounded symbolic calculation, left OPEN (as in Sol's note).
- **STEP 3 (coupled pair): the coupling is projective/diagonal**, third minor is
  a consequence (VERIFIED); a genuine Frobenius-matrix theorem is not claimed.
- **Corrections:** V1 ladder is p≥13 not p≥11; the uniform Dwork floor is the
  `q_1`-only form (exceptional-prime-safe).
