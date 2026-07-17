# The Central-Binomial Cancellation Lemma — proof, reduction, and obstruction map

Working note, 17 July 2026. Companion to `SYMMETRIC_ZETA5_TARGET.txt`.

Exact arithmetic throughout. Every congruence below was verified over a large
`(n,p)` sample **before** any proof attempt (`lemma_cb_*.py`). Finite checks are
recorded as evidence, never as theorems (repo honesty standard).

---

## 0. The lemma

For Zudilin's ζ(5) sequences (arXiv:math/0206178), with

    A_n = 2 d_n^5 p_n ∈ ℤ    (Zudilin's denominator theorem; d_n = lcm(1..n)),

the target `12 d_n^5 P_n ∈ ℤ` is equivalent (note §2) to

    binom(2n,n) | 6 A_n,   i.e.   ord_p(A_n) ≥ ord_p binom(2n,n) − ord_p(6)   (CB)

for every prime `p`. Here `p_n = w̃_n v_n − w_n ṽ_n` is the ζ(3)-eliminated
numerator (note §4), where `w_n, w̃_n` are the ζ(3) coefficients and `v_n, ṽ_n`
the rational parts of Zudilin's two companion forms `r_n = Σ_k R_n(k)` and
`r̃_n = Σ_k −k(k+n)R_n(k)`.

The account below splits `(CB)` at the primes into the clean interval
`n < p ≤ 2n` (**Phase 1**) and `p ≤ n` (**Phase 2**).

---

## 1. Main result of this note (Phase 1, reduced to one congruence)

**Theorem A (reduction — proved).** Fix a prime `p` with `n < p ≤ 2n` and `p ≥ 5`.
Then `ord_p binom(2n,n) = 1`, `ord_p(6) = 0`, and

    w_n ≡ 0 (mod p)  and  w̃_n ≡ 0 (mod p)   ⟹   ord_p(A_n) ≥ 1,

i.e. `(CB)` holds at `p`.

*Proof.* Because `n < p ≤ 2n`, exactly one multiple of `p` lies in
`{n+1,…,2n}` (namely `p`; `2p > 2n`), and none in `{1,…,n}`, so
`ord_p binom(2n,n) = ord_p(2n)! − 2·ord_p n! = 1 − 0 = 1`; and `p ≥ 5` gives
`ord_p(6) = 0`. Since `p` is odd and `p > n` we have `ord_p(2 d_n^5) = 0`, hence
`ord_p(A_n) = ord_p(p_n)`.

Every `a_{i,j}` is `p`-integral: it is a ℤ-combination of the integers
`(n!)^4`, `(n/2−j)`, `(n±·)` and of inverse powers of the integers `(m−j)` with
`|m−j| ≤ n < p`; no denominator carries `p`. The harmonic numbers `H_j^{(i)}`
with `j ≤ n < p` are likewise `p`-integral. Therefore `v_n = Σ_{i,j} a_{i,j}
H_j^{(i)}` and `ṽ_n` are `p`-integral, i.e. `ord_p(v_n), ord_p(ṽ_n) ≥ 0`.
With `ord_p(w_n), ord_p(w̃_n) ≥ 1` by hypothesis,

    ord_p(p_n) = ord_p(w̃_n v_n − w_n ṽ_n) ≥ 1.   ∎

So on the whole clean interval, **`(CB)` reduces to the single congruence**

    (W)   w_n ≡ 0 (mod p)  and  w̃_n ≡ 0 (mod p),   for all primes n < p ≤ 2n, p ≥ 5.

This is stronger than the note's route (A) (`p`-adic *dependence* of the vectors
`(w,w̃)` and `(v,ṽ)`): experimentally the `w`-vector is not merely dependent on
the `v`-vector, it **vanishes outright** mod `p`. `v_n, ṽ_n` are generic units.

**Status of (W): massively verified, not yet proved.** Verified with exact
`p`-adic valuations over **855 pairs** `(n,p)`, `n ≤ 90`, `n<p≤2n`, `p≥5`:
zero failures (`lemma_cb_wcong.py`). Valuation distribution:
`ord_p(w_n) ∈ {1,2}` (16 twos), `ord_p(w̃_n) ∈ {1,2}` (7 twos); the excess
`ord = 2` cases are sporadic apart from the systematic `t = p−n = 1` column.

**Integer reframing (matches Zudilin's own denominator bound).** Zudilin
(math/0206178) states for the linear form `r_n = u_n ζ(5) + w_n ζ(3) − v_n`:
`2u_n ∈ ℤ`, `2 D_n^2 w_n ∈ ℤ`, `2 D_n^5 v_n ∈ ℤ` (`D_n = d_n = lcm(1..n)`).
Verified exactly here that `2 d_n^2 w_n ∈ ℤ` and `2 d_n^2 w̃_n ∈ ℤ` (both, `n<40`;
this is the *tight* power — `2 d_n^1 w_n` already fails at `n=4`). Writing the
integers `W_n := 2 d_n^2 w_n`, `W̃_n := 2 d_n^2 w̃_n` and the "large-prime part"
`B_n^{high} := ∏_{p ∈ (n,2n], p ≥ 5} p`, congruence `(W)` is exactly the integer
divisibility

    B_n^{high} | W_n   and   B_n^{high} | W̃_n,

verified for all `n < 40` (`lemma_cb_wframe`). Note this is **strictly weaker
than `binom(2n,n) | W_n`**, which is *false* (holds only sporadically:
`n = 1,4,16,…`). Only the window primes, each to order 1, divide `W_n`.

---

## 2. Structural results that ARE proved

These are complete, char-0 / Kummer proofs; each is also verified exactly.

**P1. Reflection symmetry.** `R_n(−n−k) = −R_n(k)` (direct: each factor group
is invariant up to the stated sign; the `(n!)^4 / ∏(k+j)^6` part is symmetric,
`(k+n/2)` flips sign, and the two order-`n` products swap with a combined
`(−1)^{2n}=+1`). Expanding both sides at the pole `k=−j` gives

    a_{i, n−j} = (−1)^{i+1} a_{i,j},   for 1 ≤ i ≤ 6, 0 ≤ j ≤ n.   (P1)

Verified exactly (`lemma_cb_verify.py`, V2: 0 failures, `n ≤ 40`).

**P2. Even-layer vanishing (over ℚ).** With `S_i := Σ_{j=0}^n a_{i,j}`, pairing
`j ↔ n−j` in (P1) gives `S_i = (−1)^{i+1} S_i`, so

    S_2 = S_4 = S_6 = 0.

Also `S_1 = 0`: `S_1` is the sum of all residues of `R_n`, which decays like
`(n!)^4 k^{−4n−5}` at `∞`, so the residue sum vanishes. Thus in
`r_n = S_5 ζ(5) + S_3 ζ(3) − v_n` only the two odd layers survive:
`u_n = S_5`, `w_n = S_3`. Verified exactly (V3: 0 failures). These are exactly
the well-poised vanishings; they explain why the ζ(3) coefficient `w_n = S_3` is
the *only* even-index obstruction to remove, and why `(P1)` alone cannot kill it
(for odd `i`, (P1) is symmetric, not antisymmetric).

**P3. Pole-order (ord_p) accounting.** From the closed form
`a_{6,j} = (−1)^n (n/2−j) binom(n,j)^6 binom(n+j,n) binom(2n−j,n)`, for a prime
`p = n+t`, `n < p ≤ 2n`, `p ≥ 5`, Kummer's carry count gives

    ord_p binom(n+j,n)  = [ j ≥ t ],
    ord_p binom(2n−j,n) = [ j ≤ n−t ],
    ord_p(n/2−j) = ord_p binom(n,j) = 0,

hence `ord_p(a_{6,j}) = [j ≥ t] + [j ≤ n−t]`, which is `0` on the open window
`(n−t, t)` — empty precisely when `p ≤ 3n/2` (the entire top layer then vanishes
mod `p`). Verified for all `p ≥ 5` (V1: 0 failures; the sole "mismatch" is the
irrelevant `p = 2`). **Caveat that shaped the whole approach:** the lower layers
`a_{3,j}` have *full* support mod `p` (differentiation via
`a_{i,j} = B_j^{(6−i)}(−j)/(6−i)!`, `B_j = (k+j)^6 R_n`, spreads the mass; the
log-derivative `B_j'/B_j` picks up a single `1/p` term at `m = p−j` or
`m = t+j`). So `(W)` is a genuine **global sum-cancellation**, not a support
collapse — confirmed by the mod-`p` tables in `lemma_cb_window.py`.

**P4. Moment identities (exact tools for the cancellation).** For every `m` with
`k^m R_n(k)` decaying at `∞` (i.e. `m < 4n+5`, so all relevant `m`), the residue
sum of `k^m R_n` vanishes, giving

    Σ_{l=0}^m binom(m,l) (−1)^{m−l} M_{l+1, m−l} = 0,   M_{i,r} := Σ_j j^r a_{i,j}.   (★)

In particular `m = 2` yields the exact identity (verified `n ≤ 24`)

    w_n = 2 Σ_j j·a_{2,j} − Σ_j j²·a_{1,j}.

These relations are the natural handles for a proof of `(W)`: they express the
even-layer coefficient `w_n` through the (symmetry-controlled) layers
`a_{2,j}, a_{1,j}`. They constrain but do not by themselves close `(W)`.

**P5. Unified form of (W).** `w_n` and `w̃_n` are the ζ(3) coefficients of
`Σ_k Q(k) R_n(k)` for `Q = 1` and `Q = k(k+n)`, both of which satisfy the
well-poised symmetry `Q(−n−k) = Q(k)`. So `(W)` is one instance of:

> **Conjecture (W′).** For every polynomial `Q` with `Q(−n−k) = Q(k)`, the ζ(3)
> coefficient of `Σ_{k≥1} Q(k) R_n(k)` is `≡ 0 (mod p)` for all primes
> `n < p ≤ 2n`, `p ≥ 5`.

---

## 2.5 Does Zudilin's published arithmetic already prove (W)?

Checked against Zudilin math/0206178 (our exact `q,p,p̃` sequences) and the
general machinery of math/0206176 §§8–9. **Verdict: no — (W) is not a corollary.**

- The published coefficient bounds are **lcm/denominator** statements:
  `2 D_n^2 w_n ∈ ℤ` (and the Lemma-4-type inclusions of 0206176 use powers of
  `D_n = lcm(1..n)`). Such a bound says the *denominator* of `w_n` divides
  `2 D_n^2`, whose prime factors are all `≤ n`. Equivalently it gives
  `w_n` is `p`-integral for every `p > n` — but it asserts **nothing** about the
  *numerator* `W_n` being divisible by primes `p ∈ (n,2n]`. Those primes do not
  appear in `D_n` at all, so no power of `D_n` can detect them.
- The `Φ_n` prime-savings construction of 0206176 reduces the **leading**
  coefficient's denominator (for the ζ-irrationality estimate) by removing
  primes `p` with `{n/p}` in a savings window. That is a denominator *reduction*
  on the top-weight slot, not a numerator *divisibility* on the ζ(3) slot. It
  does not yield `p | W_n`.
- Direct disproof that a stronger published-style statement holds:
  `binom(2n,n) ∤ W_n` in general (§1). So (W) cannot be packaged as "the central
  binomial divides the ζ(3) coefficient"; it is precisely the window-restricted
  divisibility `B_n^{high} | W_n`, which is new.

**Why the termwise floor-count (route 2) does not close it directly.** The
normal form of the coefficient is
`w_n = Σ_{j=0}^n a_{3,j} = Σ_{j=0}^n (1/6) G_j'''(−j)`, with
`G_j(k) = (n!)^4 (k+n/2) ∏_{m=1}^n (k−m)(k+n+m) / ∏_{m≠j}(k+m)^6`.
Expanding the third derivative by the log-derivative of `G_j` gives
`a_{3,j} = a_{6,j} · (b_3 + b_1 b_2 + b_1^3/6)`, a **binomial product `a_{6,j}`
times a weight-≤3 harmonic polynomial** in the `b_r = ψ_r(−j)/r!`. The harmonic
factors carry `1/p` poles at the window boundary, so the individual integers-
scaled terms `2 d_n^2 a_{3,j}` are **not** integers (note §8) — floor-counting
`ord_p ≥ 1` termwise is therefore impossible; the `p`-divisibility is a global
sum cancellation. Closing (W) by floor-counting requires first re-expressing
`W_n` as a genuine integer combination of binomial products **without harmonic
denominators** — the Krattenthaler–Rivoal multiple-sum normal form (route B).
That re-expression is the concrete open sub-task; the derivation above
(`a_{3,j} = a_{6,j}·(b_3+b_1b_2+b_1^3/6)`, valid for `j ≠ n/2`; the middle pole
`j = n/2` at even `n` has `a_{6,j}=0` and needs a separate limiting form) is its
exact, verifiable starting point — checked in `lemma_cb_wframe.py` (F3).

---

## 3. Phase 2 — primes `p ≤ n`

Here `ord_p binom(2n,n)` can exceed 1 and interacts with `d_n^5` and with the
carries of `binom(2n,n)`. Exact ledger `ord_p(A_n)` vs `ord_p binom(2n,n) −
ord_p(6)` (`lemma_cb_verify.py`, V5):

- **`n ≤ 60`: zero failures**, and **206 tight cases** (`slack = 0`, requirement
  `> 0`). The tight cases prove the inequality has *no* slack to spare — Phase 2
  is not a soft consequence of denominator size; the `d_n^5` reserve is exactly
  consumed at those primes.

No clean single mechanism for Phase 2 was isolated. The verified data plus the
tightness say a proof must track the interaction of `ord_p(p_n)` with both
`ord_p binom(2n,n)` and the harmonic denominators simultaneously — consistent
with route (B) of the note (a well-poised multiple-sum representation exposing
`binom(2n,n)` termwise). This is left open.

---

## 4. Obstruction map — what remains and why

| Piece | Status |
|---|---|
| Reduction of `(CB)` on `n<p≤2n` to `(W)` (Theorem A) | **Proved** |
| Reflection `a_{i,n−j}=(−1)^{i+1}a_{i,j}` (P1) | **Proved** + verified |
| Even-layer vanishing `S_1=S_2=S_4=S_6=0` (P2) | **Proved** + verified |
| `ord_p(a_{6,j})=[j≥t]+[j≤n−t]`, window (P3) | **Proved** (Kummer) + verified |
| Moment identities (★), `w_n=2Σj a_{2,j}−Σj²a_{1,j}` (P4) | **Proved** + verified |
| `(W)`: `w_n≡w̃_n≡0 (mod p)`, `n<p≤2n`, `p≥5` | **Open**; verified 855 pairs, `n≤90` |
| Phase 2 (`p≤n`) inequality | **Open**; verified `n≤60`, 206 tight |

**The single remaining kernel is `(W)`** (equivalently `(W′)`). What blocks a
proof: `w_n = S_3` is an even-index (weight-3) coefficient whose mod-`p`
cancellation is *global* — its summands `a_{3,j}` have full support mod `p`
(P3), and the exact reflection (P1) is symmetric, not antisymmetric, on the
`i=3` layer, so it gives no sign cancellation. The genuine content is a harmonic
identity: the mod-`p` value is
`Σ_j a_{3,j} = −Σ_i Σ_{j≠j'} a_{i,j}(j−j')^{−i}`-type (from summing the reduced
`R̄ = N/D` over a complete residue system, `Σ_{k∈F_p} N·D^{p−2}`), which couples
to the `v_n`-harmonic data rather than isolating `w_n`. Routes not yet closing
it: (i) reflection symmetry (no antisymmetry on odd layers); (ii) moment
identities (★) (constrain, don't isolate `w_n`); (iii) Faà-di-Bruno / log-
derivative expansion of `a_{3,j}` (produces `1/p` corrections that must be
re-summed over `j`). A proof most likely comes from a Krattenthaler–Rivoal
well-poised multiple-sum representation of `w_n` (route B), making the truncation
mod `p` visible.

**Not a supercongruence.** The McCarthy–Osburn–Straub / Osburn–Sahu–Straub
"cellular integrals / sporadic sequences" results concern `A(mp^r) ≡ A(mp^{r-1})
(mod p^k)`. `(W)` is a different object — divisibility of a *numerator* by primes
`p ∈ (n,2n]` that are absent from `d_n` — closer to Rivoal–Zudilin well-poised
denominator theory than to sporadic supercongruences. Not a corollary of the
literature we checked.

---

## 5. Scripts (all exact `Fraction` / integer arithmetic)

- `lemma_cb_explore.py` — builds `a_{i,j}, ã_{i,j}, w_n, w̃_n, u_n, ũ_n, v_n,
  ṽ_n, p_n, q_n` exactly; mod-`p^m` reduction and `ord_p`. Run:
  `python3 lemma_cb_explore.py 1 30`.
- `lemma_cb_wcong.py` — Phase-1 driver: verifies `(W)` and `ord_p(p_n)≥1` with
  exact valuations; valuation histograms. Run: `python3 lemma_cb_wcong.py 1 90`
  (855 pairs, 0 failures).
- `lemma_cb_window.py` — prints `a_{i,j} mod p` tables with the window / Kummer
  markers (P3 evidence).
- `lemma_cb_verify.py` — battery V1 (pole order), V2 (reflection), V3 (even
  vanishing), V4 (mod `p^2` refinement), V5 (Phase-2 ledger + tight cases). Run:
  `python3 lemma_cb_verify.py 1 40`.
- `lemma_cb_wframe.py` — integer reframing F1 (`2 d_n^2 w_n, 2 d_n^2 w̃_n ∈ ℤ`),
  F2 (`B_n^{high} | W_n, W̃_n`), F3 (normal form `a_{3,j}=a_{6,j}(b_3+b_1b_2+
  b_1^3/6)`). Run: `python3 lemma_cb_wframe.py 1 30` (all OK).

(Existing `symmetric_zeta5_divisibility.py` unchanged; it verifies the target
integrality itself for `n ≤ 12`.)

---

## 6. Bottom line

Phase 1 of the Central-Binomial Cancellation Lemma is reduced, by a complete
proof (Theorem A) plus proved structural results (P1–P5), to the **single clean
congruence `(W)`: `w_n ≡ w̃_n ≡ 0 (mod p)` for `n < p ≤ 2n`, `p ≥ 5`** — the
vanishing of the two well-poised ζ(3) coefficients mod the large primes.
`(W)` is verified without exception over 855 `(n,p)` pairs (`n ≤ 90`) but is not
yet proved; it is the last arithmetic gap in the flagship case. Phase 2 holds on
all tested `n ≤ 60` (206 tight cases) and remains open. Per the repo standard,
none of the finite verification is presented as a theorem.
