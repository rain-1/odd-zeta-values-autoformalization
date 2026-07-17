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

## 2.6 Assembly attempt via reflection/pole-sign structure (verified; does not yet close)

Three hand-derived ingredients were tested exactly (`lemma_cb_wproof.py`,
`lemma_cb_signtab`), `n ≤ 20`–`40`:

**Verified.**
- **b-parity** `b_r(n−j) = (−1)^r b_r(j)` (`b_1` odd, `b_2` even, `b_3` odd),
  consistent with `a_{6,j}` odd ⟹ `a_{3,j}` even (0 failures).
- **Pole-sign structure of the `b_r`** (0 failures), with `p = n+t`,
  `ε_j := −[j ≥ t] + [j ≤ n−t]`:
  - `b_1`: `ord = −1` with `1/p`-coefficient `ε_j` (the two boundaries enter
    with **opposite** signs), so `b_1` is `p`-integral (`ord 0`) on the middle
    range `t ≤ j ≤ n−t` where `ε_j = 0`.
  - `b_2`: `ord = −2` **everywhere including the middle** (the two boundaries
    add with the **same** sign; no cancellation).
  - `b_3`: `1/p^3`-coefficient `∝ ε_j` (opposite signs) and in fact `b_3` is
    fully `p`-integral (`ord 0`) on the middle range.

**Two corrections to the proposed assembly.**

1. **Wraparound (R1) is vacuous.** `R_n(k) = 0` for *every* integer
   `k ∈ {1,…,n}` (the factor `∏_{m=1}^n (k−m)` vanishes). The proposed sum
   `Σ_{k=1}^{p−1−n} R_n(k)` has upper limit `p−1−n ≤ n−1`, so **all its terms are
   identically zero** — the congruence holds trivially and carries no `p`-adic
   information. The nonzero, `p`-adically large evaluations are `R_n(k)` for
   `k ∈ {n+1,…,p}` (equivalently `R_n(p−j)`, `j < t`, `ord_p = −6 + [j≤n−t]`;
   `R_n(p−j) = 0` for `j ≥ t`). A Beukers-type extraction of `w_n mod p` from
   these tail terms remains possible in principle but is not delivered by R1.

2. **The middle range does NOT vanish** — so `(W)` does **not** reduce to the
   edges. On `t ≤ j ≤ n−t`: `ord(a_{6,j}) = 2`, `ord(b_1)=ord(b_3)=0`,
   `ord(b_2)=−2`, hence in `a_{3,j} = a_{6,j}(b_3 + b_1 b_2 + b_1^3/6)` the terms
   `a_{6,j}b_3` and `a_{6,j}b_1^3/6` have `ord ≥ 2` but `a_{6,j}b_1 b_2` has
   `ord = 2 + 0 + (−2) = 0` — a **unit**. So (a clean by-product, verified
   mod `p^2`)

       a_{3,j} ≡ a_{6,j} · b_1(j) · b_2(j)   (mod p^2)   for t ≤ j ≤ n−t,

   and the middle partial sum `S_mid = Σ_{mid} a_{3,j}` is a **nonzero unit**
   mod `p` in 92 of 94 sampled `(n,p)` with nonempty middle (only sporadic
   `S_mid ≡ 0` at `n=18,p=23` and `n=38,p=43`). Empirically `S_mid` and the edge
   sum `S_edge` satisfy `S_mid%p + S_edge%p = p` (they cancel *each other*), never
   `S_mid ≡ 0` alone. So the required cancellation genuinely couples middle and
   edge; it cannot be localized to the edges.

**Net.** The reflection/pole-sign machinery is correct and gives an explicit
mod-`p^2` form for the middle summands, but the cancellation in `(W)` remains
global (middle ↔ edge), reinforcing that a harmonic-denominator-free binomial
multiple-sum (route B) is the operative next step.

---

## 2.7 PROOF of (W) by an F_p-linear certificate — Phase 1 essentially closed

This supersedes the "open" status of `(W)`: it is now **proved for each `n` by a
finite exact certificate** (verified `n ≤ 32`, 130 pairs), and the general-`n`
statement is reduced to a single clean uniform-existence lemma.

**The exact relations `E_M` (provable, over ℚ).** Since
`R_n(k) = (n!)^4 k^{−4n−5}(1+O(1/k))`, the coefficient of `k^{−M}` in the Laurent
expansion at `∞` vanishes for `1 ≤ M ≤ 4n+4`. Using
`(k+j)^{−i} = Σ_r C(−i,r) j^r k^{−i−r}`,

    E_M := Σ_{i=1}^{min(6,M)} C(−i, M−i) · Σ_{j=0}^n j^{M−i} a_{i,j} = 0.   (R2)

Verified to hold **exactly over ℚ** for all `n ≤ 32` (`lemma_cb_certificate.py`).
(For `M=1,2,3` these are `Σa_{1,j}=0`, `Σa_{2,j}=Σj a_{1,j}`,
`w_n = 2Σj a_{2,j} − Σj² a_{1,j}` — the ★ family of §2, now taken to full order.)

**The certificate.** For each prime `n < p ≤ 2n` (`p ≥ 5`), the `F_p`-functional
`w = Σ_j a_{3,j}` lies in the `F_p`-linear span of `{E_M mod p : 1 ≤ M ≤ 4n+4}`:
there exist `c_M ∈ F_p` with `Σ_M c_M E_M ≡ w` as functionals mod `p`. Since every
`a_{i,j}` is `p`-integral (`p > n`) and every `E_M(a) = 0` exactly, evaluating on
the true coefficient vector gives

    w_n = w(a) = Σ_M c_M E_M(a) ≡ 0   (mod p).

The same certificate exists for `w̃ = Σ_j ã_{3,j}` (functional
`j(n−j)a_{3,j}+(2j−n)a_{4,j}−a_{5,j}`). Both verified with **zero failures** over
all `n ≤ 32`, `n < p ≤ 2n`, `p ≥ 5` (130 pairs). For each such `n` this is a
finite exact `F_p` linear-algebra identity — a **genuine proof**, not sampling.

**Why exactly `n < p ≤ 2n` (threshold law, verified).** The minimal truncation
that forces `w` is `M = 2p+1`. Available relations reach `M = 4n+4`. Hence the
certificate exists **iff `2p+1 ≤ 4n+4`, i.e. `p ≤ 2n+1`** — matching the
central-binomial window exactly (and the harmless extra prime `p = 2n+1`, where
indeed `ord_p(w_n) ≥ 3` though `p ∤ binom(2n,n)`).

**Soundness controls (verified).** The method does **not** force what is false:
the `ζ(5)` coefficient `u = Σ_j a_{5,j}` (a unit mod `p`) is **never** in the span;
and for primes `p > 2n+1`, `w` is **not** forced (consistent with `w_n` being a
unit there). So the certificate fires exactly on the true congruences.

**Consequence.** Combined with Theorem A (§1), **`(CB)` on the clean interval
`n < p ≤ 2n` is proved for every `n ≤ 32`**, with an explicit finite certificate,
and the mechanism (`ord_∞ R_n = 4n+5` vs the threshold `2p+1`) is understood.

**The single remaining Phase-1 gap** is now purely uniform-in-`n`:

> **Lemma (uniform certificate) — remaining.** For all `n` and all primes
> `n < p ≤ 2n`, the functional `Σ_j a_{3,j}` (and its `w̃` analogue) lies in the
> `F_p`-span of `{E_M : 1 ≤ M ≤ 4n+4}`.

This is a self-contained statement about the mod-`p` rank of the explicit
`∞`-expansion matrix `[C(−i,M−i) j^{M−i}]`; the verified minimal-`M = 2p+1` law
and Fermat wraparound (`j^{M} ≡ j^{M−(p−1)}`, active once `M > p−1`, i.e. exactly
when `p ≤ 2n`) are the structural handles for proving it in general.

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

### 3.1 Phase-2 structure discovered (reconnaissance, 2026-07-17 late)

Scripts: `lemma_cb_phase2_recon.py`, `lemma_cb_phase2_univ.py`. Three verified
facts reorganize Phase 2 (all exact arithmetic; DATA, not yet theorems, except
(a) which is trivial and (b) which is free):

**(a) Kummer band law (proved, trivial).** For `n/2 < p ≤ n`: `κ :=
ord_p binom(2n,n) = [p ≤ 2n/3]` (write `n = p+r`; the single possible carry is
`2r ≥ p`). So Phase 2 is VACUOUS on `(2n/3, n]`; the first open band is
`(n/2, 2n/3]`, where exactly `+1` p-adic order beyond Zudilin's bound is needed.
Verified n < 200.

**(b) `binom(2n,n) | q_n` is FREE (all p ≥ 5).** `Q_n = ±q_n/binom(2n,n)` is
BZ's cellular coefficient with the manifestly-integer double binomial sum
(sumQ), so `ord_p q_n ≥ κ` costs nothing. Verified 80 cases `n ≤ 24`.

**(c) p-adic proximity (the discovery — DATA).** In the band, naive products
give `ord_p ≈ −7` but `ord_p(p_n) = −4` with slack 0 everywhere: the vectors
`(w,w̃)` and `(v,ṽ)` are p-adically near-proportional (route (A) confirmed).
Stronger: `ρ_n := p_n/q_n` (ord `−5`) is a UNIVERSAL p-adic constant across `n`
sharing a band prime — pairwise differences `ρ_n − ρ_m` gain 1–4 digits over
the size of the terms (p=5: −3 vs −5; p=7: −5 vs −6; p=11: −2 vs −5; p=13
similar). So `p_n ≈ ρ_p·q_n` p-adically with `ρ_p` an n-independent constant —
a p-adic ζ(5) avatar (Calegari-type: rational approximations converging
p-adically to p-adic L-values).

**Consequent reframing of Phase 2.** Given (b), the target
`ord_p(p_n) ≥ κ − 5` follows from ONE statement:

>  (PROX)  `ord_p(p_n − ρ_p q_n) ≥ κ(n,p) − 5`  for some n-independent
>  `ρ_p ∈ ℚ_p` with `ord_p ρ_p ≥ −5`,

since then `ord_p p_n ≥ min(ord ρ_p + κ, κ−5) = κ−5`. I.e. **the p-adic error
of the approximation p_n/q_n → ρ_p must be at least as central-binomially
divisible as q_n itself** — the exact p-adic mirror of the archimedean
smallness of `r_n = q_nζ(5) − p_n`. Two-species theme, now on the p-adic side.
Band case needs just ONE digit of proximity (κ=1); data shows 1–4 digits.

**Attack tools for the band:** the exact ℤ-lift of the Frobenius certificate
`k^p − k = (k+j)^p − (k+j) + p·G_j(k+j)`, `G_j ∈ ℤ[u]` (verified) — jets
correct mod p ⟹ main-term-plus-p×(crude-bound) structure, the right shape for
a +1 gain; plus Wolstenholme-type block congruences for the harmonic layer
(`H^{(i)}` over full residue blocks). Status: reconnaissance only; (PROX) is
the open statement.

---

## 4. Obstruction map — what remains and why

| Piece | Status |
|---|---|
| Reduction of `(CB)` on `n<p≤2n` to `(W)` (Theorem A) | **Proved** |
| Reflection `a_{i,n−j}=(−1)^{i+1}a_{i,j}` (P1) | **Proved** + verified |
| Even-layer vanishing `S_1=S_2=S_4=S_6=0` (P2) | **Proved** + verified |
| `ord_p(a_{6,j})=[j≥t]+[j≤n−t]`, window (P3) | **Proved** (Kummer) + verified |
| Moment identities (★)/`E_M` relations, exact over ℚ (P4, §2.7) | **Proved** + verified |
| `(W)`: `w_n≡w̃_n≡0 (mod p)`, `n<p≤2n` — **F_p certificate** (§2.7) | **Proved for each `n≤32`** (finite exact certificates); general `n` = uniform-certificate lemma |
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
- `lemma_cb_wproof.py` — assembly-attempt battery (§2.6): R1 wraparound (verified
  vacuous), R2 b-parity, R3 pole-sign structure + tail ords, and the middle/edge
  decomposition showing `S_mid` is a nonzero unit. Run:
  `python3 lemma_cb_wproof.py 1 20`. Middle mod-`p^2` reduction
  `a_{3,j} ≡ a_{6,j} b_1 b_2` verified separately (290 checks, 0 mismatches).
- `lemma_cb_moment.py` — F_p-moment reduction (§2.7 precursor): verifies
  `w_n ≡ 3 Σ_j j² a_{1,j}` and `w̃_n ≡ 3 Σ_j j² ã_{1,j}` mod `p` (residue-layer
  form), genuineness (`ord_p(w−3X)≥1`), and the moment-parity table. Run:
  `python3 lemma_cb_moment.py 2 40`.
- `lemma_cb_certificate.py` — **the proof of (W)** (§2.7): checks `E_M = 0` exactly
  over ℚ, then that `w` and `w̃` lie in the `F_p`-span of `{E_M}` for `n<p≤2n`
  (proving `w_n≡w̃_n≡0`), with the `u`-not-forced soundness control. Run:
  `python3 lemma_cb_certificate.py 2 32` (130 pairs, all OK).

(Existing `symmetric_zeta5_divisibility.py` unchanged; it verifies the target
integrality itself for `n ≤ 12`.)

---

## 6. Bottom line

Phase 1 of the Central-Binomial Cancellation Lemma reduces, by a complete proof
(Theorem A), to the congruence `(W)`: `w_n ≡ w̃_n ≡ 0 (mod p)` for `n < p ≤ 2n`.
`(W)` is now **proved for every `n ≤ 32` by an explicit finite `F_p`-linear
certificate** (§2.7): the well-poised ζ(3) functionals lie in the mod-`p` span of
the exact `∞`-expansion relations `E_M = 0` (`M ≤ 4n+4`), which forces the
congruence precisely because `4n+4 ≥ 2p+1 ⇔ p ≤ 2n+1`. The certificate is a
genuine per-`n` proof (not sampling), with soundness controls passing (`u = Σa_{5,j}`
never forced; nothing forced for `p > 2n+1`). Hence **`(CB)` on the clean interval
is a theorem for all `n ≤ 32`**, and the general-`n` case is reduced to one
self-contained uniform-existence lemma about the mod-`p` rank of the explicit
`∞`-expansion matrix. Phase 2 (`p ≤ n`) holds on all tested `n ≤ 60` (206 tight
cases) and remains open. Finite certificate checks for a given `n` are exact
proofs for that `n`; the uniform-in-`n` statement is not yet a theorem.
