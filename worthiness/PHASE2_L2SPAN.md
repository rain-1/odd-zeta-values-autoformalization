# PHASE2_L2SPAN — the depth-2 iterated-certificate experiment

2026-07-19. Executes `PHASE2_CERT_FROM_FABLE.md` §3. Tests whether the level-1
Frobenius-certificate mechanism (`cb_certificate.tex`), which proved
`w_n ≡ 0 (mod p)` for `n < p ≤ 2n`, iterates to depth 2 to buy the extra Kummer
digit(s) at the colliding primes `p ≤ n`.

Code: `l2span.py` (pipeline), `l2span_linalg.py` (validated local-ring linear
algebra). Reproduce: `python3 l2span.py` (grid + gates), `python3 l2span.py 8 5`
(per-pair landscape).

**Verdict: NOT FORCED.** The depth-2 `ℤ/p²`-span of the exact decay relations
`{E_M}` forces **no digit at any depth** for the target functionals `w, w̃` once
`p ≤ n`. The level-1 certificate survives *as an algebraic identity* but loses all
arithmetic force, because the coefficients `a_{i,j}` are no longer `p`-integral.
The iterated-certificate route (Idea 1 of the memo) does not survive.

---

## 0. The mechanism being tested, and the honest depth-2 forcing lemma

Level 1 has two ingredients: (i) the target covector `w = Σ_j a_{3,j}` lies in the
`𝔽_p`-span of the exact relations `E_M(a) = 0` (`M = 1..4n+4`), and (ii) every
`a_{i,j}` is **`p`-integral** (`p > n`). Then `w = Σ c_M E_M + p·U` for an integer
covector `U`, and `w(a) = p·U(a)` with `U(a) ∈ ℤ_p`, giving `ord_p(w_n) ≥ 1`.

**Forcing lemma (sound, general depth `s`).** Let `m_a := min_{i,j} ord_p(a_{i,j})`.
If `T` lies in the `ℤ/p^s` row-span of `{E_M}`, then `T = Σ c_M E_M + p^s U` (`U`
integer), so `T(a) = p^s U(a)` and

>   `ord_p(T(a)) ≥ s + m_a`.

At level 1, `m_a = 0`, so span-mod-`p` ⟹ `ord ≥ 1`. **At `p ≤ n` the poles
`j = 0..n` collide and the `a_{i,j}` acquire `p` in the denominator, so `m_a < 0`.**
The entire question is whether the span depth `s` can outrun the denominator loss
`m_a`. It cannot.

---

## 1. Soundness gates and the regression anchor (all PASS)

- **Gate 0 — linear algebra.** `l2span_linalg.py` implements a modular Hermite
  normal form over the local ring `ℤ/p²` (init `H = N·I`, all arithmetic mod `N`,
  non-unit diagonal pivots carry the `p`-torsion: a pivot `= p` forces only a
  depth-1 congruence, a pivot `= 1` a depth-2 one) plus an independent coefficient-
  tracking reduction that extracts explicit certificates. Both are validated
  against **literal brute-force span enumeration** for `N = 25, 49` and against each
  other for `N = 25, 49, 121, 169` (`_selftest()` → `ALL PASS`).
- **Gate 1 — regression anchor `(n,p) = (8,11)` (level 1).** `w` forced mod `p`;
  the unit `u = Σ_j a_{5,j}` **not** forced; the classical three-term certificate
  `(c_3, c_{p+2}, c_{2p+1}) = (1,−2,1)` at `M = (3,13,23)` reproduces `w` mod `p`.
  Additional band anchors `(3,5),(4,7),(5,7),(6,11),(8,13),(10,19),(12,23)` all
  PASS.
- **Gate 2 — no unsound forcing.** Across the whole `p ≤ n` grid, the guaranteed
  bound `s + m_a` **never exceeds** the measured `ord_p(T(a))` for any of the ~40
  functionals per pair (`w, w̃, u`, all class sums `S_{i,c}`, all digit refinements
  `T_{i,c}`). Reported as `Gate (b): NONE`. The linear-algebra facts and the exact
  valuations are mutually consistent everywhere — the pipeline is sound.

---

## 2. MAP phase — the `p ≤ n` congruence landscape (recorded agnostically)

New territory (the campaign had only mapped `n < p ≤ 2n`). Exact-`ℚ` facts:

**(M1) The `a_{i,j}` are not `p`-integral.** Per-layer minima `min_j ord_p(a_{i,j})`
are stable across the grid: `i=1: −3` (`−4` once `L=ord_p(d_n)=2`), `i=2: −3`,
`i=3: −2`, `i=4: −1`, `i=5: 0`, `i=6: ≥ 1`. So `m_a = −3` for `n < p²`, degrading
to `−4` (e.g. `(23,5),(24,5),(38,7)`) and `−9` at `(28,5)` (`L=2`). This negative
`m_a` is the whole story — it is exactly the feature absent at level 1.

**(M2) Residue-class layer sums `S_{i,c} = Σ_{j≡c(p)} a_{i,j}`.** For the `w`-layer
`i=3`, every non-central class has the *same* valuation as `w` itself
(`(8,5)`: `ord = −2` for `c=0..3`; `(18,5)`: `ord = −1` for `c=0..4`). Regrouping by
residue class buys nothing: the collision does not concentrate valuation into a
cleaner class functional. The reflection centre `j = n/2` sits in one class and is
individually highly divisible (`(8,5)`: `ord(a_{3,4}) = 7`), a symmetry artifact.

**(M3) Empirical span membership (mod `p`, mod `p²`).**
- `w, w̃ ∈` span mod `p` for **every** grid pair — membership *persists* from level
  1, and at `(8,5)` the classical `(1,−2,1)` three-term certificate still reproduces
  `w` mod `p` exactly. But this is now valuation-empty (see §3).
- `w, w̃ ∉` span mod `p²` for **every** grid pair — a hard non-membership fact,
  independent of the `m_a` argument. **The second digit is simply not available.**
- The digit-1 refinement functionals `T_{i,c} = Σ_{j≡c} ((j−c)/p) a_{i,j}` are
  **not in the span even mod `p`** (span depth 0) anywhere. The "next base-p digit"
  structure the memo flagged for exploration lies entirely outside the `E_M` span.

---

## 3. Verdict table (`l2span.py`) — required digits vs forced digits

`w:s/meas/gtd` = (max span depth `s`) / (measured `ord_p`) / (guaranteed `s+m_a`).
`req = κ − 5L` is the Phase-2 target `ord_p(p_n) ≥ κ − 5L`, `L = ord_p(d_n)`,
`κ = ord_p\binom{2n}{n}` (# base-`p` carries).

| (n,p) | κ | L | m_a | ord(p_n) | req=κ−5L | w: s/meas/gtd | w̃: s/meas/gtd | 2nd digit on w,w̃? |
|------:|--:|--:|----:|---------:|---------:|:-------------:|:--------------:|:-----------------:|
| (8,5)  | 1 | 1 | −3 | −4 | −4 | 1/−2/−2 | 1/−2/−2 | **no** |
| (9,5)  | 1 | 1 | −3 | −4 | −4 | 1/−2/−2 | 1/−1/−2 | **no** |
| (13,7) | 1 | 1 | −3 | −4 | −4 | 1/−2/−2 | 1/−1/−2 | **no** |
| (14,7) | 0 | 1 | −3 | −3 | −5 | 1/ 0/−2 | 1/ 2/−2 | **no** |
| (18,5) | 2 | 1 | −3 | −3 | −3 | 1/−1/−2 | 1/−1/−2 | **no** |
| (19,5) | 2 | 1 | −3 | −3 | −3 | 1/−1/−2 | 1/ 0/−2 | **no** |
| (23,5) | 2 | 1 | −4 | −2 | −3 | 1/−1/−3 | 1/−1/−3 | **no** |
| (24,5) | 2 | 1 | −4 | −2 | −3 | 1/−1/−3 | 1/ 1/−3 | **no** |
| (38,7) | 1 | 1 | −4 | −4 | −4 | 1/−1/−3 | 1/−1/−3 | **no** |
| (28,5) | 1 | 2 | −9 | −9 | −9 | 1/−4/−8 | 1/−4/−8 | **no** |

(The `(8,5)` run flags "4 fns" at depth ≥ 2: these are the singleton centre class
`j = 4 = n/2 < p`, benign symmetry artifacts, never `w`/`w̃`. For `n = 18` the
centre class `{4,9,14}` is not a singleton and nothing reaches depth 2.)

**Reading the table.** For every pair, `w` and `w̃` have span depth exactly `s = 1`,
and the guaranteed bound `s + m_a` sits at the **crude denominator floor**
`1 + m_a`, always `≤` measured (frequently strictly below it — e.g. `(18,5)`
measured `−1` vs guaranteed `−2`). So:

1. **No second digit is ever forced** (`s = 1` throughout, and `w,w̃ ∉` span mod `p²`).
2. **No first digit is forced either**, in the arithmetic sense: at `p ≤ n` the
   span-mod-`p` membership only yields `ord_p(w) ≥ 1 + m_a = m_a + 1 ≤ −1`, never the
   level-1 conclusion `≥ 1`. The certificate persists as an identity but the
   `p`-integrality factor that gave it force is gone.
3. **The real Phase-2 gain is bilinear, not linear.** The target divisibility
   `ord_p(p_n) = κ − 5L` (tight) comes from a cancellation in
   `p_n = w̃·v − w·v_tilde`: measured `ord(w̃)+ord(v)` and `ord(w)+ord(v_tilde)` are
   each around `−7`, but `p_n` is `−4` — a 3-digit cancellation (the near-
   proportionality `(w,w̃) ∥ (v,ṽ)` recorded as (PROX) in `LEMMA_CB.md` §3.1). This
   cancellation is **invisible to the `ℤ/p²`-span of the linear functionals `E_M`.**

---

## 4. Budget arithmetic (level-2 degree count) — the headline

Level 1: `deg φ = 2p`, top functional index `M = 2p+1 ≤ 4n+4 ⇔ p ≤ 2n+1`. The
depth-2 Frobenius candidates `(k^{p²}−k^p)²` and `(k^p−k)^{2p}` both have degree
`2p²`, so their top index is `M = 2p²+1`, which must satisfy `2p²+1 ≤ 4n+4`, i.e.
`n ≥ (2p²−3)/4`.

| (n,p) | lvl2 top M = 2p²+1 | avail M = 4n+4 | budget fits? |
|------:|-------------------:|---------------:|:------------:|
| (8,5)  | 51 | 36  | **no** |
| (9,5)  | 51 | 40  | **no** |
| (13,7) | 99 | 56  | **no** |
| (14,7) | 99 | 60  | **no** |
| (18,5) | 51 | 76  | yes |
| (19,5) | 51 | 80  | yes |
| (23,5) | 51 | 96  | yes |
| (24,5) | 51 | 100 | yes |
| (28,5) | 51 | 116 | yes |
| (38,7) | 99 | 156 | yes |

**Budget-prediction vs span-fact = the headline (they DISAGREE).**

- For the first-collision small cases `(8,5),(9,5),(13,7),(14,7)` the budget
  **fails** (`2p²+1 > 4n+4`): the depth-2 certificate polynomial cannot fit under
  the `O(k^{−4n−5})` decay ceiling. The span forces nothing extra — **agreement**.
- For `(18,5),(19,5),(23,5),(24,5),(28,5),(38,7)` the budget **is satisfiable**
  (`2p²+1 ≤ 4n+4`): a degree-`2p²` certificate *would* fit. Yet the span **still
  forces no second digit** on `w,w̃` — **disagreement**.

So degree-budget satisfiability is **necessary but not sufficient**. The obstruction
is not the degree ceiling; it is the **denominators** (`m_a < 0`), which the degree
count cannot see. The memo's conjecture "satisfiable-iff-second-carry, short-by-a-
constant is the likely failure mode" is **refuted in its optimistic direction**: the
failure is not a near-miss in degree but a structural collapse of the forcing lemma
once the coefficients stop being `p`-integral.

---

## 5. Explicit certificates extracted

- **Level-1 anchor `(8,11)`:** `w ≡ E_3 − 2E_{13} + E_{23} (mod 11)`, i.e.
  `φ = (k^{11}−k)²`, `(c_3,c_{13},c_{23}) = (1,−2,1)`. Verified.
- **`(8,5)`, depth 1:** `w ∈` span mod `5`; the classical `(1,−2,1)` at
  `M = (3,7,11)` still reproduces `w` mod `5` (the identity persists into Phase 2).
  Arithmetically empty: guarantees only `ord_5(w) ≥ 1 + m_a = −2`.
- **`(8,5)`, depth 2:** `w ∉` span mod `25` — **no depth-2 certificate exists.**
  (Same for every grid pair, and for `w̃`.)

---

## 6. Honest read — does the iterated-certificate route survive?

**No.** The level-1 proof factored as *(span membership) × (`p`-integrality) ⟹
(one forced digit)*. At `p ≤ n` the first factor survives (membership even at
depth 1, and the classical three-term certificate is still an algebraic identity),
but the second factor is destroyed: `m_a ≤ −3` kills the valuation gain at every
depth, and independently `w, w̃ ∉` span mod `p²`, so there is no depth-2 certificate
to find. The digit-refinement functionals `T_{i,c}` are not even in the span mod
`p`. The one-digit-per-carry picture is correct as a *statement about `ord_p(p_n)`*,
but that gain is a **bilinear cancellation** `(w,w̃) ∥ (v,ṽ)` — precisely the (PROX)
proximity of `LEMMA_CB.md` §3.1 — and is invisible to any `ℤ/p^s`-span of the linear
`E_M`. Phase 2 will not fall to an iterated *linear* certificate; the live object
remains (PROX)/the projective Dwork twist (`dwork_vecform.py`, Sol's top-down route),
which is bilinear by construction.

The experiment did its job: it localizes the missing mathematics precisely — not in
the degree budget, but in the non-`p`-integrality of the partial-fraction data and
the bilinearity of the true cancellation.
