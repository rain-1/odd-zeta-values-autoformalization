# Phase-2 band verification V1-V5 -- findings (Fable, 2026-07-18)

> **V5 (2026-07-18, coordinator upgrade) is below §V4** and SUPERSEDES the primary
> line of attack: the V3 "global rationals" are the **n=1 ladder ratios**, and the
> whole band phenomenon is a **Dwork descent** that generalises to ALL `p <= n`,
> reducing Phase 2 entirely to `(FREE) + (DWORK)`. Read §V5 first for the current
> state; §§V1-V4 remain valid as the band-only (`a=1`) verification.

---

# Phase-2 band verification V1-V4 -- findings (Fable, 2026-07-18)

Execution of `PHASE2_BAND_BLUEPRINT.md` stages V1-V4. Exact `Fraction` arithmetic
throughout. Band = `n/2 < p <= 2n/3`, `p >= 5` (`kappa = ord_p C(2n,n) = 1`);
target `ord_p(p_n) >= kappa - 5 = -4`. Coverage: **46 band pairs**, `n = 8..45`,
primes `p = 5,7,11,13,17,19,23,29` (full bands for `p <= 23`, partial `p=29`).
Scripts: `lemma_cb_band_v1.py .. _v4.py`. **HONESTY: everything below is verified
congruence / measured data, NOT proved, except where a prior theorem is cited.**

Write `n = p + r`; in-band `r in [ceil(p/2), p-1]`; the only multiple of `p` in
`[1,n]` is `p` itself. "Clean primes" = `p >= 11` (behaviour uniform); `p = 5,7`
are Wolstenholme-edge (deeper ords, still band-closing); `p=29` partial band.

## Bottom line

**The band closes, conditionally on an explicit finite congruence list.** All four
stages ran to completion. The universal constants exist AND are identified as two
**global rationals** (V3, the headline finding). The reduction of the band target
to a finite head-window congruence list succeeds (V4 A/B). The Phase-1 `E_M`
certificate does **not** force the deep congruence (V4 C, honest negative) --
that is the precise remaining gap.

| Stage | Verdict |
|---|---|
| V1 decomposition | **PASS** -- H-tail removal exact; `ord(S_i^head)=i-5` ladder; residual `ord -2` |
| V2 universal constants | **PASS** -- `rho_p` (ord -5), `sig_p` (ord -3) universal to `>=2` digits (clean primes), `>=1` (edge); band needs `>=1` |
| V3 identification | **FINDING** -- `rho_p = (29/28) p^{-5}`, `sig_p = (101/84) p^{-3}`, global rationals, full universal precision, all 5 clean primes |
| V4 reduction | **PASS** -- band target `ord(p_n) >= -4` closes from explicit list (margin `>=1`) |
| V4 certificate | **NEGATIVE** -- `E_M` forces `HW` only mod `p^0` (full) / `p^1` (window); needs `>= p^3`. Wolstenholme machinery required |

---

## V1 -- exact decomposition (`lemma_cb_band_v1.py`)

`H_j^{(i)} = Hhat_j^{(i)} + [j>=p] p^{-i}` (`Hhat` p-integral: only multiple of
`p` in `[1,j<=n<2p]` is `p`). Hence `v = sum_{i,j} a_{i,j} Hhat_j^{(i)} + sum_i
p^{-i} S_i^tail` with `S_i^tail = sum_{j>=p} a_{i,j} = (-1)^{i+1} S_i^head`
(reflection P1), `S_i^head := sum_{j=0}^r a_{i,j}`. So

    RESIDUAL(v) := v - sum_i p^{-i}(-1)^{i+1} S_i^head  =  sum_{i,j} a_{i,j} Hhat_j^{(i)}.

Computed two independent ways per pair; **`A == B` asserted for all 46 pairs** (the
H-tail removal is exact). Findings (clean primes `p>=11`, uniform):

- `ord_p(v) = -5`; after removing the H-tail singular part, `ord_p(RESIDUAL) = -2`
  (the a-singularity residue, blueprint 2b). Gains 3 orders.
- **`ord_p(S_i^head) = i - 5` for `i = 2..6`** (i.e. `-3,-2,-1,0,+1`); `S_1^head`
  deep-integral (`ord ~ +4`, `= inf` when `r` even). Same ladder for the companion.
- So each layer `i=2..6` contributes `p^{-i} S_i^head` of ord exactly `-5`: the whole
  depth-5 singularity of `v` lives in the head window `[0,r]`.

## V2 -- the universal constants (`lemma_cb_band_v2.py`)

Solve `[[u,w],[ut,wt]] [rho,sig]^T = [v,vt]^T` per `n`, `det = q_n`, `ord_p(q_n) =
kappa = 1` (near-singular). **Exact** Cramer: `rho_n = p_n/q_n`, `sig_n =
ptil_n/q_n` where `ptil_n = u vt - ut v` is the third (`u,v`) minor. *Precision
note:* the near-singular det causes **no numerical loss** -- inversion is over Q,
every p-adic digit of `rho_n,sig_n` is pinned exactly; the blueprint's "precision
loss" is the **universality** question (are they n-independent?), quantified as
cross-`n` agreement. Every disagreement below is genuine n-dependence at that
digit, never "undetermined".

Uniform ords (clean primes): `ord q=1, ord p_n=-4, ord ptil=-2`, `ord rho=-5,
ord sig=-3`. Cross-`n` agreement `#digits = v_p(rho_n - rho_m) - ord(rho)`:

| p | band n | min #agree rho | min #agree sig |
|---|---|---|---|
| 11 | 17-21 | **3** | 2 |
| 13 | 20-25 | 2 | 2 |
| 17 | 26-33 | 2 | 2 |
| 19 | 29-37 | 2 | 2 |
| 23 | 35-45 | 2 | 2 |
| 5 | 8-9 | 2 | 2 |
| 7 (edge) | 11-13 | 1 | 1 |
| 29 (partial) | 44-45 | 1 | 2 |

**Band needs `>= 1` digit; data gives `>= 2` (clean), `>= 1` (edge).** The third
minor `sig_n = ptil_n/q_n` is universal with the same `q_n` family (blueprint V2
last clause) -- PASS.

## V3 -- identification (`lemma_cb_band_v3.py`)

Compared the universal leading digits against the blueprint menu (Fermat quotients
`q_p(2),q_p(3)`; Bernoulli `B_{p-3},B_{p-5} mod p`; Wolstenholme block quotients
`H_{p-1}^{(i)}/p^{e_i}`; small rationals). **No consistent match** -- the leading
digit `d0(rho)` is `3,8,15,18,15` at `p=11,13,17,19,23`; matches to any menu
entry are sporadic (coincidental).

**But CRT + rational reconstruction across the 5 clean primes of `p^{|ord|}*const
mod p^2` gives a clean, unique low-height rational, identical from 1 or 2 digits:**

    rho_p ≡ (29/28) * p^{-5}   (mod p^{-3}),      sig_p ≡ (101/84) * p^{-3}   (mod p^{-1}).

Verified directly (not just via CRT): `p^5 * rho_n ≡ 29/28` and `p^3 * sig_n ≡
101/84` to `>= 2` p-adic digits (often 3-4) at every band `n`, every clean prime.
So **the constants are FIXED GLOBAL RATIONALS times `p`-powers**, not p-adic
L-value avatars in the Bernoulli/Fermat basis. (`28 = 2^2·7`, `84 = 2^2·3·7`;
`29/28 = 87/84`, `sig-rho·p^2`-type relation `101/84 - 87/84 = 1/6`.) A genuine
identification -- the height-`<30` rational satisfying `>= 10` residue constraints
is not coincidence.

## V4 -- reduction to the finite congruence list + certificate (`lemma_cb_band_v4.py`)

### A/B -- the closing chain (verified, 46 pairs)

With the explicit constants `rho_p = 29/28 p^{-5}`, `sig_p = 101/84 p^{-3}`:

    Sing := sum_i p^{-i}(-1)^{i+1} S_i^head          (head-window singular part = v's H-tail)
    v = Sing + resid,   resid = sum a_{i,j} Hhat_j^{(i)}

Measured worst-case ords over the whole table (clean primes uniform; edge `p=7`
one order deeper but still band-closing):

- **(HW)** `Sing ≡ rho_p u_n + sig_p w_n  (mod p^0)`  -- `ord(HW) >= 0` (`p>=11`).
  Leading mod-`p` form, verified exactly at all clean primes:
  `p^5 Sing ≡ (29/28) u + (101/84) p^2 w  (mod p)` (the `p^2 w` term matters: `ord w = -2`).
- **(resid)** `ord(resid) >= -2`  (a-singularity residue).
- Hence **(Z_p)** `v ≡ rho_p u + sig_p w`, `vt ≡ rho_p ut + sig_p wt  (mod p^{-2})`
  i.e. `theta = -2` (the blueprint hoped `-1`; `-2` is enough, see below).
- **(PROX)** `ord(p_n - rho_p q_n) >= -2` (worst `-3` at edge `p=7`), need `>= -4`.

**Why `theta=-2` suffices (the closing estimate):**
`p_n = wt v - w vt = rho_p q_n + (wt E_v - w E_vt)`, `E_v = v - rho_p u - sig_p w`.
With `ord(w),ord(wt) >= -2` (Zudilin) and `ord(E_v),ord(E_vt) >= -2`,
`ord(error) >= -4`; and `ord(rho_p q_n) = -5 + ord(q_n) >= -5 + kappa = -4` using
`ord_p(q_n) >= kappa` (**FREE**, BZ sumQ, blueprint fact b). So
`ord_p(p_n) >= -4 = kappa - 5`. **BAND TARGET CLOSES, margin `>= 1`.**

This is a genuine *reduction*: the band inequality follows, uniformly in `n`, from
the explicit finite list below -- no per-`n` computation of `p_n` needed.

### The precise remaining congruence list (the V4 deliverable)

To make the band a theorem it remains to PROVE (all verified here, `p >= 11`):

1. **(HW)** `Sing ≡ (29/28) p^{-5} u_n + (101/84) p^{-3} w_n  (mod p^{-2})`
   and its companion **(HW~)** with `Sing~, ut, wt`.
   Equivalently the three leading digits (`ord -5,-4,-3`) of the head-window sum
   `Sing` are the stated multiples of `u_n, w_n`. *[The a-singularity residue
   `ord(resid) >= -2` (2) is the shallow companion.]*
2. **(const)** the rationals are exactly `29/28`, `101/84` (i.e. (HW) holds with them).
3. `ord_p(w_n), ord_p(wt_n) >= -2`  -- **already Zudilin** (`2 d_n^2 w_n in Z`).
4. `ord_p(q_n) >= kappa = 1`  -- **already FREE** (BZ integer sumQ, LEMMA_CB 3.1b).

Items 3,4 are theorems; the open content is **1 (+2)**: the deep head-window
congruence with explicit constants.

### C -- window E_M / Frobenius certificate (honest NEGATIVE)

Mimicking `lemma_cb_certificate.py` at module level: is the functional
`2352 * p^6 * HW` in the `Z/p^K`-module span of the exact infinity-vanishing
relations `{E_M : 1 <= M <= 4n+4}` (`= 0` on the true vector)? Valuation-aware
elimination over `Z/p^6`, sanity-checked (an actual `E_M` row reduces to `0`;
target evaluates to `ord = 6` on the true vector).

    FULL E_M   : HW forced only mod p^0  (residual is a unit -- not forced at all)
    WINDOW E_M : HW forced mod p^1        (restricting to [0,r] columns gains 1 order)
    (need mod p^3 to kill ords -5,-4,-3; verified at n,p = 17/11, 20/13, 26/17, 29/19, 35/23)

**Conclusion:** the Phase-1 `E_M` machinery alone does **not** force the deep
head-window congruence -- it is a genuinely p-adic (proximity) statement about the
*leading units* of the window sums `S_i^head`, not an `F_p`-linear functional the
`infinity`-relations can hit. Window restriction helps (0 -> 1 digit) but leaves a
2-digit gap. Closing it needs the **Wolstenholme-block congruences**
(`H_{p-1}^{(i)}` over the tail block) the blueprint flags in 2(c) -- these inject
the missing p-adic content that `E_M` (a char-0 vanishing) cannot. That is the
sharp next step.

---

## Status summary

- V1, V2 **PASS**; V3 delivers a clean **identification** (`29/28`, `101/84`);
  V4 A/B **reduces** the band to an explicit finite list and shows it **closes**
  (margin `>= 1`); V4 C is an honest **negative** locating the exact remaining gap.
- The Phase-2 band is now: **theorem modulo the two explicit head-window
  congruences (HW)/(HW~)** with constants `29/28, 101/84`, whose proof needs
  Wolstenholme-block (not `E_M`) machinery.
- Scripts: `lemma_cb_band_v1.py`, `_v2.py`, `_v3.py`, `_v4.py`
  (run `python3 lemma_cb_band_v4.py 11 45 23`).

---

# V5 -- the Dwork ladder congruence and the general-kappa reduction (`lemma_cb_band_v5.py`)

**Coordinator upgrade (2026-07-18).** The V3 constants are exact **ladder ratios**:

    29/28 = p_1/q_1,   101/84 = ptil_1/q_1,   24289/23424 = p_2/q_2,   ...   (verified)

so the band constant for `n = p+r` (digits `(1,r)` base `p`) is the leading-digit
ratio `p_1/q_1`, and the phenomenon is a **Dwork/Frobenius descent on the ratio**
`rho_n := p_n/q_n`, not a per-band coincidence. This reorganises ALL of Phase 2
(every `p <= n`), superseding the Wolstenholme-block hunt as the primary route.

## V5.1 -- the central congruence (Dwork descent; verified)

For `a = floor(n/p)`, `kappa = ord_p binom(2n,n)`:

    (DWORK)   p^5 * (p_n/q_n)    ≡ p_a/q_a       (mod p^{k}),
              p^3 * (ptil_n/q_n) ≡ ptil_a/q_a    (mod p^{k}),
              guaranteed floor  k >= 2 - kappa;  typical k = 3 - kappa.

Verified over **272 descents** (`p = 11,13,17,19,23`, `n <= 45`, `a = 1,2,3`),
non-exceptional primes: floor `k >= 2-kappa` with **0 failures** (min `k+kappa =
2`); 223 hit the typical `3-kappa`, 46 are **boosted** (`+1/+2`). Boosts sit at
the reflection centre `r=(p-1)/2` and the endpoints `r=1,p-1` -- the first
correction digit is **antisymmetric in `r` about the centre** (`~ (2r+1-p)`), the
signature of a derivative term `p*(d/da)` as in the standard Dwork
`F(x)/F(x^p)` congruences. The closure needs only `k >= 1`, so `2-kappa` (for
`kappa <= 1`, the reachable range) is comfortable.

## V5.2 -- iterated descent => the general-kappa target (0 failures)

Iterating `(DWORK)` `L = ord_p(d_n) = floor(log_p n)` times down to the base
digit `n0 = floor(n/p^L) < p` gives, for non-exceptional `p`,

    ord_p(p_n/q_n) = -5L + ord_p(p_{n0}/q_{n0}) = -5L      (base ratio a p-unit).

Combined with **(FREE)** `ord_p(q_n) >= kappa` (BZ integer sumQ):

    ord_p(p_n) = ord_p(rho_n) + ord_p(q_n)  >=  -5L + kappa  =  kappa - 5L,

which is **exactly the (CB) target** for `p >= 5`: `ord_p(A_n) = 5L + ord_p(p_n)
>= kappa` with `A_n = 2 d_n^5 p_n`, `ord_p(6) = 0`. The `d_n^5` reserve supplies
exactly `5` per digit-level, matching the `-5` the Dwork descent costs per level
(the zeta(5) weight). **`ord_p(p_n) >= kappa - 5L` verified with 0 failures**,
all `p >= 5`, `n <= 45` (`lemma_cb_band_v5.py` V5.2). *This is the (CB) inequality
itself -- the earlier band `-4` was the `L=1,kappa=1` special case.*

## V5.3 -- exceptional primes (`p | den` of a ladder ratio)

If `p` divides the denominator of a ladder ratio on the descent path, the base
ratio is not a `p`-unit and `ord_p(rho_n)` **dips** below `-5L` by the exceptional
multiplicity `mu`. Two cases seen: `7 | 28 = den(p_1/q_1)` makes **7 exceptional
for every row** (dip `mu=1`, `ord(rho) = -5L-1`); `11 | den(p_3/q_3)` makes 11
exceptional at digit `a=3`. In **every** exceptional row, `ord_p(q_n)` rises above
`kappa` by `nu >= mu`, so

    ord_p(p_n) = ord_p(rho_n) + ord_p(q_n)  >=  (-5L - mu) + (kappa + nu)  >=  kappa - 5L

is **preserved** (25/25 exceptional rows compensated, verified). The clean
unconditional invariant is thus the **combined** `ord_p(p_n) >= kappa - 5L` (or
equivalently the integer form `A_n`), which absorbs the denominator of the ladder
constants -- the corrected statement directive (2) asked for. `p = 2,3` are
strongly exceptional (they divide `28,84,...`); the ratio `ord(rho)` is wildly
negative there but `ord(p_n) >= kappa - 5L - ord_p(6)` still holds (they are
outside the `p>=5` (CB) range anyway).

## V5.4 -- Lucas control (negative) and the operative structure

Plain **Lucas fails**: `q_{ap+b} != q_a q_b` and `Q_{ap+b} != Q_a Q_b (mod p)`
(`Q_n = q_n/binom`), many failures at every `p` (V5.3 in script). So `q_n` is not
a Lucas sequence in the naive sense; the correct structure is the **Dwork ratio
descent** above (ratios of the two fundamental solutions `p_n, q_n`, not products
of digits). This matches Dwork/Frobenius theory for the ratio of truncated
solutions, cf. Delaygue-Rivoal-Roques (Dwork congruences for hypergeometric
sequences) and Straub / Malik-Straub (Lucas congruences for Apery-like numbers).

## V5.5 -- the general-kappa conjecture (Phase 2 reduced)

> **Conjecture (Phase-2 Dwork closure).** For every prime `p` and every `n`, with
> `a = floor(n/p)`, `kappa = ord_p binom(2n,n)`, `L = ord_p(d_n)`:
>
>   (FREE)  `ord_p(q_n) >= kappa`                                       [BZ sumQ -- known]
>   (DWORK) `p^5 (p_n/q_n) ≡ p_a/q_a (mod p)` and `p^3(ptil_n/q_n) ≡ ptil_a/q_a (mod p)`
>           (to >= 1 digit; at exceptional `p` the integer-normalised form).
>
> Together they give `ord_p(p_n) >= kappa - 5L`, i.e. **(CB) at `p` for all `p >= 5`**.

`(FREE)` is known. `(DWORK)` is a **known-technology** statement: a Dwork-Frobenius
congruence for the ratio of the two Zudilin solutions. **If `(DWORK)` is proved
(uniformly, with the exceptional-prime normalisation), Phase 2 is a theorem** --
no per-`n` certificate, no Wolstenholme-block assembly. This subsumes the §V4
head-window list (the `a=1` slice of `(DWORK)`): the constants there are now
explained as `p_1/q_1`, `ptil_1/q_1`, and the required depth `theta` is the
`a=1,kappa=1` case `k >= 1` of the descent-depth law.

## V5 status

- Ladder-ratio identification: **exact** (V5.0).
- `(DWORK)` descent + depth law `k >= 2-kappa`: **verified**, 272 descents, 0 floor failures.
- `(CB)` target `ord_p(p_n) >= kappa - 5L`: **verified 0 failures**, all `p>=5`, `n<=45`.
- Exceptional-prime compensation: **verified**, 25/25 rows.
- Lucas: **negative** (Dwork ratio is the correct structure).
- Remaining: prove `(DWORK)` uniformly (Dwork-Frobenius technology) -- the single
  clean gate for ALL of Phase 2. Run: `python3 lemma_cb_band_v5.py 45`.
