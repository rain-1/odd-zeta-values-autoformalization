# Phase-2 (DWORK): the (HW) two-digit calculation — itemized analysis

Worker note, 2026-07-19 (Opus, continuation of `PHASE2_DWORK_A1.md`).
Executes the coordinator's continuation task on the single open a=1 identity (HW).

Exact `Fraction`/integer arithmetic. **HONESTY: every result is a finite exact
check over the stated grid. The fully symbolic-in-`r` proof is NOT achieved (nor
is it in Sol's memo, which calls it "a concrete calculation, not yet a theorem").**
Script: `dwork_hw.py` (run `python3 dwork_hw.py`).

---

## The object

    Q_HW(n,p) := p^5·Sing − (29/28)·u − (101/84)·p^2·w,
    Sing = Σ_{i=1}^6 (−1)^{i+1} p^{−i} S_i^head,   S_i^head = Σ_{j=0}^r a_{i,j},

with `n = p+r`. Target (Sol eq 17): `ord_p(Q_HW) ≥ 3`. The p⁰ digit is forced by
the window `E_M` relations (`lemma_cb_band_v4` C — verified); the **p¹ and p²
digits were the "two missing digits"** the `E_M` machinery could not force.

---

## Result 1 — (HW) holds on-grid with large margin (VERIFIED)

**`ord_p(Q_HW) ≥ 5`** uniformly on the band, occasionally 6 (never below 5).
Grid: `p ∈ {11,13,17,19,23,29,31,37}`, every `r ∈ [⌈p/2⌉, p−1]` (86 pairs, 0
below 5). So **not only c₀ but c₁,c₂,c₃,c₄ all vanish** — the two missing digits
are (verified) zero, with two further digits to spare. The constants `29/28`,
`101/84` capture the `Sing↔(u,w)` match to depth 5, far beyond the mod-p³ target.

STATUS: **VERIFIED-ON-GRID**, not proved. This is stronger than the coordinator's
mod-p³ target but remains a finite check, scoped to the grid above.

## Result 2 — the cancellation is GLOBAL, not termwise (VERIFIED, itemized)

Write `Q_HW` as 8 exact items: the six pole-layers `L_i = (−1)^{i+1}p^{5−i}S_i^head`
and the two constant terms `Cu = −(29/28)u`, `Cw = −(101/84)p^2 w`. Individual
items reach `ord_p = 0` (units); the exact sum reaches `ord_p = 5` — a **valuation
jump of 5 by exact cancellation**. (p-adic digits do NOT add columnwise — carries
obstruct any naive "digit-column" table; the honest display is by exact valuation.)

Example `p=23, r=22`: item ords `Cu:0 L5:0 L6:0 L4:0 Cw:0 L2:0 L3:0 L1:∞`,
sum ord `= 5`. **Layer-deletion sensitivity control** (exact): dropping any of
`L4,L5,L6` returns the sum to `ord 0`; dropping `L2` or `L3` to `ord ≤ 1`; only
`L1` (already `ord 8`) is inert. So every pole-layer `i=2..6` is essential to the
mod-p³ vanishing — it is a genuine six-layer (weight-structure) cancellation, not
a layerwise or blockwise one. (This is the exact analogue of the LEMMA_CB §2.6
"global middle↔edge" finding, now at the head-window/Dwork level.)

## Result 3 — P4 verdict: centre-vanishing YES, `(2r+1−p)` factor NO

Sol P4 predicts the first-correction digit `c(r)` (of `D(r)=p^5ρ_{p+r}−ρ_1`, at
depth `3−κ`) is antisymmetric under `r→p−1−r` with a factor `(2r+1−p)`.

- **CONFIRMED (exact, every prime `p=11..41`):** `c((p−1)/2) = 0` — the
  first-correction digit vanishes at the reflection centre. This is the
  derivative-Frobenius signature (the "reflection-centre boost" of `PHASE2_BAND_V`
  V5.1): at the centre `ord(D)` jumps by ≥1.
- **FALSIFIED (exact):** `c(r)` is **not** a global multiple of `(2r+1−p)` —
  `c(r)/(2r+1−p) mod p` takes many distinct values (e.g. 23 distinct at `p=41`),
  not one. `c(r)` vanishes at the centre but has additional structure / sporadic
  extra roots (matching the sporadic extra boosts at `r=3,5` for `p=23`, etc.,
  seen in the ord-scan). The boost pattern is richer than a single linear factor.

VERDICT: the qualitative derivative-Frobenius / centre-vanishing prediction is
correct; the specific linear `(2r+1−p)` form is not.

## Result 4 — P6 verdict: NOT executed

Sol P6 (delete the reversal identity → p¹ digit reappears; delete the block-
binomial → p² digit reappears) is an ingredient-deletion test on the **full
Φ/Bell symbolic reconstruction** of `a_{i,j}` (Sol eq 3–10), which routes the
head-window sums through the full-block harmonics `H_{p−1}^{(t)}`. That
reconstruction was **not built** in this session (the block tools `Φ`, `E_m`,
reversal, valuation inputs are individually verified in `dwork_a1_band.py`, but
they were not assembled into a togglable expansion of `Q_HW`). The available
exact sensitivity control is the **pole-layer deletion** of Result 2, which tests
a different (weight-layer) axis of the cancellation, not Sol's harmonic-block axis.

STATUS: OPEN. This is the honest gap: the two missing digits are verified to
vanish (Result 1) and shown to vanish *globally across the six pole-layers*
(Result 2), but the *reason* in Sol's harmonic-block terms (reversal-identity
coupling `H_1/H_2, H_3/H_4` for p¹; block-binomial + Bell `D_1D_2,D_3` for p²) is
not demonstrated by deletion — it would need the Φ/Bell rebuild.

---

## Bottom line — (HW) status

| Claim | Status |
|---|---|
| `ord_p(Q_HW) ≥ 3` (the (HW) target, both missing digits vanish) | **VERIFIED-ON-GRID** (in fact ≥5), 86 pairs, p=11..37 |
| cancellation is global across the six pole-layers (not termwise) | **VERIFIED** (exact valuation jump + layer-deletion) |
| symbolic-in-`r` proof of (HW) | **OPEN** (not achieved; not in Sol's memo either) |
| **P4** centre-vanishing `c((p−1)/2)=0` | **CONFIRMED** exact, all primes |
| **P4** linear `(2r+1−p)` factor | **FALSIFIED** exact (c has higher structure) |
| **P6** reversal-id / block-binomial deletion | **NOT EXECUTED** (needs Φ/Bell rebuild) |

The (HW) identity is on very firm empirical ground (depth 5, uniform) and its
cancellation mechanism is localized to the six-pole-layer (weight) structure with
an exact sensitivity control. The two remaining pieces of a *proof* are (i) the
Φ/Bell symbolic assembly that would let the P6 deletion tests run and expose
Sol's predicted harmonic-block sources, and (ii) the closed symbolic-in-`r`
argument. Neither is delivered here; both are bounded, well-specified next steps.
