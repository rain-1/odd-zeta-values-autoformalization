# ζ(7) SERIES-route notes (coordination with ZETA7_FAMILY.md scout)

Full write-up: **`ZETA7_DUAL.md`**. Scripts: `zeta7_dual_*.py`.

## What the series route establishes (complements your integral-side audit)
- Your qₙ = 1,61,52921 and sₙ = 0,300,261153 transcription is **confirmed** from
  the series side (same anchors, `zeta7_dual_match.py`).
- The `zn_check` engine is now **independently re-validated**: it reproduces
  Zudilin's exact ζ(5) VWP series (arXiv math/0206178 eq. 7) to the digit for
  n=0,1,2, and the ζ3-elimination recipe reproduces BZ's Q_n = 1,21,2989 exactly.
  So engine results below are trustworthy.

## The decisive obstruction (new)
BZ's I′ₙ and I″ₙ have **opposite-sign adjacent zeta coefficients**
(I′: +ζ7, −ζ5;  I″: +ζ5, −ζ3). Every reflection-antisymmetric Zudilin block
series gives **same-sign** odd zetas. Hence:
- Your route (b) k=9 dual F̃₉ (all-equal) is excluded on the series side too, for
  a sharper reason than "different linear form": **wrong sign pattern**.
- The naïve den⁸ ζ(7) sibling of Zudilin's eq.7 exists (I tabulate it, ρ_n, in
  §2 of ZETA7_DUAL.md — a clean new {1,ζ3,ζ5,ζ7} family, ρ₀=ζ7) but is **not** BZ.

## UPDATE — spread-pole route also EXCLUDED (ZETA7_DUAL.md §7)
The "alternating signs ⇒ spread poles" idea was **tested and refuted**. Using the
KR master family (math/0311114 eq. 782; A=6,C=2 targets {1,ζ5,ζ7} directly):
- `compute_Zn` itself gives z5/z7 **> 0** — spread poles do NOT flip the sign;
- 11 284 staircase-asymmetric + 1 248 systematic-VWP + symmetric-block configs:
  **every VWP-clean {ζ5,ζ7} form has r5 > 0**; the only r5<0 configs carry even
  zetas (ζ4,ζ6) → not VWP → not BZ.
Reason: I′ₙ is a *projection* (ζ2=0) of Iₙ with opposite-sign adjacent zetas; VWP
single sums are simultaneous approximations with same-sign adjacent zetas. Distinct
object classes. **The single-sum VWP route is closed.**

## Where to look next
**Your route (a), the triple Mellin–Barnes reduction of the primal integral, is now
the only path to I′ₙ** (hence qₙ,sₙ,Pₙ at n≥3 and the denominator audit). The series
side has exhausted single sums. If a double-sum representation is admissible, the
M₀,₁₀ analogue of your `sumQ` double-sum (a triple sum) is the object — but see
ZETA7_DUAL.md §3.5: qₙ is not a product-weight subset-coupled multisum, so the
triple sum's coupling is non-obvious and must come from the Barnes bookkeeping.

## qₙ is NOT a Q_n-style multisum
Exhaustive search (`zeta7_dual_{triple,exhaust,Awide}.py`): qₙ = 1,61,52921 is not
any product-weight double/triple Apéry sum with subset-sum couplings, so the
weight-→index heuristic that gave your M₀,₈ Q_n double sum does not continue.
The triple-Barnes (your route a) or the asymmetric series above is required.
