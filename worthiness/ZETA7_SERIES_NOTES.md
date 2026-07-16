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

## Where the series route says to look next
Alternating signs ⇒ **spread-pole / asymmetric VWP** (the structure of
`zn_check.compute_Zn`'s ζ(5..11) family), not the symmetric block form. A tuned
one-parameter asymmetric VWP in {ζ3,ζ5,ζ7} is the natural I′/I″ candidate. This is
the recommended series-side experiment; it is cheaper than your route (a) triple
Barnes and, if it lands, gives qₙ,sₙ,Pₙ at all n (enabling your n≥3 denominator
audit — the deliverable we both want).

## qₙ is NOT a Q_n-style multisum
Exhaustive search (`zeta7_dual_{triple,exhaust,Awide}.py`): qₙ = 1,61,52921 is not
any product-weight double/triple Apéry sum with subset-sum couplings, so the
weight-→index heuristic that gave your M₀,₈ Q_n double sum does not continue.
The triple-Barnes (your route a) or the asymmetric series above is required.
