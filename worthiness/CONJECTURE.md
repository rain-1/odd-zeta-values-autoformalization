# Conjecture: exact denominators for Brown–Zudilin ζ(5) linear forms

**Status:** empirical; 164 verified (a, n) cells as of 2026-07-16 late.
**AMENDED after one verified exception — see the addendum at the bottom.**
The {2,3} ceilings hold at every cell (excess₂ ≤ +2 attained 46×, excess₃
≤ +1 attained 30×). The clause "no excess at p ≥ 5" is FALSIFIED as
stated: one verified cell (a = (6,2,6,1,6,4,5,5), n = 1) has excess +1 at
p = 7 = m₁ against the ν-sharpened prediction (den(P) = 2⁷·3⁴·5²·7,
stable under precision changes; ν₇ = 1 claimed by the orbit bound, not
realized). Note p = m₁ is the boundary prime of the multiset. The orbit-transfer
mechanism is now CONFIRMED by direct audit: the maximizing orbit partner
a′ = (6,2,5,2,4,6,6,5) has den(P) = 2⁶·3⁴·5²·7² — raw excess +1 at p=7
against its own d-product, exactly as the exact identity
I′(ga) = I′(a)·(factorial ratio) predicts from the first cell. Two
consequences: (i) even the raw (ν-free) 12·(d-product) law fails at
p = 7 = m₁ at some points, so the {2,3}-Bernoulli mechanism is the BULK
story but not the whole story — there is a rarer boundary-prime effect
(observed size +1, at p = max h); (ii) excesses are orbit-coherent, not
per-point accidents: the right invariant is an orbit-level "anomaly
divisor", and the ν-sharpened prediction inherits partners' anomalies —
which is exactly how one cell's ledger betrayed its neighbor's. The
agreement of two independent PSLQ recoveries with the exact factorial-
ratio identity is also a strong end-to-end validation of the pipeline.
The conjecture below should be read with this amendment; the original
text is preserved for the record.

## Setup

For an admissible a (all 28 forms of the multiset h(a) non-negative), write
I′(a·n) = Q_n ζ(5) − P_n with Q_n ∈ ℤ (arXiv:2210.03391). Let

    D_ν(a, n) = ∏_i d_{m_i n} / Φ*_n,    Φ*_n = ∏_{ALL p} p^{ν_p},

where m₁ ≥ … ≥ m₅ are the five largest entries of h(a),
ν_p = max_{g ∈ 𝔊} ord_p( ∏_{i∈𝓕} (h_i(a)n)! / ∏_{i∈𝓕} (h_i(g a)n)! ),
i.e. Brown–Zudilin's sharpening (their eq. (nu_p)) **extended from
p > √(m₁n) to every prime** — legitimate because the underlying identity
I′(g a) = I′(a)·∏(h_i(a))!/∏(h_i(g a))! is exact p-adically.

## Conjecture

    12 · D_ν(a, n) · I′(a·n)  ∈  ℤ ζ(5) + ℤ        for all admissible a, n ≥ 1,

and the factor 12 = 2²·3 is sharp: the 2-part is attained (e.g. the totally
symmetric point at every n = 1…5, and a = (3,1,3,2,2,1,1,2), (4,1,3,2,3,2,4,1),
(3,1,2,1,1,2,2,1) at n = 1, 2), and the 3-part is attained (14 cells, all at
points where the 3-adic prediction is tight).

Equivalently, per prime: ord_p den(P_n) ≤ ord_p D_ν + [2 bits if p=2, 1 if p=3,
0 if p ≥ 5].

## Evidence

- 103 distinct (a, n): 99 points at n=1 (heights up to entry 5), five points
  at n=2, symmetric point at n=1..5. Excess distribution (req − pred):
  p=2: max +2 over all cells (attained 28×); p=3: max +1 (attained 14×);
  p ∈ {5,7,11}: never positive.
- Brown–Zudilin's published claims (their (incl), (sharp_incl), and the
  totally-symmetric display d_n⁵P_n ∈ ℤ) are **false as stated** — off by
  exactly the factor above; e.g. their own printed P₂ = 1190161/384 against
  their d₂⁵ = 32. Their claims hold after multiplying by 12.
- The ζ(3)-companion behaves analogously: at the symmetric point,
  den(P̂_n) = 2 · (2-part of d_n²d_{2n}) exactly for n = 1…5.

## Interpretation (heuristic)

The construction obtains I′ by motivically "setting ζ(2) := 0" — a row
operation against the period (2πi)². The integral normalization of that
period carries the Bernoulli denominator (ζ(2) = π²/6; the relevant lattice
constant is 24 = 2³·3). A universal 2²·3 loss in exactly the ζ(5)-coefficient
pair (and 2¹ in the ζ(3)-pair) is the fingerprint such an elimination step
would leave. Proving the conjecture should amount to making the
ζ(2)-elimination integral, i.e. tracking the Betti lattice through the row
operation in the period matrix (Section "Geometry" of the paper).

## Falsification surface

Any future audit cell with excess₂ > 2, excess₃ > 1, or any excess at p ≥ 5
kills the conjecture. Growth cells (n = 3, 6, 7) and taller points are being
computed (see worker queues).

## Provenance

Pipeline: `audit.py` (exact Q via the paper's double sum; J via the
₃F₂-product integral, fast path `fast_eval.py`; PSLQ recovery of P, P̂ over
{1, ζ(2)}; anchors reproduce the paper's exact printed rationals).
Data: `audit_map_results.jsonl`, `tiamat_results.jsonl`, `symmetric_growth.log`.
Analysis: `explore_findings.py` and the excess-distribution snippets in the
session log.


## Addendum 2 (same day, later): scan + growth verdicts

* Boundary-prime recurrence scan: 0/40 fresh trigger-condition points
  (m₁ prime ∈ {5,7,11,13}, ν_{m₁} ≥ 1) show any p = m₁ excess. The p=7
  orbit re-audited at n=2 flips to slack (−2) at BOTH partner points,
  orbit-coherently. Verdict: the p ≥ 5 effect is a single-orbit, n=1-only
  fluctuation — rare and non-persistent, not structural.
* Growth series (n up to 5 at the anomalous points, n=8 symmetric):
  all slack trajectories are bounded wobble (outlier: −6,−5,−4,−5,−3);
  excesses decay rather than compound; the symmetric 2-adic +2 law holds
  through n=8 with the 3-adic ceiling attained there. **No measured cell
  or direction shows growing slack** — the divisible-class program's
  exponential-upside question is answered negatively on all data so far
  (~215 cells).
