# Conjecture: exact denominators for Brown–Zudilin ζ(5) linear forms

**Status:** empirical, 103 verified (a, n) cells, 2026-07-16. No counterexample.

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
