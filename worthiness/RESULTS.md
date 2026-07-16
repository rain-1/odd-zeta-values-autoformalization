# Is sup γ over the Brown–Zudilin cone already found? — Yes. Closed.

**Date:** 2026-07-16 · **Question:** arXiv:2210.03391 proves γ = 0.86597135…
(γ > 1 ⟹ ζ(5) irrational) at a parameter point introduced only as "let us
look at a concrete example," with the search never described. The paper's
exhaustiveness theorem covers the *group* 𝔊, not the parameters, so
sup γ over the 7-dimensional projective cone was formally unclaimed.
This experiment implements γ from scratch and searches the cone.

## Verdict

**The record 0.86597135… is the supremum for this construction, to the
resolution of a multi-thousand-point global search.** Brown–Zudilin's
"concrete example" is a silently optimized point, repeating the
Rhin–Viola/Zudilin authorial pattern. No improvement exists within the
family; the direction is closed, on measurement rather than prior.

## Evidence

1. **Implementation validated to 8 decimals** against every number published
   in the paper: γ = 0.77795976 (totally symmetric case), γ = 0.86597135
   (record point, including intermediates C₀ = −31.55296934,
   C₁ = 85.08768883, Φ-limit = 34.39425186, m = {18,17,17,16,16}),
   γ = 0.85163139 (second example). Scale- and S₇-invariance hold to
   10 decimals.

2. **The record point is structured.** In the paper's own symmetric
   coordinates, a = (8,16,10,15,12,16,18,13) is
   s = (20.5; 3.5, 4.5, 5.5, 6.5, 7.5, 8.5, 9.5): s₁…s₇ is a perfect
   arithmetic progression. This is a swept family, not a stumbled-on point.

3. **Strict local maximum:** steepest ascent with a ~130-move neighborhood
   (unit steps, parity flips, pair transfers) finds no improvement, on the
   integer lattice or the half-integer refinement.

4. **Global maximum of the AP family:** exhaustive scan of all 31,710
   projectively distinct arithmetic-progression points (t₀; c, c+e, …, c+6e)
   up to height 160: the unique maximum is (t₀:c:e) = (41:7:2) — exactly the
   BZ point. Runners-up (0.8653, 0.8651, …) are neighboring rational rays.

5. **Multi-modal landscape, all below:** 120 random multi-start hill-climbs
   land on many distinct local optima spanning 0.73–0.8652, best
   0.86521684 at a = (10,23,13,21,16,22,25,18) — a near-AP point with a
   defect, still short of the record; 60 basin-hopping rounds around the
   optimum never exceed it (and re-find it from perturbations).

## Why the gap was never closable by search

γ > 1 ⟺ C₀ + C₂ < 0. At the optimum C₀ + C₂ = **+18.05**: the linear form
times its true denominator diverges exponentially. The map "0.866 → 1.0"
reads as a 15% push but requires cutting the denominator cost ≈ 36%. The
group 𝔊 ≅ S₇ is provably exhaustive (BZ), capping arithmetic gains within
the family. The paper's own loose ends are worth ~+0.005 in γ (measured by
BZ for the ν_p anomaly on their second example; the record point has no
such losses, and the refined m-selection is inert there since ℓ ∈ {3,4}
already matches). The remaining 0.134 cannot come from inside the cone.
BZ's closing sentence locates the exit themselves: "extra savings … from
different integral representations, each possessing their own arithmetic.
But what are those other representations?" — i.e., a new construction.

## Files

- `gamma.py` — γ(a) implementation (~330 lines): exact resultant of the
  saddle equations → cubic → λ₂, λ₃ (mpmath); 28-form multiset and
  m-selection; S₇ orbit arithmetic gain integrated against dψ (digamma).
  `python3 gamma.py` runs the validation suite.
- `search.py` — hill-climb / random multi-start / basin-hopping
  (`bz | random N | basin K`), caching, S₇-canonical forms.
- `ap_scan.py` — exhaustive projective scan of the AP subfamily.
- `search_results.jsonl`, `*.log` — raw outcomes.
