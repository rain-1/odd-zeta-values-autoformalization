import Cbcert.Defs

/-!
# The cleared partial-fraction identity (Layer L1, load-bearing) — STAGED

The concrete coefficients `acoeff n i j = [t^{6-i}] B_j` are, by construction, the
partial-fraction coefficients of `R_n`. Cleared of denominators, that is the
polynomial identity `pf_cleared` below: multiply `R_n = Σ a_{i,j}/(k+j)^i` through
by `D_n(k) = ∏_{m=0}^n (k+m)^6`. It is the load-bearing input to Lemma A (`Decay`).

`N_n(k) = (n!)^4 (k + n/2) ∏_{m=1}^n (k−m) ∏_{m=1}^n (k+n+m)`  (degree `2n+1`)
`D_n(k) = ∏_{m=0}^n (k+m)^6`                                   (degree `6n+6`)
`N_n(k) = Σ_{j=0}^n Σ_{i=1}^6 a_{i,j} (k+j)^{6-i} ∏_{m≠j} (k+m)^6`.

At `n = 2` this is exactly `ErrorExhibit.pf_cert` (there proved by `ring` after
unfolding the hardcoded `ac`); here it must hold for all `n`.

## Status: STATED, proof STAGED (`sorry`). Owner: Worker A1.

## Intended route
`acoeff n i j = [t^{6-i}] B_j` where `B_j(k) = (k+j)^6 R_n(k) = N_n(k)/∏_{m≠j}(k+m)^6`.
Two routes:
- (Taylor/derivative) The `(k+j)`-principal part of `R_n` at the pole `−j` has, by
  definition of `acoeff`, coefficients matching the Taylor jet of `B_j`; the standard
  Hermite/partial-fraction uniqueness over `ℚ[k]` gives the identity. In Lean:
  evaluate both sides' `(k+j)`-jets to order 5 and match, OR
- (interpolation) Both sides are polynomials in `k` of degree `≤ 6n+5`; prove equality
  as `Polynomial ℚ` by showing all coefficients agree, reducing to the truncated-series
  algebra that DEFINES `acoeff` (the cleanest for the concrete definition: the RHS's
  `(k+j)`-adic expansion is `Σ_i acoeff n i j (k+j)^{6-i} · [unit at −j]`, and
  `acoeff` is exactly that unit's Taylor data).

Numeric cross-check available: `ErrorExhibit.pf_cert` (n=2).
-/

namespace Cbcert.PartialFraction

open Cbcert

/-- `N_n(k)` — the numerator of `R_n`. -/
def Nnum (n : ℕ) (k : ℚ) : ℚ :=
  (Nat.factorial n : ℚ) ^ 4 * (k + (n : ℚ) / 2)
    * (∏ m ∈ Finset.Icc 1 n, (k - (m : ℚ)))
    * (∏ m ∈ Finset.Icc 1 n, (k + (n : ℚ) + (m : ℚ)))

/-- **The cleared partial-fraction identity.** For all `n` and all `k : ℚ`. -/
theorem pf_cleared (n : ℕ) (k : ℚ) :
    Nnum n k
      = ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.Icc 1 6,
          acoeff n i j * (k + (j : ℚ)) ^ (6 - i)
            * ∏ m ∈ (Finset.range (n + 1)).erase j, (k + (m : ℚ)) ^ 6 := by
  sorry

end Cbcert.PartialFraction
