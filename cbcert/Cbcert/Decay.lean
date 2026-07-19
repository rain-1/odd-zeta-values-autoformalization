import Cbcert.Defs

/-!
# Lemma A — the decay relations (Layer L1) — STAGED

`E_M(a) = 0` for `1 ≤ M ≤ 4n+4`, and `E_M(ã) = 0` for `1 ≤ M ≤ 4n+2`.
These are the vanishing Laurent coefficients `[k^{-M}] R_n = 0` implied by
`R_n(k) = O(k^{-(4n+5)})` (`cb_certificate.tex`, eq. (decay) and the `E_M` display
in §5). Note the tighter range `4n+2` for `ã` (`ord_∞(−k(k+n)R_n) = 4n+3`).

## Status: STATED, proof STAGED (`sorry`). This is the risk-concentrate layer.

## Intended route (elementary power-series, avoids LaurentSeries API)
Let `x = 1/k`. Then `E_M(a) = [x^M] R_n(1/x)` because
`R_n(1/x) = Σ_{i,j} a_{i,j} x^i (1 + j x)^{-i} = Σ_{i,j,r} a_{i,j} C(-i,r) j^r x^{i+r}`,
so `[x^M] = Σ_{i,j} a_{i,j} C(-i, M-i) j^{M-i} = E_M(a)`. And
`R_n(1/x) = x^{4n+5} · Ñ(x) / D̃(x)` where `Ñ(x) = x^{2n+1} N_n(1/x)`,
`D̃(x) = x^{6n+6} D_n(1/x) = ∏_m (1 + m x)^6` has `D̃(0) = 1` (a unit in `ℚ⟦x⟧`),
so `R_n(1/x)` is `x^{4n+5}` times a power series, giving `[x^M] = 0` for `M ≤ 4n+4`.

The one nontrivial input is the partial-fraction identity
`R_n = Σ a_{i,j} (k+j)^{-i}` for the concrete `acoeff` (owned by
`Cbcert/PartialFraction.lean`); from it the two facts above are `PowerSeries`
bookkeeping. For `ã`, replace `R_n` by `−k(k+n)R_n` (degree count gives `4n+3`).
-/

namespace Cbcert.Decay

open Cbcert

/-- **Lemma A (base).** `E_M(a) = 0` for `1 ≤ M ≤ 4n+4`. -/
theorem decay_a (n M : ℕ) (hM1 : 1 ≤ M) (hM : M ≤ 4 * n + 4) :
    EM n M (acoeff n) = 0 := by
  sorry

/-- **Lemma A (companion).** `E_M(ã) = 0` for `1 ≤ M ≤ 4n+2`. -/
theorem decay_at (n M : ℕ) (hM1 : 1 ≤ M) (hM : M ≤ 4 * n + 2) :
    EM n M (atcoeff n) = 0 := by
  sorry

end Cbcert.Decay
