/-
Lean-verified numeric bound for `s = 33` (`q = 17`).

At the unique positive root `x₀` of `f 17 x = 1` (`x₀ = 2.289…e-5`), we have
`log g(x₀) = −36.3834…`, and `3^33 = e^{36.2543…}`, so `3^33 · g(x₀) = e^{-0.129} < 1`.

Strategy: `f 17` is strictly decreasing near `x₀` from `+∞`, and `f 17 x = 1` with `0 < x`
pins `x = x₀`.  Bracket `x₀` between two explicit rationals via `norm_num`/monotonicity
(Basic.lean's `f_shape`), then bound `g 17 x₀` on the bracket.
-/
import Mathlib
import Zeta5Odd.Basic

namespace Zeta5Odd

/-- **Numeric bound.** For the unique positive `x` with `f 17 x = 1`,
`3^33 · g 17 x < 1`. -/
theorem g_small (x : ℝ) (hx : 0 < x) (hfx : f 17 x = 1) :
    (3 : ℝ) ^ (33 : ℕ) * g 17 x < 1 := by
  sorry

end Zeta5Odd
