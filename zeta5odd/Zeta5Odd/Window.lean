/-
Piece 2 of Lemma 4: the termwise ratio c/ĉ on the window.
Owner file — only `term_ratio_on_window` (and its private helpers) lives here.
Key available input: `centralBinom_rate` in Basic.lean.
-/
import Zeta5Odd.Basic

open Filter Finset
open scoped Nat Topology

namespace Zeta5Odd

/-- Piece 2 (termwise ratio on the window): uniformly over
`|k - x₀ n| ≤ εn`, the ratio `c k / ĉ k` is eventually within `δ(ε)` of 1,
where `δ(ε) → 0` with `ε`.  Uses the two-sided central-binomial rate
`centralBinom_rate` for the expression (e10) of the paper. -/
theorem term_ratio_on_window (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (x₀ - ε) * n ≤ k → (k : ℝ) ≤ (x₀ + ε) * n →
      |c q n k / chat q n k - 1| ≤ δ := by
  sorry

end Zeta5Odd
