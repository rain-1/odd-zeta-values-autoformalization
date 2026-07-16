/-
Piece 1 of Lemma 4: εn-localization of the sum r n.
Owner file — only `sum_localizes` (and its private helpers) lives here.
-/
import Zeta5Odd.Basic

open Filter Finset
open scoped Nat Topology

namespace Zeta5Odd

/-- Piece 1 (εn-localization): for every ε > 0, the tail of `r n` outside
the window `|k - x₀ n| ≤ εn` is exponentially negligible relative to the
whole sum.  This replaces de Bruijn's γ√n localization. -/
theorem sum_localizes (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
        (∑' k : {k : ℕ // (k : ℝ) < (x₀ - ε) * n ∨ (x₀ + ε) * n < (k : ℝ)},
          c q n k) / r q n)
      atTop (𝓝 0) := by
  sorry

/-- Same localization for the half-shifted series `r̂` (needed by
`tendsto_ratio`): the machinery is identical — the term ratio
`chat (k+1) / chat k` is the same exact rational function up to
half-integer shifts. -/
theorem sum_localizes_chat (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
        (∑' k : {k : ℕ // (k : ℝ) < (x₀ - ε) * n ∨ (x₀ + ε) * n < (k : ℝ)},
          chat q n k) / rhat q n)
      atTop (𝓝 0) := by
  sorry

end Zeta5Odd
