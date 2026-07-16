/-
Lemma 4, first claims: the nth-root limits for r and r̂.
Owner file — only `tendsto_root_r` and `tendsto_root_rhat` live here.
May use `sum_localizes` (imported, possibly still sorry'd) as an input.
-/
import Zeta5Odd.Basic
import Zeta5Odd.Localize

open Filter Finset
open scoped Nat Topology

namespace Zeta5Odd

/-- Lemma 4, first claim for `r`. -/
theorem tendsto_root_r (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    Tendsto (fun n : ℕ => r q n ^ (1 / (n : ℝ))) atTop (𝓝 (g q x₀)) := by
  sorry

/-- Lemma 4, first claim for `r̂`. -/
theorem tendsto_root_rhat (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    Tendsto (fun n : ℕ => rhat q n ^ (1 / (n : ℝ))) atTop (𝓝 (g q x₀)) := by
  sorry

end Zeta5Odd
