/-
Lemma 4, second claim: r n / r̂ n → 1 (what makes 7 r − r̂ > 0 eventually).
Owner file — only `tendsto_ratio` lives here.
May use `sum_localizes` and `term_ratio_on_window` (imported, possibly
still sorry'd) as inputs.
-/
import Zeta5Odd.Basic
import Zeta5Odd.Localize
import Zeta5Odd.Window

open Filter Finset
open scoped Nat Topology

namespace Zeta5Odd

/-- Lemma 4, second claim: the two linear forms are asymptotically equal.
This is what makes `7 r_n - r̂_n > 0` eventually, hence nonvanishing. -/
theorem tendsto_ratio (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    Tendsto (fun n : ℕ => r q n / rhat q n) atTop (𝓝 1) := by
  sorry

end Zeta5Odd
