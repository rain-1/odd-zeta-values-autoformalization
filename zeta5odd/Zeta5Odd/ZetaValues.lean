/-
Zeta values as real series, the target index set, and the common-denominator
lemma used in the final contradiction.
-/
import Mathlib
import Zeta5Odd.Basic

namespace Zeta5Odd

open scoped BigOperators

/-- The real zeta value `ζ(j) = ∑_{n≥1} 1/n^j`, written as `∑_{n≥0} 1/(n+1)^j`. -/
noncomputable def zetaVal (j : ℕ) : ℝ := ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ j

/-- Odd indices from 5 to 33 — the target zeta values for `s = 33`. -/
def oddIdx : Finset ℕ := (Finset.Icc 5 33).filter (fun j => Odd j)

lemma zetaVal_nonneg (j : ℕ) : 0 ≤ zetaVal j :=
  tsum_nonneg (fun n => by positivity)

/-- If every `ζ(j)`, `j ∈ oddIdx`, is rational, there is a common positive
integer denominator `a` with `a·ζ(j) ∈ ℤ` for all these `j`. -/
lemma exists_common_denom (h : ∀ j ∈ oddIdx, ¬ Irrational (zetaVal j)) :
    ∃ a : ℕ, 0 < a ∧ ∀ j ∈ oddIdx, ∃ z : ℤ, (a : ℝ) * zetaVal j = z := by
  classical
  -- `den · q = num` in ℝ
  have hQd : ∀ q : ℚ, ((q.den : ℝ)) * (q : ℝ) = (q.num : ℝ) := by
    intro q
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    rw [Rat.cast_def]
    field_simp
  -- each ζ(j) is some rational Q j
  have hex : ∀ j ∈ oddIdx, ∃ q : ℚ, (q : ℝ) = zetaVal j := by
    intro j hj
    have hmem : zetaVal j ∈ Set.range ((↑) : ℚ → ℝ) := by
      by_contra hc; exact h j hj hc
    obtain ⟨q, hq⟩ := hmem
    exact ⟨q, hq⟩
  choose! Q hQ using hex
  refine ⟨∏ i ∈ oddIdx, (Q i).den, Finset.prod_pos (fun i _ => (Q i).den_pos), ?_⟩
  intro j hj
  have hdvd : (Q j).den ∣ ∏ i ∈ oddIdx, (Q i).den :=
    Finset.dvd_prod_of_mem (fun i => (Q i).den) hj
  set m : ℕ := (∏ i ∈ oddIdx, (Q i).den) / (Q j).den with hm
  have hma : m * (Q j).den = ∏ i ∈ oddIdx, (Q i).den := Nat.div_mul_cancel hdvd
  refine ⟨(m : ℤ) * (Q j).num, ?_⟩
  rw [← hQ j hj]
  have hacast : ((∏ i ∈ oddIdx, (Q i).den : ℕ) : ℝ) = (m : ℝ) * ((Q j).den : ℝ) := by
    rw [← hma]; push_cast; ring
  rw [hacast]
  push_cast
  rw [mul_assoc, hQd (Q j)]

end Zeta5Odd
