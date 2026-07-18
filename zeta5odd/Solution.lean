/-
Solution for `leanprover/comparator`.

Proves the Mathlib-only statement of `Challenge.lean` — phrased with Mathlib's
`riemannZeta` — from the project's main theorem `Zeta5Odd.zeta_odd_irrational`.

Two small bridges are needed, both discharged here:
  * the index set `Zeta5Odd.oddIdx = (Finset.Icc 5 33).filter Odd` unpacks to
    `Odd j ∧ 5 ≤ j ∧ j ≤ 33`;
  * for a natural k > 1, `(riemannZeta k).re = Zeta5Odd.zetaVal k`, i.e. the
    real part of Mathlib's `riemannZeta` at an integer is the real Dirichlet
    series `∑' n, 1/(n+1)ᵏ` that the project reasons about.

`#print axioms zeta_odd_irrational` yields exactly
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib
import Zeta5Odd

open Complex

/-- For a natural `k > 1`, the real part of Mathlib's `riemannZeta k` is the
real Dirichlet series `Zeta5Odd.zetaVal k = ∑' n, 1/(n+1)ᵏ`. -/
theorem re_riemannZeta_eq_zetaVal {k : ℕ} (hk : 1 < k) :
    (riemannZeta (k : ℂ)).re = Zeta5Odd.zetaVal k := by
  have hre : 1 < ((k : ℂ)).re := by
    rw [Complex.natCast_re]; exact_mod_cast hk
  have hterm : ∀ n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ (k : ℂ)
      = ((1 / ((n : ℝ) + 1) ^ k : ℝ) : ℂ) := by
    intro n
    rw [Complex.cpow_natCast]
    push_cast
    ring
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre, tsum_congr hterm,
    ← Complex.ofReal_tsum, Complex.ofReal_re]
  rfl

theorem zeta_odd_irrational :
    ∃ j : ℕ, Odd j ∧ 5 ≤ j ∧ j ≤ 33 ∧ Irrational (riemannZeta j).re := by
  obtain ⟨j, hjmem, hirr⟩ := Zeta5Odd.zeta_odd_irrational
  rw [Zeta5Odd.oddIdx, Finset.mem_filter, Finset.mem_Icc] at hjmem
  obtain ⟨⟨h5, h33⟩, hodd⟩ := hjmem
  refine ⟨j, hodd, h5, h33, ?_⟩
  rw [re_riemannZeta_eq_zetaVal (by omega : 1 < j)]
  exact hirr
