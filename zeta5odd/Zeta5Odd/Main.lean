/-
Final assembly (paper §4): at least one of ζ(5),…,ζ(33) is irrational.

Endgame: `b n := d_n^33·(7 r_n − r̂_n) ≥ 0`.  From Hanson `d_n ≤ 3^n` and the root limit
`(7 r_n − r̂_n)^{1/n} → g(x₀)` with `3^33·g(x₀) < 1`, we get `b n → 0`, hence `a·b n → 0`.
But `a·b n` is (via `elim_integer` + a common denominator `a` for the ζ-values, and
`seven_r_sub_rhat_pos_eventually`) a *positive integer*, so `a·b n ≥ 1`.  Contradiction.
-/
import Mathlib
import Zeta5Odd.Basic
import Zeta5Odd.Localize
import Zeta5Odd.Window
import Zeta5Odd.Roots
import Zeta5Odd.Ratio
import Zeta5Odd.ZetaValues
import Zeta5Odd.Forms
import Zeta5Odd.DnBound
import Zeta5Odd.Numeric

namespace Zeta5Odd

open Filter Topology
open scoped BigOperators

/-- The `n`-th root of the eliminated form tends to `g q x₀`.
Follows from `tendsto_root_r` and `tendsto_ratio` (`7 r − r̂ = r·(7 − r̂/r)`,
`r̂/r → 1`, and `h^{1/n} → 1` for `h → 6 > 0`). -/
lemma tendsto_seven_root (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    Tendsto (fun n : ℕ => (7 * r q n - rhat q n) ^ (1 / (n : ℝ))) atTop (𝓝 (g q x₀)) := by
  sorry

/-- If `w^{1/n} < σ` with `w ≥ 0`, `σ > 0`, `n ≥ 1`, then `w < σ^n`. -/
private lemma lt_pow_of_root_lt {w σ : ℝ} {n : ℕ} (hn : 1 ≤ n) (hw : 0 ≤ w) (hσ : 0 < σ)
    (h : w ^ (1 / (n : ℝ)) < σ) : w < σ ^ n := by
  have hne : (n : ℝ) ≠ 0 := by
    have hn0 : 0 < n := hn
    exact_mod_cast hn0.ne'
  have hrw : w = (w ^ (1 / (n : ℝ))) ^ n := by
    rw [← Real.rpow_natCast (w ^ (1 / (n : ℝ))) n, ← Real.rpow_mul hw, one_div,
      inv_mul_cancel₀ hne, Real.rpow_one]
  rw [hrw]
  exact pow_lt_pow_left₀ h (Real.rpow_nonneg hw _) (by omega)

/-- **Main theorem.** At least one of `ζ(5), ζ(7), …, ζ(33)` is irrational. -/
theorem zeta_odd_irrational : ∃ j ∈ oddIdx, Irrational (zetaVal j) := by
  by_contra hcon
  push_neg at hcon
  classical
  -- common denominator a for all ζ(j), j ∈ oddIdx
  obtain ⟨a, ha_pos, hden⟩ := exists_common_denom hcon
  -- integer values zf j := a·ζ(j)
  set zf : ℕ → ℤ := fun j => if h : j ∈ oddIdx then (hden j h).choose else 0 with hzf
  have hzf_spec : ∀ j ∈ oddIdx, (a : ℝ) * zetaVal j = (zf j : ℝ) := by
    intro j hj
    simp only [hzf, dif_pos hj]
    exact (hden j hj).choose_spec
  -- root x₀ of f 17
  obtain ⟨x₀, ⟨hx₀pos, hfx₀⟩, -⟩ := existsUnique_x0 17 (by norm_num)
  -- abbreviations
  set w : ℕ → ℝ := fun n => 7 * r 17 n - rhat 17 n with hw
  set b : ℕ → ℝ := fun n => (Nat.lcmUpto n : ℝ) ^ (33 : ℕ) * w n with hb
  -- (I) a·b n is an integer
  have hInt : ∀ n, ∃ M : ℤ, (M : ℝ) = a * b n := by
    intro n
    obtain ⟨A, A0, hEq⟩ := elim_integer n
    have hbn : b n = (∑ j ∈ oddIdx, (A j : ℝ) * zetaVal j) + (A0 : ℝ) := hEq
    refine ⟨(∑ j ∈ oddIdx, A j * zf j) + (a : ℤ) * A0, ?_⟩
    rw [hbn]
    push_cast
    rw [mul_add, Finset.mul_sum]
    have hterms : ∀ j ∈ oddIdx,
        (A j : ℝ) * (zf j : ℝ) = (a : ℝ) * ((A j : ℝ) * zetaVal j) := by
      intro j hj; rw [← hzf_spec j hj]; ring
    rw [Finset.sum_congr rfl hterms]
  -- (II) eventually  w n > 0  (paper's 7 r − r̂ > 0)
  have hwpos : ∀ᶠ n in atTop, 0 < w n :=
    seven_r_sub_rhat_pos_eventually 17 (by norm_num) hx₀pos hfx₀
  -- (III) numeric data
  set G : ℝ := g 17 x₀ with hG
  have hGpos : 0 < G := by
    rw [hG]; unfold g
    have h3 : (0 : ℝ) < x₀ + 3 := by linarith
    have h1 : (0 : ℝ) < x₀ + 1 := by linarith
    have h2 : (0 : ℝ) < x₀ + 2 := by linarith
    positivity
  have hLt1 : (3 : ℝ) ^ (33 : ℕ) * G < 1 := by rw [hG]; exact g_small x₀ hx₀pos hfx₀
  have h333pos : (0 : ℝ) < (3 : ℝ) ^ (33 : ℕ) := by positivity
  -- pick σ with G < σ and 3^33·σ < 1
  obtain ⟨σ, hGσ, hσ1⟩ : ∃ σ : ℝ, G < σ ∧ (3 : ℝ) ^ (33 : ℕ) * σ < 1 := by
    have hGlt : G < 1 / (3 : ℝ) ^ (33 : ℕ) := by
      rw [lt_div_iff₀ h333pos, mul_comm]; exact hLt1
    refine ⟨(G + 1 / (3 : ℝ) ^ (33 : ℕ)) / 2, by linarith, ?_⟩
    rw [← mul_div_assoc, div_lt_one (by norm_num : (0 : ℝ) < 2)]
    have hone : (3 : ℝ) ^ (33 : ℕ) * (G + 1 / (3 : ℝ) ^ (33 : ℕ)) = (3 : ℝ) ^ (33 : ℕ) * G + 1 := by
      rw [mul_add, mul_one_div, div_self h333pos.ne']
    rw [hone]; linarith [hLt1]
  have hσpos : 0 < σ := lt_trans hGpos hGσ
  -- root eventually < σ
  have hroot := tendsto_seven_root 17 (by norm_num) hx₀pos hfx₀
  have hrootσ : ∀ᶠ n in atTop, w n ^ (1 / (n : ℝ)) < σ := by
    filter_upwards [hroot.eventually (Iio_mem_nhds hGσ)] with n hn
    exact hn
  -- Hanson upper bound ⇒  b n ≤ (3^33)^n · w n
  have hbupper : ∀ᶠ n in atTop, b n ≤ ((3 : ℝ) ^ (33 : ℕ)) ^ n * w n := by
    filter_upwards [hwpos] with n hwn
    show (Nat.lcmUpto n : ℝ) ^ (33 : ℕ) * w n ≤ ((3 : ℝ) ^ (33 : ℕ)) ^ n * w n
    have hd : (Nat.lcmUpto n : ℝ) ≤ 3 ^ n := lcmUpto_le_three_pow n
    have hd0 : (0 : ℝ) ≤ (Nat.lcmUpto n : ℝ) := by positivity
    have hstep : (Nat.lcmUpto n : ℝ) ^ (33 : ℕ) ≤ (3 ^ n) ^ (33 : ℕ) := by gcongr
    have hpow : ((3 : ℝ) ^ n) ^ (33 : ℕ) = ((3 : ℝ) ^ (33 : ℕ)) ^ n := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hpow] at hstep
    exact mul_le_mul_of_nonneg_right hstep hwn.le
  -- squeeze bracket
  have hsqueeze : ∀ᶠ n in atTop, 0 ≤ b n ∧ b n ≤ ((3 : ℝ) ^ (33 : ℕ) * σ) ^ n := by
    filter_upwards [hwpos, hrootσ, hbupper, eventually_ge_atTop 1] with n hwn hrn hbn hn1
    have h1nn : (0 : ℝ) ≤ (Nat.lcmUpto n : ℝ) ^ (33 : ℕ) := by positivity
    have hbge0 : 0 ≤ b n := mul_nonneg h1nn hwn.le
    refine ⟨hbge0, ?_⟩
    have hwlt : w n < σ ^ n := lt_pow_of_root_lt hn1 hwn.le hσpos hrn
    calc b n ≤ ((3 : ℝ) ^ (33 : ℕ)) ^ n * w n := hbn
      _ ≤ ((3 : ℝ) ^ (33 : ℕ)) ^ n * σ ^ n :=
            mul_le_mul_of_nonneg_left hwlt.le (by positivity)
      _ = ((3 : ℝ) ^ (33 : ℕ) * σ) ^ n := (mul_pow _ _ _).symm
  -- b n → 0
  have htop : Tendsto (fun n => ((3 : ℝ) ^ (33 : ℕ) * σ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hσ1
  have hb0 : Tendsto b atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop
      (hsqueeze.mono (fun n h => h.1)) (hsqueeze.mono (fun n h => h.2))
  have hab0 : Tendsto (fun n => a * b n) atTop (𝓝 0) := by
    simpa using hb0.const_mul (a : ℝ)
  -- eventually a·b n < 1
  have hlt : ∀ᶠ n in atTop, a * b n < 1 := by
    filter_upwards [hab0.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    exact hn
  -- but a·b n ≥ 1 (positive integer)
  have hge : ∀ᶠ n in atTop, (1 : ℝ) ≤ a * b n := by
    filter_upwards [hwpos] with n hwn
    obtain ⟨M, hM⟩ := hInt n
    have h1nn : (0 : ℝ) < (Nat.lcmUpto n : ℝ) ^ (33 : ℕ) := by
      have := Nat.lcmUpto_pos n; positivity
    have hap : (0 : ℝ) < a := by exact_mod_cast ha_pos
    have hbpos : 0 < b n := mul_pos h1nn hwn
    have habpos : 0 < a * b n := mul_pos hap hbpos
    have hMpos : 0 < M := by
      have : (0 : ℝ) < (M : ℝ) := by rw [hM]; exact habpos
      exact_mod_cast this
    calc (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (hMpos : (0 : ℤ) < M)
      _ = a * b n := hM
  -- contradiction
  obtain ⟨n, hn1, hn2⟩ := (hlt.and hge).exists
  linarith

end Zeta5Odd
