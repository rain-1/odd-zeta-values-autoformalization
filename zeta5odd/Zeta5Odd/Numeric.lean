/-
Lean-verified numeric bound for `s = 33` (`q = 17`).

At the unique positive root `x₀` of `f 17 x = 1` (`x₀ = 2.289…e-5`), we have
`log g(x₀) = −36.3834…`, and `3^33 = e^{36.2543…}`, so `3^33 · g(x₀) = e^{-0.129} < 1`.

Strategy (`b = 1/40`):
* (A) `0 < x` and `f 17 x = 1` force `x ≤ 1/40`.  Indeed if `x > 1/40` then a
  three-term binomial lower bound on `(x+2)^17` gives `(x+3)(x+1)^17 < x(x+2)^17`,
  i.e. `f 17 x < 1`, contradicting `f 17 x = 1`.
* (B) `g 17` is increasing on `[0, 1/40]` (log-derivative
  `6/(x+3)+34/(x+1)-68/(x+2) = (-28x²-84x+12)/((x+3)(x+1)(x+2)) > 0` there), so
  `g 17 x ≤ g 17 (1/40)`, and `3^33 · g 17 (1/40) < 1` is an exact rational bound.
-/
import Mathlib
import Zeta5Odd.Basic

namespace Zeta5Odd

open Real

/-- **Numeric bound.** For the unique positive `x` with `f 17 x = 1`,
`3^33 · g 17 x < 1`. -/
theorem g_small (x : ℝ) (hx : 0 < x) (hfx : f 17 x = 1) :
    (3 : ℝ) ^ (33 : ℕ) * g 17 x < 1 := by
  have hx1 : (0:ℝ) < x + 1 := by linarith
  have hx2 : (0:ℝ) < x + 2 := by linarith
  have hx3 : (0:ℝ) < x + 3 := by linarith
  -- (A) upper bracket: x ≤ 1/40.
  have hxb : x ≤ 1 / 40 := by
    by_contra hcon
    push_neg at hcon           -- hcon : 1/40 < x
    -- three-term binomial lower bound: (x+1)^17 + 17(x+1)^16 + 136(x+1)^15 ≤ (x+2)^17
    have hB : (x + 1) ^ 17 + 17 * (x + 1) ^ 16 + 136 * (x + 1) ^ 15 ≤ (x + 2) ^ 17 := by
      have hexp : (x + 2) ^ 17
          = (x + 1) ^ 17 + 17 * (x + 1) ^ 16 + 136 * (x + 1) ^ 15
            + (680 * (x + 1) ^ 14 + 2380 * (x + 1) ^ 13 + 6188 * (x + 1) ^ 12
              + 12376 * (x + 1) ^ 11 + 19448 * (x + 1) ^ 10 + 24310 * (x + 1) ^ 9
              + 24310 * (x + 1) ^ 8 + 19448 * (x + 1) ^ 7 + 12376 * (x + 1) ^ 6
              + 6188 * (x + 1) ^ 5 + 2380 * (x + 1) ^ 4 + 680 * (x + 1) ^ 3
              + 136 * (x + 1) ^ 2 + 17 * (x + 1) + 1) := by ring
      have hrest : (0:ℝ) ≤ 680 * (x + 1) ^ 14 + 2380 * (x + 1) ^ 13 + 6188 * (x + 1) ^ 12
              + 12376 * (x + 1) ^ 11 + 19448 * (x + 1) ^ 10 + 24310 * (x + 1) ^ 9
              + 24310 * (x + 1) ^ 8 + 19448 * (x + 1) ^ 7 + 12376 * (x + 1) ^ 6
              + 6188 * (x + 1) ^ 5 + 2380 * (x + 1) ^ 4 + 680 * (x + 1) ^ 3
              + 136 * (x + 1) ^ 2 + 17 * (x + 1) + 1 := by positivity
      linarith [hexp, hrest]
    -- key polynomial inequality (x+3)(x+1)^17 < x(x+2)^17
    have key : (x + 3) * (x + 1) ^ 17 < x * (x + 2) ^ 17 := by
      have h1 : x * ((x + 1) ^ 17 + 17 * (x + 1) ^ 16 + 136 * (x + 1) ^ 15)
          ≤ x * (x + 2) ^ 17 := mul_le_mul_of_nonneg_left hB hx.le
      have hfac : x * ((x + 1) ^ 17 + 17 * (x + 1) ^ 16 + 136 * (x + 1) ^ 15)
          - (x + 3) * (x + 1) ^ 17 = (x + 1) ^ 15 * (14 * x ^ 2 + 147 * x - 3) := by ring
      have hpos : 0 < (x + 1) ^ 15 * (14 * x ^ 2 + 147 * x - 3) := by
        apply mul_pos (by positivity)
        nlinarith [hcon, mul_pos hx hx]
      linarith [h1, hfac, hpos]
    -- hence f 17 x < 1, contradicting f 17 x = 1
    have hfeq : f 17 x = (x + 3) * (x + 1) ^ 17 / (x * (x + 2) ^ 17) := by
      unfold f; rw [div_pow, div_mul_div_comm]
    have hlt : f 17 x < 1 := by
      rw [hfeq, div_lt_one (by positivity)]; exact key
    rw [hfx] at hlt
    exact absurd hlt (lt_irrefl 1)
  -- (B) monotonicity of g via its log.
  set L : ℝ → ℝ := fun t => 6 * Real.log (t + 3) + 34 * Real.log (t + 1) - 68 * Real.log (t + 2)
    with hLdef
  have hLderiv : ∀ t : ℝ, -1 < t →
      HasDerivAt L (6 / (t + 3) + 34 / (t + 1) - 68 / (t + 2)) t := by
    intro t ht
    have e3 : HasDerivAt (fun y : ℝ => Real.log (y + 3)) (1 / (t + 3)) t := by
      simpa using ((hasDerivAt_id t).add_const (3:ℝ)).log (ne_of_gt (by linarith : (0:ℝ) < t + 3))
    have e1 : HasDerivAt (fun y : ℝ => Real.log (y + 1)) (1 / (t + 1)) t := by
      simpa using ((hasDerivAt_id t).add_const (1:ℝ)).log (ne_of_gt (by linarith : (0:ℝ) < t + 1))
    have e2 : HasDerivAt (fun y : ℝ => Real.log (y + 2)) (1 / (t + 2)) t := by
      simpa using ((hasDerivAt_id t).add_const (2:ℝ)).log (ne_of_gt (by linarith : (0:ℝ) < t + 2))
    have hd := ((e3.const_mul 6).add (e1.const_mul 34)).sub (e2.const_mul 68)
    have heq : 6 * (1 / (t + 3)) + 34 * (1 / (t + 1)) - 68 * (1 / (t + 2))
        = 6 / (t + 3) + 34 / (t + 1) - 68 / (t + 2) := by ring
    rw [heq] at hd
    exact hd
  have hLcont : ContinuousOn L (Set.Icc (0:ℝ) (1 / 40)) := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    exact (hLderiv t (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hLmono : StrictMonoOn L (Set.Icc (0:ℝ) (1 / 40)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 / 40)) hLcont
    intro t ht
    rw [interior_Icc] at ht
    simp only [Set.mem_Ioo] at ht
    rw [(hLderiv t (by linarith [ht.1])).deriv]
    have h3 : (0:ℝ) < t + 3 := by linarith [ht.1]
    have h1 : (0:ℝ) < t + 1 := by linarith [ht.1]
    have h2 : (0:ℝ) < t + 2 := by linarith [ht.1]
    rw [div_add_div _ _ h3.ne' h1.ne', div_sub_div _ _ (mul_ne_zero h3.ne' h1.ne') h2.ne']
    apply div_pos
    · nlinarith [ht.1, ht.2, mul_pos ht.1 (sub_pos.mpr ht.2), sq_nonneg t]
    · positivity
  -- log g in terms of L
  have hlogg : ∀ t : ℝ, 0 < t → Real.log (g 17 t) = 6 * Real.log 2 + L t := by
    intro t ht
    have ht1 : (0:ℝ) < t + 1 := by linarith
    have ht2 : (0:ℝ) < t + 2 := by linarith
    have ht3 : (0:ℝ) < t + 3 := by linarith
    simp only [hLdef]
    unfold g
    rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  -- assemble
  have hxmem : x ∈ Set.Icc (0:ℝ) (1 / 40) := ⟨hx.le, hxb⟩
  have hbmem : (1 / 40 : ℝ) ∈ Set.Icc (0:ℝ) (1 / 40) := ⟨by norm_num, le_refl _⟩
  have hLle : L x ≤ L (1 / 40) := hLmono.monotoneOn hxmem hbmem hxb
  have hgx_pos : 0 < g 17 x := by unfold g; positivity
  have hgb_pos : 0 < g 17 (1 / 40) := by unfold g; positivity
  have hlogle : Real.log (g 17 x) ≤ Real.log (g 17 (1 / 40)) := by
    rw [hlogg x hx, hlogg (1 / 40) (by norm_num)]; linarith [hLle]
  have hgle : g 17 x ≤ g 17 (1 / 40) := by
    have h := Real.exp_le_exp.mpr hlogle
    rwa [Real.exp_log hgx_pos, Real.exp_log hgb_pos] at h
  have hbnd : (3:ℝ) ^ (33:ℕ) * g 17 (1 / 40) < 1 := by
    unfold g; norm_num
  calc (3:ℝ) ^ (33:ℕ) * g 17 x
      ≤ (3:ℝ) ^ (33:ℕ) * g 17 (1 / 40) :=
        mul_le_mul_of_nonneg_left hgle (by positivity)
    _ < 1 := hbnd

end Zeta5Odd
