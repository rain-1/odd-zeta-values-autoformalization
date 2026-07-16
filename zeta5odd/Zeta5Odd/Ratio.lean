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

/-- Pure ε/δ bookkeeping: given the window/tail decomposition of two positive
sums together with the localization bounds (tails ≤ δ₀·total) and the termwise
window comparison ((1−δ₀)·B̂ ≤ B ≤ (1+δ₀)·B̂), the ratio of totals is within δ
of 1, provided δ₀ = δ/3 and 0 < δ < 1.  This isolates all the algebra so the
main assembly only has to produce the hypotheses. -/
private lemma ratio_close {A B Ah Bh r rh δ δ₀ : ℝ}
    (hδ0 : δ₀ = δ / 3) (hδpos : 0 < δ) (hδ1 : δ < 1)
    (hA0 : 0 ≤ A) (hAh0 : 0 ≤ Ah)
    (hAle : A ≤ δ₀ * r) (hAhle : Ah ≤ δ₀ * rh)
    (hBle : B ≤ (1 + δ₀) * Bh) (hBge : (1 - δ₀) * Bh ≤ B)
    (hcAB : A + B = r) (hcABh : Ah + Bh = rh)
    (_hr : 0 < r) (hrh : 0 < rh) :
    |r / rh - 1| ≤ δ := by
  subst hδ0
  have hBh_lo : (1 - δ / 3) * rh ≤ Bh := by nlinarith [hcABh, hAhle]
  have hBh_hi : Bh ≤ rh := by nlinarith [hcABh, hAh0]
  have hupper : (1 - δ / 3) * r ≤ (1 + δ / 3) * rh := by
    nlinarith [hcAB, hAle, hBle, hBh_hi,
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 + δ / 3) (by linarith [hBh_hi] : (0:ℝ) ≤ rh - Bh)]
  have hlower : (1 - δ / 3) * ((1 - δ / 3) * rh) ≤ r := by
    nlinarith [hcAB, hA0, hBge,
      mul_le_mul_of_nonneg_left hBh_lo (by linarith : (0:ℝ) ≤ 1 - δ / 3)]
  have hub : r ≤ (1 + δ) * rh := by
    nlinarith [hupper, hrh, hδpos, hδ1,
      mul_nonneg (mul_nonneg hδpos.le (by linarith : (0:ℝ) ≤ 1 - δ)) hrh.le]
  have hlb : (1 - δ) * rh ≤ r := by
    nlinarith [hlower, hrh, hδpos, hδ1,
      mul_nonneg (mul_nonneg hδpos.le hδpos.le) hrh.le,
      mul_nonneg hδpos.le hrh.le]
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h := (le_div_iff₀ hrh).mpr hlb
    linarith
  · have h := (div_le_iff₀ hrh).mpr hub
    linarith

/-- Lemma 4, second claim: the two linear forms are asymptotically equal.
This is what makes `7 r_n - r̂_n > 0` eventually, hence nonvanishing. -/
theorem tendsto_ratio (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    Tendsto (fun n : ℕ => r q n / rhat q n) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ξ hξ
  -- target tolerance δ = min(ξ/2, 1/2) ∈ (0,1); split budget δ₀ = δ/3.
  set δ : ℝ := min (ξ / 2) (1 / 2) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) (by norm_num)
  have hδlt1 : δ < 1 := by
    rw [hδdef]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδ_le : δ ≤ ξ / 2 := by rw [hδdef]; exact min_le_left _ _
  set δ₀ : ℝ := δ / 3 with hδ0def
  have hδ0pos : 0 < δ₀ := by rw [hδ0def]; linarith
  -- window ratio input
  obtain ⟨ε, hεpos, hwin⟩ := term_ratio_on_window q hq hx₀ hfx₀ hδ0pos
  -- localization inputs
  have hloc := sum_localizes q hq hx₀ hfx₀ hεpos
  have hlochat := sum_localizes_chat q hq hx₀ hfx₀ hεpos
  -- turn the two localization limits into eventual |tail/total| ≤ δ₀
  have E2 : ∀ᶠ n : ℕ in atTop,
      |(∑' k : {k : ℕ // (k : ℝ) < (x₀ - ε) * ↑n ∨ (x₀ + ε) * ↑n < (k : ℝ)},
          c q n ↑k) / r q n| ≤ δ₀ := by
    filter_upwards [hloc.eventually (Metric.closedBall_mem_nhds (0 : ℝ) hδ0pos)] with n hn
    simp only [Real.dist_eq, sub_zero] at hn
    exact hn
  have E3 : ∀ᶠ n : ℕ in atTop,
      |(∑' k : {k : ℕ // (k : ℝ) < (x₀ - ε) * ↑n ∨ (x₀ + ε) * ↑n < (k : ℝ)},
          chat q n ↑k) / rhat q n| ≤ δ₀ := by
    filter_upwards [hlochat.eventually (Metric.closedBall_mem_nhds (0 : ℝ) hδ0pos)] with n hn
    simp only [Real.dist_eq, sub_zero] at hn
    exact hn
  -- the eventual conclusion |r/rhat − 1| ≤ δ
  have hfinal : ∀ᶠ n : ℕ in atTop, |r q n / rhat q n - 1| ≤ δ := by
    filter_upwards [hwin, E2, E3] with n hwin_n hn2 hn3
    -- window comparison, termwise, on the complement (window) set
    have htermU : ∀ i : ↥({k : ℕ | (k : ℝ) < (x₀ - ε) * ↑n ∨ (x₀ + ε) * ↑n < (k : ℝ)}ᶜ),
        c q n ↑i ≤ (1 + δ₀) * chat q n ↑i := by
      rintro ⟨k, hk⟩
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_lt] at hk
      obtain ⟨h1, h2⟩ := hk
      have hb := hwin_n k h1 h2
      have hcp := chat_pos q n k
      have h3 : c q n k / chat q n k ≤ 1 + δ₀ := by
        have := (abs_le.mp hb).2; linarith
      exact (div_le_iff₀ hcp).mp h3
    have htermL : ∀ i : ↥({k : ℕ | (k : ℝ) < (x₀ - ε) * ↑n ∨ (x₀ + ε) * ↑n < (k : ℝ)}ᶜ),
        (1 - δ₀) * chat q n ↑i ≤ c q n ↑i := by
      rintro ⟨k, hk⟩
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_lt] at hk
      obtain ⟨h1, h2⟩ := hk
      have hb := hwin_n k h1 h2
      have hcp := chat_pos q n k
      have h3 : 1 - δ₀ ≤ c q n k / chat q n k := by
        have := (abs_le.mp hb).1; linarith
      exact (le_div_iff₀ hcp).mp h3
    -- window sum comparison
    have hBle : (∑' i : ↥({k : ℕ | (k : ℝ) < (x₀ - ε) * ↑n ∨ (x₀ + ε) * ↑n < (k : ℝ)}ᶜ),
          c q n ↑i)
        ≤ (1 + δ₀) * ∑' i : ↥({k : ℕ | (k : ℝ) < (x₀ - ε) * ↑n ∨ (x₀ + ε) * ↑n < (k : ℝ)}ᶜ),
          chat q n ↑i := by
      have hle := Summable.tsum_le_tsum htermU ((summable_c q n hq).subtype _)
        (((summable_chat q n hq).subtype _).mul_left (1 + δ₀))
      rwa [tsum_mul_left] at hle
    have hBge : (1 - δ₀) * ∑' i : ↥({k : ℕ | (k : ℝ) < (x₀ - ε) * ↑n ∨ (x₀ + ε) * ↑n < (k : ℝ)}ᶜ),
          chat q n ↑i
        ≤ ∑' i : ↥({k : ℕ | (k : ℝ) < (x₀ - ε) * ↑n ∨ (x₀ + ε) * ↑n < (k : ℝ)}ᶜ),
          c q n ↑i := by
      have hle := Summable.tsum_le_tsum htermL
        (((summable_chat q n hq).subtype _).mul_left (1 - δ₀)) ((summable_c q n hq).subtype _)
      rwa [tsum_mul_left] at hle
    -- window/tail decomposition of both totals
    have hcAB := (summable_c q n hq).tsum_subtype_add_tsum_subtype_compl
      {k : ℕ | (k : ℝ) < (x₀ - ε) * ↑n ∨ (x₀ + ε) * ↑n < (k : ℝ)}
    have hcABh := (summable_chat q n hq).tsum_subtype_add_tsum_subtype_compl
      {k : ℕ | (k : ℝ) < (x₀ - ε) * ↑n ∨ (x₀ + ε) * ↑n < (k : ℝ)}
    -- nonnegativity of the tails and positivity of the totals
    have hA0 : 0 ≤ ∑' i : ↥({k : ℕ | (k : ℝ) < (x₀ - ε) * ↑n ∨ (x₀ + ε) * ↑n < (k : ℝ)}),
        c q n ↑i := tsum_nonneg (fun i => (c_pos q n ↑i).le)
    have hAh0 : 0 ≤ ∑' i : ↥({k : ℕ | (k : ℝ) < (x₀ - ε) * ↑n ∨ (x₀ + ε) * ↑n < (k : ℝ)}),
        chat q n ↑i := tsum_nonneg (fun i => (chat_pos q n ↑i).le)
    have hr_pos : 0 < r q n := r_pos q n hq
    have hrhat_pos : 0 < rhat q n := rhat_pos q n hq
    have hAle : (∑' i : ↥({k : ℕ | (k : ℝ) < (x₀ - ε) * ↑n ∨ (x₀ + ε) * ↑n < (k : ℝ)}),
        c q n ↑i) ≤ δ₀ * r q n := (div_le_iff₀ hr_pos).mp (abs_le.mp hn2).2
    have hAhle : (∑' i : ↥({k : ℕ | (k : ℝ) < (x₀ - ε) * ↑n ∨ (x₀ + ε) * ↑n < (k : ℝ)}),
        chat q n ↑i) ≤ δ₀ * rhat q n := (div_le_iff₀ hrhat_pos).mp (abs_le.mp hn3).2
    exact ratio_close hδ0def hδpos hδlt1 hA0 hAh0 hAle hAhle hBle hBge hcAB hcABh hr_pos hrhat_pos
  -- extract N and finish against the metric characterisation
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfinal
  refine ⟨N, fun n hn => ?_⟩
  show dist (r q n / rhat q n) 1 < ξ
  rw [Real.dist_eq]
  have := hN n hn
  linarith

/-- Bonus (Lemma 4 nonvanishing corollary shape): from `r_n / r̂_n → 1 < 7`,
eventually `7 r_n − r̂_n > 0`. -/
lemma seven_r_sub_rhat_pos_eventually (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ}
    (hx₀ : 0 < x₀) (hfx₀ : f q x₀ = 1) :
    ∀ᶠ n : ℕ in atTop, 0 < 7 * r q n - rhat q n := by
  have h := tendsto_ratio q hq hx₀ hfx₀
  have hev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / 7 < r q n / rhat q n :=
    h.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) / 7 < 1))
  filter_upwards [hev] with n hn
  have hrh := rhat_pos q n hq
  rw [lt_div_iff₀ hrh] at hn
  linarith

end Zeta5Odd
