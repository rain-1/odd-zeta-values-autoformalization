/-
Lemma 4, first claims: the nth-root limits for r and r̂.
Owner file — only `tendsto_root_r` and `tendsto_root_rhat` live here.
May use `sum_localizes` (imported, possibly still sorry'd) as an input.

Strategy (Worker C).  Work in logarithmic coordinates: it suffices to prove
`(1/n)·log (r n) → log (g x₀)`, then exponentiate (`r n ^ (1/n) = exp(log r / n)`).

* LOWER bound: `r n ≥ c q n (κ n)` for the peak proxy `κ n = ⌈x₀ n⌉`, so
  `(1/n) log r ≥ (1/n) log c q n (κ n) → log g x₀`.
* CORE analytic step (`tendsto_logRoot_peak`): for any `κ` with `κ n / n → x₀`,
  `(1/n) log (c q n (κ n)) → log g x₀`.  Proof: expand each factorial by
  Stirling (`m! = stirlingSeq m · √(2m) · (m/e)^m`); all `stirlingSeq`, `√`,
  and `log n` contributions die under `1/n`; the surviving `Σ coeff·α·log α`
  equals `log g x₀ + 2 x₀ log f x₀` and `f x₀ = 1`.
* UPPER bound (`logRoot_r_upper`): `r n` is dominated by a subexponential
  multiple of its peak term (localization), giving the matching upper limit.
-/
import Zeta5Odd.Basic
import Zeta5Odd.Localize
import Zeta5Odd.Ratio

open Filter Finset
open scoped Nat Topology

namespace Zeta5Odd

open Real Stirling

/-! ### Stirling logarithm expansion -/

/-- Exact Stirling expansion of `log (m!)` for `m ≥ 1`:
`log (m!) = log (stirlingSeq m) + ½ log (2m) + m log m − m`. -/
private lemma logFac (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m ! : ℝ)
      = Real.log (stirlingSeq m) + (1 / 2) * Real.log (2 * m) + (m : ℝ) * Real.log m - m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < stirlingSeq m :=
    lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos) (Stirling.sqrt_pi_le_stirlingSeq (by omega))
  have h1 : (0 : ℝ) < √(2 * (m : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have h2 : (0 : ℝ) < ((m : ℝ) / Real.exp 1) ^ m := by positivity
  have hD : √(2 * (m : ℝ)) * ((m : ℝ) / Real.exp 1) ^ m ≠ 0 := mul_ne_zero h1.ne' h2.ne'
  have hstir : (m ! : ℝ) = stirlingSeq m * (√(2 * (m : ℝ)) * ((m : ℝ) / Real.exp 1) ^ m) := by
    rw [Stirling.stirlingSeq]; exact (div_mul_cancel₀ _ hD).symm
  rw [hstir, Real.log_mul hs.ne' hD, Real.log_mul h1.ne' h2.ne',
      Real.log_sqrt (by positivity), Real.log_pow, Real.log_div hmR.ne' (Real.exp_ne_zero 1),
      Real.log_exp]
  ring

/-- Break `log (c q n k)` into six factorial-log contributions. -/
private lemma log_c_expand (q n k : ℕ) :
    Real.log (c q n k)
      = ((2 * q - 6 : ℕ) : ℝ) * Real.log (n ! : ℝ)
        + Real.log ((6 * n + 2 * k + 2)! : ℝ)
        + ((2 * q : ℕ) : ℝ) * Real.log ((n + k)! : ℝ)
        - Real.log 2
        - Real.log ((2 * k + 1)! : ℝ)
        - ((2 * q : ℕ) : ℝ) * Real.log ((2 * n + k + 1)! : ℝ) := by
  have p1 : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have p2 : (0 : ℝ) < ((6 * n + 2 * k + 2)! : ℝ) := by exact_mod_cast (6 * n + 2 * k + 2).factorial_pos
  have p3 : (0 : ℝ) < ((n + k)! : ℝ) := by exact_mod_cast (n + k).factorial_pos
  have p4 : (0 : ℝ) < ((2 * k + 1)! : ℝ) := by exact_mod_cast (2 * k + 1).factorial_pos
  have p5 : (0 : ℝ) < ((2 * n + k + 1)! : ℝ) := by exact_mod_cast (2 * n + k + 1).factorial_pos
  unfold c
  rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
  ring

/-! ### Single-factorial asymptotic -/

/-- `log n / n → 0`. -/
private lemma tendsto_logNat_div : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) := by
  have h := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards with n
  simp [Function.comp]

/-- The heart of the Stirling computation, isolated for one factorial argument.
If `a n / n → α > 0`, then after subtracting the divergent `a n · log n`, the
normalized log-factorial converges to `α log α − α`.  All Stirling, `√`, and
`log n` corrections vanish under `1/n`. -/
private lemma tendsto_facTerm (a : ℕ → ℕ) {α : ℝ} (hα : 0 < α)
    (ha : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 α)) :
    Tendsto (fun n : ℕ => (Real.log ((a n)! : ℝ) - (a n : ℝ) * Real.log n) / n)
      atTop (𝓝 (α * Real.log α - α)) := by
  have hpi : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  -- eventually `a n ≥ 1`
  have ha_ge1 : ∀ᶠ n : ℕ in atTop, 1 ≤ a n := by
    filter_upwards [ha.eventually_const_lt (show α / 2 < α by linarith), eventually_gt_atTop 0]
      with n hn hn0
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [lt_div_iff₀ hnR] at hn
    have hpos : (0 : ℝ) < (a n : ℝ) := by
      nlinarith [mul_pos (show (0 : ℝ) < α / 2 by linarith) hnR]
    exact_mod_cast hpos
  have ha_lt : ∀ᶠ n : ℕ in atTop, (a n : ℝ) / n < α + 1 :=
    ha.eventually_lt_const (show α < α + 1 by linarith)
  -- (i) stirlingSeq correction: bounded, so `/n → 0`
  have hi : Tendsto (fun n : ℕ => Real.log (stirlingSeq (a n)) / n) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log (√π)))
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log (√π) + 1 / 12)) ?_ ?_
    · filter_upwards [ha_ge1, eventually_gt_atTop 0] with n hn hn0
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      have hlo : Real.log (√π) ≤ Real.log (stirlingSeq (a n)) :=
        Real.log_le_log hpi (stirlingSeq_two_sided_rate (a n) hn).1
      exact (div_le_div_iff_of_pos_right hnR).mpr hlo
    · filter_upwards [ha_ge1, eventually_gt_atTop 0] with n hn hn0
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      have hanR : (1 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast hn
      have hup : Real.log (stirlingSeq (a n)) ≤ Real.log (√π) + 1 / 12 := by
        have h := log_stirlingSeq_sub_le (a n) hn
        have h12 : (1 : ℝ) / (12 * (a n : ℝ)) ≤ 1 / 12 :=
          one_div_le_one_div_of_le (by norm_num) (by nlinarith)
        linarith
      exact (div_le_div_iff_of_pos_right hnR).mpr hup
  -- (ii) half-log correction: `O(log n)/n → 0`
  have hU : Tendsto (fun n : ℕ =>
      (1 / 2) * (Real.log (2 * (α + 1)) / n + Real.log n / n)) atTop (𝓝 0) := by
    have h := (((tendsto_const_div_atTop_nhds_zero_nat (Real.log (2 * (α + 1)))).add
      tendsto_logNat_div).const_mul (1 / 2))
    simpa using h
  have hii : Tendsto (fun n : ℕ => (1 / 2) * Real.log (2 * a n) / n) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU ?_ ?_
    · filter_upwards [ha_ge1, eventually_gt_atTop 0] with n hn hn0
      have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have h1 : (1 : ℝ) ≤ 2 * (a n : ℝ) := by
        have : (1 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast hn
        linarith
      exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg h1)) hnR
    · filter_upwards [ha_ge1, ha_lt, eventually_gt_atTop 0] with n hn hlt hn0
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      have ha1 : (1 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast hn
      have hanpos : (0 : ℝ) < 2 * (a n : ℝ) := by linarith
      have han : (a n : ℝ) < (α + 1) * n := by rw [div_lt_iff₀ hnR] at hlt; linarith
      have hX : Real.log (2 * (a n : ℝ)) ≤ Real.log (2 * (α + 1)) + Real.log n := by
        calc Real.log (2 * (a n : ℝ)) ≤ Real.log (2 * ((α + 1) * n)) :=
              Real.log_le_log hanpos (by linarith)
          _ = Real.log (2 * (α + 1)) + Real.log n := by
              rw [show 2 * ((α + 1) * n) = 2 * (α + 1) * n by ring,
                Real.log_mul (by positivity) hnR.ne']
      have hcoef : (0 : ℝ) ≤ 1 / 2 / (n : ℝ) := by positivity
      calc (1 / 2) * Real.log (2 * (a n : ℝ)) / n
          = (1 / 2 / (n : ℝ)) * Real.log (2 * (a n : ℝ)) := by ring
        _ ≤ (1 / 2 / (n : ℝ)) * (Real.log (2 * (α + 1)) + Real.log n) :=
            mul_le_mul_of_nonneg_left hX hcoef
        _ = (1 / 2) * (Real.log (2 * (α + 1)) / n + Real.log n / n) := by ring
  -- (iii) main term via continuity of `t·log t`
  have hiii : Tendsto (fun n : ℕ => (a n : ℝ) / n * Real.log ((a n : ℝ) / n)) atTop
      (𝓝 (α * Real.log α)) := (Real.continuous_mul_log.tendsto α).comp ha
  -- combine
  have hcomb := (((hi.add hii).add hiii).sub ha)
  have hlim : (0 : ℝ) + 0 + α * Real.log α - α = α * Real.log α - α := by ring
  rw [hlim] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [ha_ge1, eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hanpos : (0 : ℝ) < (a n : ℝ) := by
    have : (1 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast hn
    linarith
  rw [logFac (a n) hn, Real.log_div hanpos.ne' hnR.ne']
  have hnz : (n : ℝ) ≠ 0 := hnR.ne'
  field_simp
  ring

/-- Ratio limit for an affine index `a n = A·n + B·κ n + C`. -/
private lemma tendsto_affine_ratio (κ : ℕ → ℕ) {x₀ : ℝ}
    (hκ : Tendsto (fun n : ℕ => (κ n : ℝ) / n) atTop (𝓝 x₀))
    (A B C : ℝ) (a : ℕ → ℕ) (hform : ∀ n, (a n : ℝ) = A * n + B * κ n + C) :
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (A + B * x₀)) := by
  have key : ∀ᶠ n : ℕ in atTop,
      A + B * ((κ n : ℝ) / n) + C * (1 / n) = (a n : ℝ) / n := by
    filter_upwards [eventually_gt_atTop 0] with n hn0
    have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
    rw [hform n]; field_simp
  have hlim : Tendsto (fun n : ℕ => A + B * ((κ n : ℝ) / n) + C * (1 / n)) atTop
      (𝓝 (A + B * x₀)) := by
    have h2 : Tendsto (fun n : ℕ => C * (1 / (n : ℝ))) atTop (𝓝 (C * 0)) :=
      (tendsto_one_div_atTop_nhds_zero_nat).const_mul C
    have h1 : Tendsto (fun _ : ℕ => A) atTop (𝓝 A) := tendsto_const_nhds
    have := (h1.add (hκ.const_mul B)).add h2
    simpa using this
  exact hlim.congr' key

/-! ### The core peak asymptotic -/

/-- CORE: for any index sequence with `κ n / n → x₀`, the normalized log of the
peak term converges to `log (g x₀)`.  This is the Stirling computation displayed
in the paper (proof of Lemma 4). -/
private lemma tendsto_logRoot_peak (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) (κ : ℕ → ℕ)
    (hκ : Tendsto (fun n : ℕ => (κ n : ℝ) / n) atTop (𝓝 x₀)) :
    Tendsto (fun n : ℕ => Real.log (c q n (κ n)) / n) atTop (𝓝 (Real.log (g q x₀))) := by
  -- clean ratio limits
  have hα1 : Tendsto (fun n : ℕ => ((n : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have h := tendsto_affine_ratio κ hκ 1 0 0 (fun n => n) (fun n => by push_cast; ring)
    rwa [show (1 : ℝ) + 0 * x₀ = 1 by ring] at h
  have hα2 : Tendsto (fun n : ℕ => ((6 * n + 2 * κ n + 2 : ℕ) : ℝ) / n) atTop (𝓝 (2 * (x₀ + 3))) := by
    have h := tendsto_affine_ratio κ hκ 6 2 2 (fun n => 6 * n + 2 * κ n + 2) (fun n => by push_cast; ring)
    rwa [show (6 : ℝ) + 2 * x₀ = 2 * (x₀ + 3) by ring] at h
  have hα3 : Tendsto (fun n : ℕ => ((n + κ n : ℕ) : ℝ) / n) atTop (𝓝 (x₀ + 1)) := by
    have h := tendsto_affine_ratio κ hκ 1 1 0 (fun n => n + κ n) (fun n => by push_cast; ring)
    rwa [show (1 : ℝ) + 1 * x₀ = x₀ + 1 by ring] at h
  have hα4 : Tendsto (fun n : ℕ => ((2 * κ n + 1 : ℕ) : ℝ) / n) atTop (𝓝 (2 * x₀)) := by
    have h := tendsto_affine_ratio κ hκ 0 2 1 (fun n => 2 * κ n + 1) (fun n => by push_cast; ring)
    rwa [show (0 : ℝ) + 2 * x₀ = 2 * x₀ by ring] at h
  have hα5 : Tendsto (fun n : ℕ => ((2 * n + κ n + 1 : ℕ) : ℝ) / n) atTop (𝓝 (x₀ + 2)) := by
    have h := tendsto_affine_ratio κ hκ 2 1 1 (fun n => 2 * n + κ n + 1) (fun n => by push_cast; ring)
    rwa [show (2 : ℝ) + 1 * x₀ = x₀ + 2 by ring] at h
  -- five factorial asymptotics
  have F1 := tendsto_facTerm (fun n => n) one_pos hα1
  have F2 := tendsto_facTerm (fun n => 6 * n + 2 * κ n + 2) (by linarith : (0 : ℝ) < 2 * (x₀ + 3)) hα2
  have F3 := tendsto_facTerm (fun n => n + κ n) (by linarith : (0 : ℝ) < x₀ + 1) hα3
  have F4 := tendsto_facTerm (fun n => 2 * κ n + 1) (by linarith : (0 : ℝ) < 2 * x₀) hα4
  have F5 := tendsto_facTerm (fun n => 2 * n + κ n + 1) (by linarith : (0 : ℝ) < x₀ + 2) hα5
  -- assemble the log(c)/n combination
  have base := ((((((F1.const_mul (2 * (q : ℝ) - 6)).add F2).add (F3.const_mul (2 * (q : ℝ)))).sub
    F4).sub (F5.const_mul (2 * (q : ℝ)))).add (tendsto_logNat_div.const_mul (1 - 2 * (q : ℝ)))).sub
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2))
  -- log identities at x₀
  have hx3 : (0 : ℝ) < x₀ + 3 := by linarith
  have hx1 : (0 : ℝ) < x₀ + 1 := by linarith
  have hx2 : (0 : ℝ) < x₀ + 2 := by linarith
  have hlogf : Real.log (x₀ + 3) - Real.log x₀ + (q : ℝ) * (Real.log (x₀ + 1) - Real.log (x₀ + 2))
      = 0 := by
    have h0 : Real.log (f q x₀) = 0 := by rw [hfx₀]; exact Real.log_one
    unfold f at h0
    rw [Real.log_mul (div_ne_zero hx3.ne' hx₀.ne') (pow_ne_zero q (div_ne_zero hx1.ne' hx2.ne')),
        Real.log_div hx3.ne' hx₀.ne', Real.log_pow, Real.log_div hx1.ne' hx2.ne'] at h0
    linear_combination h0
  have hnum : (0 : ℝ) < 2 ^ 6 * (x₀ + 3) ^ 6 * (x₀ + 1) ^ (2 * q) := by
    apply mul_pos (mul_pos (by positivity) (pow_pos hx3 6)) (pow_pos hx1 (2 * q))
  have hlogg : Real.log (g q x₀)
      = 6 * Real.log 2 + 6 * Real.log (x₀ + 3) + 2 * (q : ℝ) * Real.log (x₀ + 1)
        - 4 * (q : ℝ) * Real.log (x₀ + 2) := by
    unfold g
    rw [Real.log_div hnum.ne' (pow_pos hx2 (4 * q)).ne',
        Real.log_mul (mul_pos (by positivity) (pow_pos hx3 6)).ne' (pow_pos hx1 (2 * q)).ne',
        Real.log_mul (by positivity) (pow_pos hx3 6).ne',
        Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  -- the combination equals `log (c q n (κ n)) / n`, eventually
  have heq : (fun n : ℕ =>
      (2 * (q : ℝ) - 6) * ((Real.log ((n)! : ℝ) - (n : ℝ) * Real.log n) / n)
        + (Real.log ((6 * n + 2 * κ n + 2)! : ℝ)
            - ((6 * n + 2 * κ n + 2 : ℕ) : ℝ) * Real.log n) / n
        + 2 * (q : ℝ) * ((Real.log ((n + κ n)! : ℝ)
            - ((n + κ n : ℕ) : ℝ) * Real.log n) / n)
        - (Real.log ((2 * κ n + 1)! : ℝ) - ((2 * κ n + 1 : ℕ) : ℝ) * Real.log n) / n
        - 2 * (q : ℝ) * ((Real.log ((2 * n + κ n + 1)! : ℝ)
            - ((2 * n + κ n + 1 : ℕ) : ℝ) * Real.log n) / n)
        + (1 - 2 * (q : ℝ)) * (Real.log n / n)
        - Real.log 2 / n) =ᶠ[atTop] (fun n : ℕ => Real.log (c q n (κ n)) / n) := by
    filter_upwards [eventually_gt_atTop 0] with n hn0
    have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
    rw [log_c_expand]
    have e6 : ((2 * q - 6 : ℕ) : ℝ) = 2 * (q : ℝ) - 6 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have e2 : ((2 * q : ℕ) : ℝ) = 2 * (q : ℝ) := by push_cast; ring
    rw [e6, e2]
    field_simp
    push_cast
    ring
  have hbase := base.congr' heq
  -- identify the limit with log (g x₀)
  convert hbase using 2
  rw [hlogg, Real.log_one,
      show Real.log (2 * (x₀ + 3)) = Real.log 2 + Real.log (x₀ + 3) from
        Real.log_mul (by norm_num) hx3.ne',
      show Real.log (2 * x₀) = Real.log 2 + Real.log x₀ from
        Real.log_mul (by norm_num) hx₀.ne']
  linear_combination (-(2 * x₀)) * hlogf

/-! ### Peak index and lower bound -/

/-- The peak proxy `κ n = ⌈x₀ n⌉` has ratio `κ n / n → x₀`. -/
private lemma tendsto_ceil_div (x₀ : ℝ) (hx₀ : 0 < x₀) :
    Tendsto (fun n : ℕ => ((⌈x₀ * n⌉₊ : ℕ) : ℝ) / n) atTop (𝓝 x₀) := by
  have hup : Tendsto (fun n : ℕ => x₀ + 1 / (n : ℝ)) atTop (𝓝 x₀) := by
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.add h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hnR]; exact Nat.le_ceil _
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hnR]
    calc ((⌈x₀ * n⌉₊ : ℕ) : ℝ) ≤ x₀ * n + 1 :=
          (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ x₀ * n by positivity)).le
      _ = (x₀ + 1 / n) * n := by field_simp

/-- Telescoping upward: from `u (j+1) ≤ ρ · u j` (`b ≤ j < a`), `u a ≤ ρ^(a−b)·u b`. -/
private lemma geom_up {u : ℕ → ℝ} {ρ : ℝ} (hρ : 1 ≤ ρ) {b : ℕ} :
    ∀ a, b ≤ a → (∀ j, b ≤ j → j < a → u (j + 1) ≤ ρ * u j) → u a ≤ ρ ^ (a - b) * u b := by
  intro a hba
  induction a, hba using Nat.le_induction with
  | base => intro _; simp
  | succ a hba ih =>
    intro hstep
    have ih' := ih (fun j hj1 hj2 => hstep j hj1 (by omega))
    calc u (a + 1) ≤ ρ * u a := hstep a hba (by omega)
      _ ≤ ρ * (ρ ^ (a - b) * u b) := mul_le_mul_of_nonneg_left ih' (by linarith)
      _ = ρ ^ (a + 1 - b) * u b := by rw [← mul_assoc, ← pow_succ']; congr 2; omega

/-- Telescoping downward: from `u j ≤ ρ · u (j+1)` (`b ≤ j < a`), `u b ≤ ρ^(a−b)·u a`. -/
private lemma geom_down {u : ℕ → ℝ} {ρ : ℝ} (hρ : 1 ≤ ρ) {b : ℕ} :
    ∀ a, b ≤ a → (∀ j, b ≤ j → j < a → u j ≤ ρ * u (j + 1)) → u b ≤ ρ ^ (a - b) * u a := by
  intro a hba
  induction a, hba using Nat.le_induction with
  | base => intro _; simp
  | succ a hba ih =>
    intro hstep
    have ih' := ih (fun j hj1 hj2 => hstep j hj1 (by omega))
    calc u b ≤ ρ ^ (a - b) * u a := ih'
      _ ≤ ρ ^ (a - b) * (ρ * u (a + 1)) :=
          mul_le_mul_of_nonneg_left (hstep a hba (by omega)) (pow_nonneg (by linarith) _)
      _ = ρ ^ (a + 1 - b) * u (a + 1) := by rw [← mul_assoc, ← pow_succ]; congr 2; omega

/-- The exact term ratio `c_{k+1}/c_k` is uniformly within `δ` of `1` on a small
window `|k − x₀ n| ≤ ε n` (its limit profile is `f(x)² → f(x₀)² = 1`).  Mirrors
`Window.mainFactor_near_one`. -/
private lemma cratio_near_one (q : ℕ) {x₀ : ℝ} (hx₀ : 0 < x₀) (hfx₀ : f q x₀ = 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε, 0 < ε ∧ ε < x₀ ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ k : ℕ,
      (x₀ - ε) * n ≤ (k : ℝ) → (k : ℝ) ≤ (x₀ + ε) * n →
      |c q n (k + 1) / c q n k - 1| ≤ δ := by
  set prof : ℝ × ℝ → ℝ := fun p =>
    (6 + 2 * p.1 + 4 * p.2) * (6 + 2 * p.1 + 3 * p.2) / ((2 * p.1 + 3 * p.2) * (2 * p.1 + 2 * p.2))
      * ((1 + p.1 + p.2) / (2 + p.1 + 2 * p.2)) ^ (2 * q) with hprof
  have hval : prof (x₀, 0) = 1 := by
    have hf : (x₀ + 3) / x₀ * ((x₀ + 1) / (x₀ + 2)) ^ q = 1 := by rw [← f]; exact hfx₀
    rw [hprof]
    show (6 + 2 * x₀ + 4 * 0) * (6 + 2 * x₀ + 3 * 0) / ((2 * x₀ + 3 * 0) * (2 * x₀ + 2 * 0))
        * ((1 + x₀ + 0) / (2 + x₀ + 2 * 0)) ^ (2 * q) = 1
    have hx0 : x₀ ≠ 0 := hx₀.ne'
    have hexp : ((1 + x₀ + 0) / (2 + x₀ + 2 * 0)) ^ (2 * q)
        = (((x₀ + 1) / (x₀ + 2)) ^ q) ^ 2 := by
      rw [show (1 + x₀ + 0) / (2 + x₀ + 2 * 0) = (x₀ + 1) / (x₀ + 2) from by ring,
        show 2 * q = q * 2 from Nat.mul_comm 2 q, pow_mul]
    have hrat : (6 + 2 * x₀ + 4 * 0) * (6 + 2 * x₀ + 3 * 0) / ((2 * x₀ + 3 * 0) * (2 * x₀ + 2 * 0))
        = ((x₀ + 3) / x₀) ^ 2 := by
      rw [div_pow]; field_simp; ring
    rw [hexp, hrat, ← mul_pow, hf, one_pow]
  have hcont : ContinuousAt prof (x₀, 0) := by
    rw [hprof]
    have hnum1 : Continuous (fun p : ℝ × ℝ => (6 + 2 * p.1 + 4 * p.2) * (6 + 2 * p.1 + 3 * p.2)) := by
      fun_prop
    have hden1 : Continuous (fun p : ℝ × ℝ => (2 * p.1 + 3 * p.2) * (2 * p.1 + 2 * p.2)) := by
      fun_prop
    have hnum2 : Continuous (fun p : ℝ × ℝ => 1 + p.1 + p.2) := by fun_prop
    have hden2 : Continuous (fun p : ℝ × ℝ => 2 + p.1 + 2 * p.2) := by fun_prop
    exact (hnum1.continuousAt.div hden1.continuousAt
        (by show ((2 * x₀ + 3 * 0) * (2 * x₀ + 2 * 0) : ℝ) ≠ 0; positivity)).mul
      ((hnum2.continuousAt.div hden2.continuousAt
        (by show ((2 : ℝ) + x₀ + 2 * 0) ≠ 0; positivity)).pow (2 * q))
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨γ, hγ, hball⟩ := hcont δ hδ
  set ε : ℝ := min (x₀ / 2) (γ / 2) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hεlt : ε < x₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεγ : ε < γ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / ε)
  refine ⟨ε, hεpos, hεlt, max N 1, le_max_right _ _, ?_⟩
  intro n hn k hk1 hk2
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hNn : 1 / ε ≤ (n : ℝ) := le_trans hN (by exact_mod_cast le_trans (le_max_left N 1) hn)
  have h1n : 1 / (n : ℝ) ≤ ε := by
    rw [div_le_iff₀ hnpos]; have := (div_le_iff₀ hεpos).mp hNn; linarith
  have hx1 : x₀ - ε ≤ (k : ℝ) / n := (le_div_iff₀ hnpos).mpr hk1
  have hx2 : (k : ℝ) / n ≤ x₀ + ε := (div_le_iff₀ hnpos).mpr hk2
  have habs : |(k : ℝ) / n - x₀| ≤ ε := abs_le.mpr ⟨by linarith, by linarith⟩
  have hdle : dist ((k : ℝ) / n, 1 / (n : ℝ)) (x₀, (0 : ℝ)) ≤ ε := by
    rw [Prod.dist_eq]
    apply max_le
    · rw [Real.dist_eq]; exact habs
    · rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; exact h1n
  have hprofp := hball (lt_of_le_of_lt hdle hεγ)
  rw [hval, Real.dist_eq] at hprofp
  have hM0 : c q n (k + 1) / c q n k = prof ((k : ℝ) / n, 1 / (n : ℝ)) := by
    rw [c_ratio, hprof]
    show _ = (6 + 2 * ((k : ℝ) / n) + 4 * (1 / n)) * (6 + 2 * ((k : ℝ) / n) + 3 * (1 / n))
        / ((2 * ((k : ℝ) / n) + 3 * (1 / n)) * (2 * ((k : ℝ) / n) + 2 * (1 / n)))
        * ((1 + (k : ℝ) / n + 1 / n) / (2 + (k : ℝ) / n + 2 * (1 / n))) ^ (2 * q)
    have e1 : (6 * (n : ℝ) + 2 * k + 4) * (6 * (n : ℝ) + 2 * k + 3)
          / ((2 * (k : ℝ) + 3) * (2 * k + 2))
        = (6 + 2 * ((k : ℝ) / n) + 4 * (1 / n)) * (6 + 2 * ((k : ℝ) / n) + 3 * (1 / n))
          / ((2 * ((k : ℝ) / n) + 3 * (1 / n)) * (2 * ((k : ℝ) / n) + 2 * (1 / n))) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]; field_simp
    have e2 : (((n + k + 1 : ℕ) : ℝ) / ((2 * n + k + 2 : ℕ) : ℝ))
        = (1 + (k : ℝ) / n + 1 / n) / (2 + (k : ℝ) / n + 2 * (1 / n)) := by
      push_cast
      rw [div_eq_div_iff (by positivity) (by positivity)]; field_simp
    rw [e1, e2]
  rw [hM0]; exact le_of_lt hprofp

/-! ### Upper bound (localization)

REMAINING SUB-SORRY (analytic).  `logRoot_r_upper` is the only missing input to
`tendsto_logRoot_r`; the lower bound and the whole exp/squeeze wrapper are proven.

Intended proof (needs the concurrently-developed `sum_localizes` as a black box):
fix `ε>0` and choose `δ>0` with `H` continuous at `x₀` giving `H(x) ≤ H(x₀)+ε`
on `[x₀-δ,x₀+δ]`, where `H(x) = Σ coeffᵢ αᵢ(x) log αᵢ(x)` is the profile of
`tendsto_logRoot_peak` (`H(x₀) = log g x₀`).  Then:
  * `sum_localizes q hq hx₀ hfx₀ (ε:=δ)` ⇒ eventually `r n ≤ 2·∑_{window} c q n k`;
  * `∑_{window} c ≤ (2δn+2)·max_{window} c`, with `(2δn+2)` subexponential;
  * a *uniform-over-window* version of the `tendsto_facTerm` bound gives
    `(1/n) log (max_{window} c) ≤ H(x₀)+ε + o(1)`.
The last item (uniformity of the Stirling remainder over the window) is the real
content still to formalize; everything else is bookkeeping. -/
set_option maxHeartbeats 1000000 in
private lemma logRoot_r_upper (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, Real.log (r q n) / n ≤ Real.log (g q x₀) + ε := by
  intro s hs
  -- choose the ratio tolerance `δ` and the geometric base `ρ = 1/(1-δ)`
  set δ : ℝ := min (1 / 2) (s / (8 * x₀)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (by norm_num) (div_pos hs (by positivity))
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδs : δ ≤ s / (8 * x₀) := min_le_right _ _
  have hδs' : δ * (8 * x₀) ≤ s := (le_div_iff₀ (by positivity)).mp hδs
  have h1mδ : 0 < 1 - δ := by linarith
  set ρ : ℝ := 1 / (1 - δ) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact div_pos one_pos h1mδ
  have hρ1 : 1 ≤ ρ := by rw [hρdef, le_div_iff₀ h1mδ]; linarith
  have h1δρ : 1 + δ ≤ ρ := by rw [hρdef, le_div_iff₀ h1mδ]; nlinarith
  have hρle : ρ ≤ 1 + 2 * δ := by rw [hρdef, div_le_iff₀ h1mδ]; nlinarith
  have hlogρ : Real.log ρ ≤ 2 * δ := by
    have h := Real.log_le_sub_one_of_pos hρpos
    linarith
  have hlogρ0 : 0 ≤ Real.log ρ := Real.log_nonneg hρ1
  -- slack budget: `2ε·log ρ ≤ s/2`
  obtain ⟨ε, hεpos, hεx₀, N₁, hN₁1, hcr⟩ := cratio_near_one q hx₀ hfx₀ hδpos
  have hslack : 2 * ε * Real.log ρ ≤ s / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hlogρ hεpos.le,
      mul_le_mul_of_nonneg_right hεx₀.le hδpos.le, hδs']
  -- peak proxy and its asymptotic
  set κ : ℕ → ℕ := fun n => ⌈x₀ * n⌉₊ with hκdef
  have hcore : Tendsto (fun n : ℕ => Real.log (c q n (κ n)) / n) atTop (𝓝 (Real.log (g q x₀))) :=
    tendsto_logRoot_peak q hq hx₀ hfx₀ κ (tendsto_ceil_div x₀ hx₀)
  have hloc := sum_localizes q hq hx₀ hfx₀ hεpos
  -- `term1 → 0`
  have hterm1 : Tendsto
      (fun n : ℕ => (Real.log 2 + Real.log ((⌊(x₀ + ε) * (n : ℝ)⌋₊ : ℝ) + 1)) / n)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun n : ℕ => (Real.log 2 + Real.log (x₀ + ε + 1)) / n + Real.log n / n)
        atTop (𝓝 0) by
        have := (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2 + Real.log (x₀ + ε + 1))).add
          tendsto_logNat_div
        simpa using this) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn0
      have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hpos : (0 : ℝ) ≤ Real.log 2 + Real.log ((⌊(x₀ + ε) * (n : ℝ)⌋₊ : ℝ) + 1) := by
        have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have h3 : (0 : ℝ) ≤ Real.log ((⌊(x₀ + ε) * (n : ℝ)⌋₊ : ℝ) + 1) :=
          Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg _))
        linarith
      exact div_nonneg hpos hnR
    · filter_upwards [eventually_gt_atTop 0] with n hn0
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
      have hbound : ((⌊(x₀ + ε) * (n : ℝ)⌋₊ : ℝ) + 1) ≤ (x₀ + ε + 1) * n := by
        have hf := Nat.floor_le (show (0 : ℝ) ≤ (x₀ + ε) * n by positivity)
        nlinarith
      have hlog : Real.log ((⌊(x₀ + ε) * (n : ℝ)⌋₊ : ℝ) + 1)
          ≤ Real.log (x₀ + ε + 1) + Real.log n := by
        calc Real.log ((⌊(x₀ + ε) * (n : ℝ)⌋₊ : ℝ) + 1)
            ≤ Real.log ((x₀ + ε + 1) * n) := Real.log_le_log (by positivity) hbound
          _ = Real.log (x₀ + ε + 1) + Real.log n := Real.log_mul (by positivity) hnR.ne'
      rw [← add_div, div_le_div_iff_of_pos_right hnR]
      linarith
  -- everything eventual
  have hev1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ε * (n : ℝ) :=
    (Filter.Tendsto.const_mul_atTop hεpos (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [hloc.eventually (Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0:ℝ) < 1/2)),
      eventually_ge_atTop N₁, eventually_ge_atTop 1, hev1,
      hcore.eventually_lt_const (show Real.log (g q x₀) < Real.log (g q x₀) + s / 4 by linarith),
      hterm1.eventually_lt_const (show (0 : ℝ) < s / 4 by linarith)]
    with n hntail hnN₁ hn1 hn1ε hterm3 hterm1n
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  -- κ n lies in the window
  have hκlo : (x₀ - ε) * n ≤ (κ n : ℝ) := by
    simp only [hκdef]
    have hc := Nat.le_ceil (x₀ * (n : ℝ))
    nlinarith [hc, mul_nonneg hεpos.le hnpos.le]
  have hκhi : (κ n : ℝ) ≤ (x₀ + ε) * n := by
    simp only [hκdef]
    have h := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ x₀ * n by positivity)).le
    nlinarith [h, hn1ε]
  -- the per-window-term bound  c k ≤ ρ^⌊2εn⌋ · c (κ n)
  set B : ℝ := ρ ^ (⌊2 * ε * (n : ℝ)⌋₊) * c q n (κ n) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]; exact mul_nonneg (pow_nonneg hρpos.le _) (c_pos q n (κ n)).le
  -- ratio steps on the window
  have hstepU : ∀ j : ℕ, (x₀ - ε) * n ≤ (j : ℝ) → (j : ℝ) ≤ (x₀ + ε) * n →
      c q n (j + 1) ≤ ρ * c q n j := by
    intro j hj1 hj2
    have hb := hcr n hnN₁ j hj1 hj2
    have hcp := c_pos q n j
    have hle : c q n (j + 1) / c q n j ≤ 1 + δ := by have := (abs_le.mp hb).2; linarith
    have : c q n (j + 1) ≤ (1 + δ) * c q n j := (div_le_iff₀ hcp).mp hle
    nlinarith [this, mul_le_mul_of_nonneg_right h1δρ hcp.le]
  have hstepD : ∀ j : ℕ, (x₀ - ε) * n ≤ (j : ℝ) → (j : ℝ) ≤ (x₀ + ε) * n →
      c q n j ≤ ρ * c q n (j + 1) := by
    intro j hj1 hj2
    have hb := hcr n hnN₁ j hj1 hj2
    have hcj := c_pos q n j
    have hge : 1 - δ ≤ c q n (j + 1) / c q n j := by have := (abs_le.mp hb).1; linarith
    rw [le_div_iff₀ hcj] at hge
    rw [hρdef, one_div, inv_mul_eq_div, le_div_iff₀ h1mδ]
    nlinarith [hge]
  have hterm : ∀ k : ℕ, (x₀ - ε) * n ≤ (k : ℝ) → (k : ℝ) ≤ (x₀ + ε) * n → c q n k ≤ B := by
    intro k hk1 hk2
    rw [hBdef]
    rcases Nat.lt_or_ge k (κ n) with hkκ | hkκ
    · -- k < κ n : telescope down
      have hkκ' : k ≤ κ n := le_of_lt hkκ
      have hstep : ∀ j, k ≤ j → j < κ n → c q n j ≤ ρ * c q n (j + 1) := by
        intro j hj1 hj2
        refine hstepD j (le_trans hk1 (by exact_mod_cast hj1)) ?_
        calc (j : ℝ) ≤ (κ n : ℝ) := by exact_mod_cast hj2.le
          _ ≤ (x₀ + ε) * n := hκhi
      have hdn := geom_down (u := c q n) hρ1 (b := k) (κ n) hkκ' hstep
      have hexp : κ n - k ≤ ⌊2 * ε * (n : ℝ)⌋₊ := by
        apply Nat.le_floor
        rw [Nat.cast_sub hkκ']
        calc (κ n : ℝ) - (k : ℝ) ≤ (x₀ + ε) * n - (x₀ - ε) * n := by linarith
          _ = 2 * ε * n := by ring
      calc c q n k ≤ ρ ^ (κ n - k) * c q n (κ n) := hdn
        _ ≤ ρ ^ (⌊2 * ε * (n : ℝ)⌋₊) * c q n (κ n) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hρ1 hexp) (c_pos q n (κ n)).le
    · -- κ n ≤ k : telescope up
      have hstep : ∀ j, κ n ≤ j → j < k → c q n (j + 1) ≤ ρ * c q n j := by
        intro j hj1 hj2
        refine hstepU j (le_trans hκlo (by exact_mod_cast hj1)) ?_
        calc (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj2.le
          _ ≤ (x₀ + ε) * n := hk2
      have hup := geom_up (u := c q n) hρ1 (b := κ n) k hkκ hstep
      have hexp : k - κ n ≤ ⌊2 * ε * (n : ℝ)⌋₊ := by
        apply Nat.le_floor
        rw [Nat.cast_sub hkκ]
        calc (k : ℝ) - (κ n : ℝ) ≤ (x₀ + ε) * n - (x₀ - ε) * n := by linarith
          _ = 2 * ε * n := by ring
      calc c q n k ≤ ρ ^ (k - κ n) * c q n (κ n) := hup
        _ ≤ ρ ^ (⌊2 * ε * (n : ℝ)⌋₊) * c q n (κ n) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hρ1 hexp) (c_pos q n (κ n)).le
  -- window/tail decomposition
  set outsideSet : Set ℕ := {k : ℕ | (k : ℝ) < (x₀ - ε) * ↑n ∨ (x₀ + ε) * ↑n < (k : ℝ)} with hout
  have hrp := r_pos q n hq
  have hdecomp : (∑' i : ↥outsideSet, c q n ↑i) + (∑' i : ↥outsideSetᶜ, c q n ↑i) = r q n :=
    (summable_c q n hq).tsum_subtype_add_tsum_subtype_compl outsideSet
  -- tail ≤ r/2
  have htail : (∑' i : ↥outsideSet, c q n ↑i) ≤ (1 / 2) * r q n := by
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hntail
    have := (abs_le.mp hntail).2
    exact (div_le_iff₀ hrp).mp this
  -- window ≤ (⌊(x₀+ε)n⌋+1)·B
  set Mfl : ℕ := ⌊(x₀ + ε) * (n : ℝ)⌋₊ with hMfl
  have hwin_le : (∑' i : ↥outsideSetᶜ, c q n ↑i) ≤ ((Mfl : ℝ) + 1) * B := by
    have hsupp : ∀ k ∉ Finset.range (Mfl + 1), outsideSetᶜ.indicator (c q n) k = 0 := by
      intro k hk
      rw [Set.indicator_of_notMem]
      intro hmem
      simp only [hout, Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_lt] at hmem
      have : k ≤ Mfl := Nat.le_floor hmem.2
      simp only [Finset.mem_range] at hk; omega
    rw [tsum_subtype outsideSetᶜ (c q n), tsum_eq_sum hsupp]
    calc ∑ k ∈ Finset.range (Mfl + 1), outsideSetᶜ.indicator (c q n) k
        ≤ ∑ _k ∈ Finset.range (Mfl + 1), B := by
          apply Finset.sum_le_sum
          intro k _
          by_cases hk : k ∈ outsideSetᶜ
          · rw [Set.indicator_of_mem hk]
            simp only [hout, Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_lt] at hk
            exact hterm k hk.1 hk.2
          · rw [Set.indicator_of_notMem hk]; exact hBnn
      _ = ((Mfl : ℝ) + 1) * B := by rw [Finset.sum_const, Finset.card_range]; push_cast; ring
  -- r ≤ 2·(Mfl+1)·B
  have hrB : r q n ≤ 2 * (((Mfl : ℝ) + 1) * B) := by
    have hwinlo : r q n / 2 ≤ ∑' i : ↥outsideSetᶜ, c q n ↑i := by linarith [hdecomp, htail]
    linarith [hwin_le, hwinlo]
  -- take logs
  have hcκpos := c_pos q n (κ n)
  have hBpos : 0 < B := by
    rw [hBdef]; exact mul_pos (pow_pos hρpos _) hcκpos
  have hMp : (0 : ℝ) < (Mfl : ℝ) + 1 := by positivity
  have hnz : (n : ℝ) ≠ 0 := hnpos.ne'
  have hlogr : Real.log (r q n) ≤ Real.log 2 + Real.log ((Mfl : ℝ) + 1)
      + (⌊2 * ε * (n : ℝ)⌋₊ : ℝ) * Real.log ρ + Real.log (c q n (κ n)) := by
    have h := Real.log_le_log hrp hrB
    rw [show 2 * (((Mfl : ℝ) + 1) * B) = 2 * ((Mfl : ℝ) + 1) * B by ring,
        Real.log_mul (by positivity) hBpos.ne', Real.log_mul (by norm_num) hMp.ne',
        hBdef, Real.log_mul (pow_pos hρpos _).ne' hcκpos.ne', Real.log_pow] at h
    linarith
  -- assemble the three pieces
  have hterm2 : (⌊2 * ε * (n : ℝ)⌋₊ : ℝ) / n * Real.log ρ ≤ s / 2 := by
    have hfloor : (⌊2 * ε * (n : ℝ)⌋₊ : ℝ) ≤ 2 * ε * n := Nat.floor_le (by positivity)
    have hle : (⌊2 * ε * (n : ℝ)⌋₊ : ℝ) / n ≤ 2 * ε := by
      rw [div_le_iff₀ hnpos]; nlinarith
    calc (⌊2 * ε * (n : ℝ)⌋₊ : ℝ) / n * Real.log ρ ≤ 2 * ε * Real.log ρ :=
          mul_le_mul_of_nonneg_right hle hlogρ0
      _ ≤ s / 2 := hslack
  have hkey : Real.log (r q n) / n
      ≤ (Real.log 2 + Real.log ((Mfl : ℝ) + 1)) / n
        + (⌊2 * ε * (n : ℝ)⌋₊ : ℝ) / n * Real.log ρ + Real.log (c q n (κ n)) / n := by
    have hE : (Real.log 2 + Real.log ((Mfl : ℝ) + 1)) / n
          + (⌊2 * ε * (n : ℝ)⌋₊ : ℝ) / n * Real.log ρ + Real.log (c q n (κ n)) / n
        = (Real.log 2 + Real.log ((Mfl : ℝ) + 1) + (⌊2 * ε * (n : ℝ)⌋₊ : ℝ) * Real.log ρ
            + Real.log (c q n (κ n))) / n := by field_simp
    rw [hE, div_le_div_iff_of_pos_right hnpos]
    exact hlogr
  linarith [hkey, hterm2, hterm3, hterm1n]

/-! ### Assembling the log-limit for `r` -/

private lemma tendsto_logRoot_r (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    Tendsto (fun n : ℕ => Real.log (r q n) / n) atTop (𝓝 (Real.log (g q x₀))) := by
  set κ : ℕ → ℕ := fun n => ⌈x₀ * n⌉₊ with hκdef
  have hcore : Tendsto (fun n : ℕ => Real.log (c q n (κ n)) / n) atTop (𝓝 (Real.log (g q x₀))) :=
    tendsto_logRoot_peak q hq hx₀ hfx₀ κ (tendsto_ceil_div x₀ hx₀)
  -- lower inequality (all `n`): `log (c (κ n)) / n ≤ log (r n) / n`
  have hlow : ∀ n : ℕ, Real.log (c q n (κ n)) / n ≤ Real.log (r q n) / n := by
    intro n
    have hle : c q n (κ n) ≤ r q n :=
      Summable.le_tsum (summable_c q n hq) (κ n) (fun j _ => (c_pos q n j).le)
    have hlog : Real.log (c q n (κ n)) ≤ Real.log (r q n) := Real.log_le_log (c_pos q n (κ n)) hle
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      exact (div_le_div_iff_of_pos_right hnR).mpr hlog
  refine tendsto_order.mpr ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- from below: `a < log g x₀` gives eventually `a < log r / n`
    filter_upwards [(tendsto_order.mp hcore).1 a ha] with n hn
    exact lt_of_lt_of_le hn (hlow n)
  · -- from above: `b > log g x₀` gives eventually `log r / n < b`
    have hε : (0 : ℝ) < (b - Real.log (g q x₀)) / 2 := by linarith
    filter_upwards [logRoot_r_upper q hq hx₀ hfx₀ _ hε] with n hn
    linarith

/-! ### Final theorems -/

/-- Reduce `u n ^ (1/n) → L` to `(1/n) log (u n) → log L`. -/
private lemma tendsto_root_of_logRoot {L : ℝ} (hL : 0 < L) (u : ℕ → ℝ) (hu : ∀ n, 0 < u n)
    (h : Tendsto (fun n : ℕ => Real.log (u n) / n) atTop (𝓝 (Real.log L))) :
    Tendsto (fun n : ℕ => u n ^ (1 / (n : ℝ))) atTop (𝓝 L) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (Real.log (u n) / n)) atTop (𝓝 L) := by
    have := (Real.continuous_exp.tendsto _).comp h
    rwa [Real.exp_log hL] at this
  have heq : (fun n : ℕ => u n ^ (1 / (n : ℝ))) = fun n : ℕ => Real.exp (Real.log (u n) / n) := by
    funext n
    rw [Real.rpow_def_of_pos (hu n)]
    congr 1
    ring
  rw [heq]; exact hexp

/-- Lemma 4, first claim for `r`. -/
theorem tendsto_root_r (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    Tendsto (fun n : ℕ => r q n ^ (1 / (n : ℝ))) atTop (𝓝 (g q x₀)) := by
  have hg : 0 < g q x₀ := by unfold g; positivity
  exact tendsto_root_of_logRoot hg (fun n => r q n) (fun n => r_pos q n hq)
    (tendsto_logRoot_r q hq hx₀ hfx₀)

/-- The `r̂` analogue of `tendsto_logRoot_r`, obtained from the `r`-limit and the
proven ratio limit `r n / r̂ n → 1` (`Zeta5Odd.tendsto_ratio`):
`(1/n) log r̂ = (1/n) log r − (1/n) log (r/r̂)`, and `log (r/r̂) → 0` kills the
second term under the `1/n`. -/
private lemma tendsto_logRoot_rhat (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    Tendsto (fun n : ℕ => Real.log (rhat q n) / n) atTop (𝓝 (Real.log (g q x₀))) := by
  have hr := tendsto_logRoot_r q hq hx₀ hfx₀
  have hratio := tendsto_ratio q hq hx₀ hfx₀
  -- `log (r/r̂) → log 1 = 0`
  have hlogratio : Tendsto (fun n : ℕ => Real.log (r q n / rhat q n)) atTop (𝓝 0) := by
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
    rwa [Real.log_one] at this
  -- `(1/n) log (r/r̂) → 0`
  have hdiv : Tendsto (fun n : ℕ => Real.log (r q n / rhat q n) / n) atTop (𝓝 0) :=
    hlogratio.div_atTop tendsto_natCast_atTop_atTop
  have heq : ∀ᶠ n : ℕ in atTop,
      Real.log (r q n) / n - Real.log (r q n / rhat q n) / n = Real.log (rhat q n) / n := by
    filter_upwards with n
    rw [Real.log_div (r_pos q n hq).ne' (rhat_pos q n hq).ne']
    ring
  simpa using (hr.sub hdiv).congr' heq

/-- Lemma 4, first claim for `r̂`. -/
theorem tendsto_root_rhat (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    Tendsto (fun n : ℕ => rhat q n ^ (1 / (n : ℝ))) atTop (𝓝 (g q x₀)) := by
  have hg : 0 < g q x₀ := by unfold g; positivity
  exact tendsto_root_of_logRoot hg (fun n => rhat q n) (fun n => rhat_pos q n hq)
    (tendsto_logRoot_rhat q hq hx₀ hfx₀)

end Zeta5Odd
