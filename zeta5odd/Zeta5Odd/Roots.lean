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
private lemma tendsto_ratio (κ : ℕ → ℕ) {x₀ : ℝ}
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
    have h := tendsto_ratio κ hκ 1 0 0 (fun n => n) (fun n => by push_cast; ring)
    rwa [show (1 : ℝ) + 0 * x₀ = 1 by ring] at h
  have hα2 : Tendsto (fun n : ℕ => ((6 * n + 2 * κ n + 2 : ℕ) : ℝ) / n) atTop (𝓝 (2 * (x₀ + 3))) := by
    have h := tendsto_ratio κ hκ 6 2 2 (fun n => 6 * n + 2 * κ n + 2) (fun n => by push_cast; ring)
    rwa [show (6 : ℝ) + 2 * x₀ = 2 * (x₀ + 3) by ring] at h
  have hα3 : Tendsto (fun n : ℕ => ((n + κ n : ℕ) : ℝ) / n) atTop (𝓝 (x₀ + 1)) := by
    have h := tendsto_ratio κ hκ 1 1 0 (fun n => n + κ n) (fun n => by push_cast; ring)
    rwa [show (1 : ℝ) + 1 * x₀ = x₀ + 1 by ring] at h
  have hα4 : Tendsto (fun n : ℕ => ((2 * κ n + 1 : ℕ) : ℝ) / n) atTop (𝓝 (2 * x₀)) := by
    have h := tendsto_ratio κ hκ 0 2 1 (fun n => 2 * κ n + 1) (fun n => by push_cast; ring)
    rwa [show (0 : ℝ) + 2 * x₀ = 2 * x₀ by ring] at h
  have hα5 : Tendsto (fun n : ℕ => ((2 * n + κ n + 1 : ℕ) : ℝ) / n) atTop (𝓝 (x₀ + 2)) := by
    have h := tendsto_ratio κ hκ 2 1 1 (fun n => 2 * n + κ n + 1) (fun n => by push_cast; ring)
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
private lemma logRoot_r_upper (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, Real.log (r q n) / n ≤ Real.log (g q x₀) + ε := by
  sorry

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

/-- The `r̂` analogue of `tendsto_logRoot_r`.

REMAINING SUB-SORRY (analytic).  Same skeleton as `tendsto_logRoot_r`: a lower
bound from the peak term `ĉ_{κ n}` and an upper bound from `sum_localizes_chat`.
The `ĉ` peak asymptotic reduces to `tendsto_facTerm` after writing the odd-index
product of `chat` (Basic.lean) as factorials and powers of `2`, OR is transferred
from the `c` peak via the two-sided subexponential ratio bound `c/ĉ` (paper (e10),
`centralBinom_two_sided`), which is constant-factor and hence invisible under the
`1/n` root.  Its limit is again `log g x₀` because `f x₀ = 1`. -/
private lemma tendsto_logRoot_rhat (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    Tendsto (fun n : ℕ => Real.log (rhat q n) / n) atTop (𝓝 (Real.log (g q x₀))) := by
  sorry

/-- Lemma 4, first claim for `r̂`. -/
theorem tendsto_root_rhat (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    Tendsto (fun n : ℕ => rhat q n ^ (1 / (n : ℝ))) atTop (𝓝 (g q x₀)) := by
  have hg : 0 < g q x₀ := by unfold g; positivity
  exact tendsto_root_of_logRoot hg (fun n => rhat q n) (fun n => rhat_pos q n hq)
    (tendsto_logRoot_rhat q hq hx₀ hfx₀)

end Zeta5Odd
