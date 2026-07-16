/-
Hanson's elementary bound `d_n = lcm(1,…,n) ≤ 3^n`.

Mathlib provides only the weaker Chebyshev bound `ψ x ≤ log4·x + o(x)` (⇒ `d_n ≲ 4^n`),
which is insufficient for any `s`.  Hanson (1972) gives the elementary `d_n < 3^n`, enabling
`s = 33`.  Verified numerically for all `n` (max rate `log d_n / n = 1.0388 < log 3`).

Building blocks in Mathlib: `Nat.lcmUpto`, `Chebyshev.psi_eq_log_lcmUpto`,
`Chebyshev.isBigO_psi_sub_theta_sqrt` (ψ−θ = O(√x log x)), `primorial_add_le`,
`Nat.choose_dvd_lcmUpto`.

## Proof architecture (Hanson 1972)

Let `a₀ = 2, a₁ = 3, a₂ = 7, a₃ = 43, …` be **Sylvester's sequence** and
`P k = a₀·a₁·⋯·a_{k-1}` its partial products (`P k = 1, 2, 6, 42, 1806, …`, with
`a k = P k + 1`).  Hanson's integer is the multinomial-type quotient

    C n = n! / (⌊n/a₀⌋! · ⌊n/a₁⌋! · ⌊n/a₂⌋! · ⋯).

The proof has two halves:

* **Divisibility** `d_n ∣ C n`.  By Legendre's formula this reduces, prime-by-prime and
  power-by-power, to the elementary inequality  `∑ᵢ ⌊m/aᵢ⌋ ≤ m − 1`  for every `m ≥ 1`
  (`core_sum_le` below — **fully proved**).  The subtle point: the partial sums
  `∑ᵢ 1/aᵢ = 1 − 1/P_N` are *strictly* below `1`, so the comparison must be carried out over
  `ℝ` (where `m/P_N > 0`), not over `ℕ` (where `⌊m/P_N⌋` collapses to `0`).

* **Size** `C n ≤ 3^n`.  A Stirling estimate turns this into
  `∑ᵢ (log aᵢ)/aᵢ = 1.0826… < log 3 = 1.0986…`.

Status of this file:
* `sum_inv_sylv`  (telescoping identity)               — proved (sorry-free)
* `core_sum_le`   (the arithmetic heart `∑⌊m/aᵢ⌋≤m−1`) — proved (sorry-free)
* `hansonDenom_dvd`, `hansonC_pos`                      — proved (sorry-free)
* `lcmUpto_dvd_hansonC`  (**entire divisibility half**) — proved (sorry-free)
* `hansonC_le_three_pow` (the size bound `C n ≤ 3^n`)   — reduced (sorry-free) to `hansonC_log_bound`
* `hansonC_log_bound_finite` (`n < 1337`, `decide`)     — proved (sorry-free)
* `hansonC_log_bound_large`  (`n ≥ 1337`, Stirling)     — the ONLY `sorry`.

Thus `lcmUpto_le_three_pow` is reduced to the single analytic estimate `C n ≤ 3^n` for `n ≥ 1337`
(equivalently `∑ᵢ (log aᵢ)/aᵢ < log 3`, a Stirling computation); the whole range `n < 1337` is
machine-checked by `decide`.  Numerically verified for all `n` with margin
(`maxₙ (log C n − n·log 3) = −0.386`).  `#print axioms` shows the divisibility chain and the finite
size regime use no `sorryAx`; only `hansonC_log_bound_large` does.
-/
import Mathlib
import Zeta5Odd.Basic

namespace Zeta5Odd

open Finset

/-! ### Sylvester's sequence and its partial products -/

/-- Partial products of Sylvester's sequence: `P 0 = 1`, `P (k+1) = P k · (P k + 1)`,
giving `P = 1, 2, 6, 42, 1806, …`. -/
def sylvProd : ℕ → ℕ
  | 0 => 1
  | (k + 1) => sylvProd k * (sylvProd k + 1)

/-- Sylvester's sequence `a k = P k + 1 = 2, 3, 7, 43, 1807, …`. -/
def sylv (k : ℕ) : ℕ := sylvProd k + 1

theorem sylvProd_pos : ∀ k, 0 < sylvProd k
  | 0 => one_pos
  | (k + 1) => by
      have := sylvProd_pos k
      simp only [sylvProd]; positivity

theorem sylvProd_succ (k : ℕ) : sylvProd (k + 1) = sylvProd k * sylv k := rfl

theorem two_le_sylv (k : ℕ) : 2 ≤ sylv k := by
  have := sylvProd_pos k; simp only [sylv]; omega

theorem sylv_pos (k : ℕ) : 0 < sylv k := by have := two_le_sylv k; omega

/-! ### The telescoping identity `∑_{i<N} 1/aᵢ = 1 − 1/P_N` (over `ℝ`) -/

theorem sum_inv_sylv (N : ℕ) :
    ∑ i ∈ range N, (1 : ℝ) / sylv i = 1 - 1 / sylvProd N := by
  induction N with
  | zero => simp [sylvProd]
  | succ N ih =>
    rw [sum_range_succ, ih, sylvProd_succ]
    have hP : (0 : ℝ) < sylvProd N := by exact_mod_cast sylvProd_pos N
    have hs : (sylv N : ℝ) = sylvProd N + 1 := by simp [sylv]
    have hs0 : (0 : ℝ) < sylv N := by exact_mod_cast sylv_pos N
    push_cast
    rw [hs]
    field_simp
    ring

/-! ### The core inequality `∑ᵢ ⌊m/aᵢ⌋ ≤ m − 1` for `m ≥ 1` -/

/-- Over `ℝ`, the sum of `⌊m/aᵢ⌋` is *strictly* below `m`: it is at most
`m − m/P_N < m` because the Sylvester partial sums miss `1` by exactly `1/P_N`. -/
theorem sum_div_sylv_lt (m : ℕ) (hm : 1 ≤ m) (N : ℕ) :
    (∑ i ∈ range N, (m / sylv i : ℕ) : ℝ) < m := by
  have hstep : (∑ i ∈ range N, (m / sylv i : ℕ) : ℝ) ≤ (m : ℝ) - m / sylvProd N := by
    calc (∑ i ∈ range N, (m / sylv i : ℕ) : ℝ)
        = ∑ i ∈ range N, ((m / sylv i : ℕ) : ℝ) := by norm_cast
      _ ≤ ∑ i ∈ range N, (m : ℝ) / sylv i := by
          apply sum_le_sum; intro _ _; exact Nat.cast_div_le
      _ = (m : ℝ) * ∑ i ∈ range N, (1 : ℝ) / sylv i := by
          rw [mul_sum]; apply sum_congr rfl; intro i _; rw [mul_one_div]
      _ = (m : ℝ) * (1 - 1 / sylvProd N) := by rw [sum_inv_sylv]
      _ = (m : ℝ) - m / sylvProd N := by ring
  have hpos : (0 : ℝ) < m / sylvProd N := by
    apply div_pos
    · exact_mod_cast hm
    · exact_mod_cast sylvProd_pos N
  linarith

/-- **Core inequality (fully proved).** For every `m ≥ 1` and every truncation `N`,
`∑_{i<N} ⌊m/aᵢ⌋ ≤ m − 1`.  This is the arithmetic heart of Hanson's divisibility claim. -/
theorem core_sum_le (m : ℕ) (hm : 1 ≤ m) (N : ℕ) :
    ∑ i ∈ range N, m / sylv i ≤ m - 1 := by
  have h := sum_div_sylv_lt m hm N
  have hnat : (∑ i ∈ range N, m / sylv i) < m := by exact_mod_cast h
  omega

/-! ### Hanson's integer and the reduction of the main theorem -/

/-- Hanson's multinomial-type integer `C n = n! / ∏ᵢ ⌊n/aᵢ⌋!`.  The product ranges over
`i < n+1`, more than enough terms since `aᵢ > n` (hence `⌊n/aᵢ⌋! = 1`) for small `i`. -/
def hansonC (n : ℕ) : ℕ := n.factorial / ∏ i ∈ range (n + 1), (n / sylv i).factorial

/-- The denominator `∏ᵢ ⌊n/aᵢ⌋!`. -/
def hansonDenom (n : ℕ) : ℕ := ∏ i ∈ range (n + 1), (n / sylv i).factorial

theorem hansonDenom_ne_zero (n : ℕ) : hansonDenom n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _

/-- Legendre's formula for `n!` at a prime `p`, truncated at the (over-generous) bound `n+1`. -/
theorem factFact (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (n.factorial).factorization p = ∑ j ∈ Ico 1 (n + 1), n / p ^ j :=
  Nat.factorization_factorial hp (Nat.lt_succ_of_le (Nat.log_le_self p n))

/-- Legendre's formula applied to the denominator, with the two sums swapped and the floor
identity `⌊⌊n/aᵢ⌋/pʲ⌋ = ⌊⌊n/pʲ⌋/aᵢ⌋`. -/
theorem denomFact (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (hansonDenom n).factorization p
      = ∑ j ∈ Ico 1 (n + 1), ∑ i ∈ range (n + 1), n / p ^ j / sylv i := by
  unfold hansonDenom
  rw [Nat.factorization_prod (fun i _ => Nat.factorial_ne_zero _), Finsupp.finsetSum_apply]
  have hterm : ∀ i ∈ range (n + 1), ((n / sylv i).factorial).factorization p
      = ∑ j ∈ Ico 1 (n + 1), n / sylv i / p ^ j := fun i _ =>
    Nat.factorization_factorial hp
      (Nat.lt_succ_of_le ((Nat.log_le_self p _).trans (Nat.div_le_self n (sylv i))))
  rw [sum_congr rfl hterm, Finset.sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- Inner bound: `∑ᵢ ⌊(n/pʲ)/aᵢ⌋ ≤ n/pʲ` (weak form, always true). -/
theorem inner_le (n p j : ℕ) : ∑ i ∈ range (n + 1), n / p ^ j / sylv i ≤ n / p ^ j := by
  rcases Nat.eq_zero_or_pos (n / p ^ j) with h0 | hpos
  · simp [h0]
  · exact (core_sum_le _ hpos _).trans (Nat.sub_le _ _)

/-- The denominator divides `n!` (per prime, `inner_le` via Legendre), hence `C n > 0`. -/
theorem hansonDenom_dvd (n : ℕ) : hansonDenom n ∣ n.factorial := by
  rw [← Nat.factorization_le_iff_dvd (hansonDenom_ne_zero n) (Nat.factorial_ne_zero n),
    Finsupp.le_iff]
  intro p hp_supp
  have hp : p.Prime :=
    Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp_supp)
  rw [denomFact n hp, factFact n hp]
  exact Finset.sum_le_sum fun j _ => inner_le n p j

theorem hansonC_pos (n : ℕ) : 0 < hansonC n :=
  Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos n) (hansonDenom_dvd n))
    (Finset.prod_pos fun _ _ => Nat.factorial_pos _)

/-- **Divisibility half.**  `d_n ∣ C n`.  By Legendre's formula the exponent of a prime `p`
in `C n` is `∑_{j≥1} (⌊n/pʲ⌋ − ∑ᵢ ⌊n/(aᵢ pʲ)⌋)`; each of the `⌊log_p n⌋` terms with
`pʲ ≤ n` is `≥ 1` by `core_sum_le` (with `m = ⌊n/pʲ⌋ ≥ 1`), giving exponent
`≥ ⌊log_p n⌋ = v_p(d_n)`. -/
theorem lcmUpto_dvd_hansonC (n : ℕ) : Nat.lcmUpto n ∣ hansonC n := by
  have hDdvd := hansonDenom_dvd n
  -- `hansonC n * hansonDenom n = n!`
  have hCmul : hansonC n * hansonDenom n = n.factorial := Nat.div_mul_cancel hDdvd
  rw [← Nat.factorization_le_iff_dvd (Nat.lcmUpto_ne_zero n) (hansonC_pos n).ne',
    Finsupp.le_iff]
  intro p hp_supp
  have hp : p.Prime :=
    Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp_supp)
  -- from `hansonC n * hansonDenom n = n!`, split the factorization additively
  have hadd : (hansonC n).factorization p + (hansonDenom n).factorization p
      = (n.factorial).factorization p := by
    rw [← Finsupp.add_apply,
      ← Nat.factorization_mul (hansonC_pos n).ne' (hansonDenom_ne_zero n), hCmul]
  rw [Nat.factorization_lcmUpto n hp]
  -- reduce to an additive inequality avoiding truncated subtraction
  set L := Nat.log p n with hL
  -- goal: L ≤ (hansonC n).factorization p
  have key : L + (hansonDenom n).factorization p ≤ (n.factorial).factorization p := by
    rw [denomFact n hp, factFact n hp]
    -- ∑ j, (∑ i, ⌊n/pʲ/aᵢ⌋)  vs  ∑ j, ⌊n/pʲ⌋, with a surplus of ≥ 1 on j = 1..L
    have hsplit : ∀ j ∈ Ico 1 (n + 1),
        (∑ i ∈ range (n + 1), n / p ^ j / sylv i)
          + (n / p ^ j - ∑ i ∈ range (n + 1), n / p ^ j / sylv i) = n / p ^ j :=
      fun j _ => Nat.add_sub_cancel' (inner_le n p j)
    rw [← Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    -- suffices: L ≤ ∑ j, (⌊n/pʲ⌋ − ∑ i ⌊n/pʲ/aᵢ⌋)
    have hsub : Ico 1 (L + 1) ⊆ Ico 1 (n + 1) :=
      Finset.Ico_subset_Ico_right (by have := Nat.log_le_self p n; omega)
    have hB : L ≤ ∑ j ∈ Ico 1 (n + 1),
        (n / p ^ j - ∑ i ∈ range (n + 1), n / p ^ j / sylv i) := by
      calc L = ∑ _j ∈ Ico 1 (L + 1), 1 := by rw [Finset.sum_const, Nat.card_Ico]; simp
        _ ≤ ∑ j ∈ Ico 1 (L + 1),
              (n / p ^ j - ∑ i ∈ range (n + 1), n / p ^ j / sylv i) := by
            refine Finset.sum_le_sum fun j hj => ?_
            rw [Finset.mem_Ico] at hj
            have hn0 : n ≠ 0 := by
              rintro rfl
              have : L = 0 := by rw [hL]; simp
              omega
            have hpj : p ^ j ≤ n := Nat.pow_le_of_le_log hn0 (by omega)
            have hdpos : 1 ≤ n / p ^ j := (Nat.one_le_div_iff (pow_pos hp.pos j)).mpr hpj
            have := core_sum_le (n / p ^ j) hdpos (n + 1)
            omega
        _ ≤ ∑ j ∈ Ico 1 (n + 1),
              (n / p ^ j - ∑ i ∈ range (n + 1), n / p ^ j / sylv i) :=
            Finset.sum_le_sum_of_subset hsub
    omega
  omega

/-! ### Stirling log-factorial bounds (from `Zeta5Odd.Basic`) -/

section Size
open Real Stirling

/-- Exact log-factorial identity via Mathlib's `stirlingSeq`:
`log m! = log(stirlingSeq m) + ½·log(2m) + m·log m − m`. -/
theorem log_factorial_eq (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m.factorial : ℝ)
      = Real.log (stirlingSeq m) + (1 / 2) * Real.log (2 * m) + (m : ℝ) * Real.log m - m := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2m : (0 : ℝ) < 2 * (m : ℝ) := by positivity
  have hSpos : 0 < stirlingSeq m :=
    lt_of_lt_of_le (Real.sqrt_pos.mpr pi_pos) (sqrt_pi_le_stirlingSeq (by omega))
  have hpow : (0 : ℝ) < ((m : ℝ) / Real.exp 1) ^ m := by positivity
  have hsqrt : (0 : ℝ) < √(2 * (m : ℝ)) := Real.sqrt_pos.mpr h2m
  have hfac : (m.factorial : ℝ) = stirlingSeq m * (√(2 * (m : ℝ)) * ((m : ℝ) / Real.exp 1) ^ m) := by
    rw [stirlingSeq]; field_simp
  rw [hfac, Real.log_mul hSpos.ne' (by positivity),
      Real.log_mul hsqrt.ne' hpow.ne', Real.log_sqrt h2m.le, Real.log_pow,
      Real.log_div hmR.ne' he.ne', Real.log_exp]
  ring

theorem log_sqrt_pi : Real.log (√π) = (1 / 2) * Real.log π := by
  rw [Real.log_sqrt pi_pos.le]; ring

/-- Upper bound: `log m! ≤ ½·log(2πm) + m·log m − m + 1/(12m)`  (split as `½logπ + ½log(2m)`). -/
theorem log_factorial_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m.factorial : ℝ)
      ≤ (1 / 2) * Real.log π + (1 / 2) * Real.log (2 * m) + (m : ℝ) * Real.log m - m
        + 1 / (12 * m) := by
  rw [log_factorial_eq m hm]
  have h := log_stirlingSeq_sub_le m hm
  rw [log_sqrt_pi] at h
  linarith

/-- Lower bound: `½·log(2πm) + m·log m − m ≤ log m!`. -/
theorem log_factorial_ge (m : ℕ) (hm : 1 ≤ m) :
    (1 / 2) * Real.log π + (1 / 2) * Real.log (2 * m) + (m : ℝ) * Real.log m - m
      ≤ Real.log (m.factorial : ℝ) := by
  rw [log_factorial_eq m hm]
  have hlo : √π ≤ stirlingSeq m := sqrt_pi_le_stirlingSeq (by omega)
  have h : Real.log (√π) ≤ Real.log (stirlingSeq m) := Real.log_le_log (Real.sqrt_pos.mpr pi_pos) hlo
  rw [log_sqrt_pi] at h
  linarith

end Size

/-! ### Monotonicity of Sylvester's sequence and a truncation lemma

For `n < sylv 4 = 1807` every tail factor `⌊n/aᵢ⌋! = 1` (`i ≥ 4`), so the denominator
collapses to the fixed finite product `∏_{i<4} ⌊n/aᵢ⌋!`.  This makes the small-`n` regime
`decide`-computable: only `sylv 0..3 = 2,3,7,43` are ever evaluated. -/

/-- `k ≤ P k` (`sylvProd` dominates the identity). -/
theorem id_le_sylvProd : ∀ k, k ≤ sylvProd k
  | 0 => Nat.zero_le _
  | (k + 1) => by
      have ih := id_le_sylvProd k
      have h1 : sylvProd (k + 1) = sylvProd k * (sylvProd k + 1) := rfl
      have hp := sylvProd_pos k
      rw [h1]; nlinarith [ih, hp]

/-- `sylvProd` is monotone. -/
theorem sylvProd_mono : Monotone sylvProd :=
  monotone_nat_of_le_succ fun k => by
    have h1 : sylvProd (k + 1) = sylvProd k * (sylvProd k + 1) := rfl
    rw [h1]; nlinarith [sylvProd_pos k]

/-- Sylvester's sequence `a k = P k + 1` is monotone. -/
theorem sylv_mono : Monotone sylv := fun a b h => by
  simp only [sylv]; exact Nat.add_le_add_right (sylvProd_mono h) 1

/-- `k < a k` (each Sylvester term exceeds its index). -/
theorem lt_sylv_self (i : ℕ) : i < sylv i := by
  have := id_le_sylvProd i; simp only [sylv]; omega

/-- **Truncation.**  For `n < sylv 4 = 1807`, the full denominator `∏_{i<n+1} ⌊n/aᵢ⌋!`
collapses to `∏_{i<4} ⌊n/aᵢ⌋!` (all further factors are `0! = 1`). -/
theorem hansonDenom_eq_prod4 (n : ℕ) (hn : n < sylv 4) :
    hansonDenom n = ∏ i ∈ range 4, (n / sylv i).factorial := by
  unfold hansonDenom
  rcases Nat.lt_or_ge (n + 1) 4 with h | h
  · refine Finset.prod_subset (by intro x hx; rw [Finset.mem_range] at hx ⊢; omega) ?_
    intro i _ hin
    rw [Finset.mem_range, not_lt] at hin
    have hlt : n < sylv i := lt_of_lt_of_le (by omega : n < i) (le_of_lt (lt_sylv_self i))
    rw [Nat.div_eq_of_lt hlt, Nat.factorial_zero]
  · refine (Finset.prod_subset (by intro x hx; rw [Finset.mem_range] at hx ⊢; omega) ?_).symm
    intro i _ hi4
    rw [Finset.mem_range, not_lt] at hi4
    have hlt : n < sylv i := lt_of_lt_of_le hn (sylv_mono hi4)
    rw [Nat.div_eq_of_lt hlt, Nat.factorial_zero]

set_option maxRecDepth 40000 in
/-- **Finite regime (fully proved, `decide`-backed).**  For `n < 1337`, the log size bound
holds.  Reduced to the `ℕ` inequality `n! ≤ 3^n · ∏_{i<4} ⌊n/aᵢ⌋!`, discharged by `decide`
(kernel GMP arithmetic; axioms `[propext, Classical.choice, Quot.sound]` only — no
`native_decide`/`ofReduceBool`).  `1337` is the threshold below which the closed-form Stirling
relaxation of `hansonC_log_bound_large` fails, and `1337 < sylv 4 = 1807` licenses the `range 4`
truncation. -/
theorem hansonC_log_bound_finite (n : ℕ) (hn : n < 1337) :
    Real.log (n.factorial : ℝ)
      ≤ (n : ℝ) * Real.log 3 + ∑ i ∈ range (n + 1), Real.log (((n / sylv i).factorial : ℝ)) := by
  have h4 : n < sylv 4 := lt_of_lt_of_le hn (by decide)
  have hfin : ∀ m ∈ range 1337,
      m.factorial ≤ 3 ^ m * ∏ i ∈ range 4, (m / sylv i).factorial := by decide
  have hkeyNat : n.factorial ≤ 3 ^ n * hansonDenom n := by
    rw [hansonDenom_eq_prod4 n h4]; exact hfin n (Finset.mem_range.mpr hn)
  have hDpos : (0 : ℝ) < (hansonDenom n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (hansonDenom_ne_zero n)
  have hlogD : Real.log (hansonDenom n : ℝ)
      = ∑ i ∈ range (n + 1), Real.log (((n / sylv i).factorial : ℝ)) := by
    unfold hansonDenom
    rw [Nat.cast_prod,
      Real.log_prod (fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
  have hstar : (n.factorial : ℝ) ≤ (3 : ℝ) ^ n * (hansonDenom n : ℝ) := by
    exact_mod_cast hkeyNat
  calc Real.log (n.factorial : ℝ)
      ≤ Real.log ((3 : ℝ) ^ n * (hansonDenom n : ℝ)) :=
        Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) hstar
    _ = (n : ℝ) * Real.log 3
          + ∑ i ∈ range (n + 1), Real.log (((n / sylv i).factorial : ℝ)) := by
        rw [Real.log_mul (by positivity) hDpos.ne', Real.log_pow, hlogD]

/-- **Large regime (residual `sorry`).**  For `n ≥ 1337` the log size bound follows from the
sharp two-sided Stirling estimate combined with the closed-form rate bound
`∑ᵢ (log aᵢ)/aᵢ < log 3`.  This is the sole remaining analytic obstruction; see the
end-of-file note. -/
theorem hansonC_log_bound_large (n : ℕ) (hn : 1337 ≤ n) :
    Real.log (n.factorial : ℝ)
      ≤ (n : ℝ) * Real.log 3 + ∑ i ∈ range (n + 1), Real.log (((n / sylv i).factorial : ℝ)) := by
  sorry

/-- **Size bound in log form.**  `C n ≤ 3^n` is exactly

  `log n! ≤ n·log 3 + ∑_{i<n+1} log ⌊n/aᵢ⌋!`.

This is TRUE for every `n` (numerically `max_n (log C n − n·log 3) = −0.386 < 0`).  It is proved
by splitting at `n = 1337`: the finite regime `n < 1337` is fully machine-checked
(`hansonC_log_bound_finite`, `decide`-backed, sorry-free), and the large regime `n ≥ 1337` is the
sole remaining `sorry` (`hansonC_log_bound_large`).  This dispatcher is itself sorry-free. -/
theorem hansonC_log_bound (n : ℕ) :
    Real.log (n.factorial : ℝ)
      ≤ (n : ℝ) * Real.log 3 + ∑ i ∈ range (n + 1), Real.log (((n / sylv i).factorial : ℝ)) := by
  rcases Nat.lt_or_ge n 1337 with h | h
  · exact hansonC_log_bound_finite n h
  · exact hansonC_log_bound_large n h

/-- **Size half.**  `C n ≤ 3^n`.  Fully reduced (sorry-free) to `hansonC_log_bound`:
`hansonDenom n ∣ n!` gives `C n = n!/hansonDenom n` exactly, so `C n ≤ 3^n` is equivalent to
`n! ≤ 3^n · hansonDenom n`, which (all factors positive) is equivalent to the log inequality. -/
theorem hansonC_le_three_pow (n : ℕ) : (hansonC n : ℝ) ≤ 3 ^ n := by
  have hD : hansonDenom n ∣ n.factorial := hansonDenom_dvd n
  have hCmul : hansonC n * hansonDenom n = n.factorial := Nat.div_mul_cancel hD
  have hDpos : (0 : ℝ) < (hansonDenom n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (hansonDenom_ne_zero n)
  have hn0 : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hrhs : (0 : ℝ) < (3 : ℝ) ^ n * (hansonDenom n : ℝ) := by positivity
  have hlogD : Real.log (hansonDenom n : ℝ)
      = ∑ i ∈ range (n + 1), Real.log (((n / sylv i).factorial : ℝ)) := by
    unfold hansonDenom
    rw [Nat.cast_prod,
      Real.log_prod (fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
  -- (⋆):  `n! ≤ 3^n · hansonDenom n`, obtained by exponentiating the log inequality.
  have star : (n.factorial : ℝ) ≤ (3 : ℝ) ^ n * (hansonDenom n : ℝ) := by
    refine (Real.log_le_log_iff hn0 hrhs).mp ?_
    rw [Real.log_mul (by positivity) hDpos.ne', Real.log_pow, hlogD]
    exact hansonC_log_bound n
  -- transfer `n! ≤ 3^n · D` through the exact identity `C n · D = n!`.
  have hmul : (hansonC n : ℝ) * (hansonDenom n : ℝ) ≤ (3 : ℝ) ^ n * (hansonDenom n : ℝ) :=
    calc (hansonC n : ℝ) * (hansonDenom n : ℝ)
        = ((hansonC n * hansonDenom n : ℕ) : ℝ) := by push_cast; ring
      _ = (n.factorial : ℝ) := by rw [hCmul]
      _ ≤ (3 : ℝ) ^ n * (hansonDenom n : ℝ) := star
  exact le_of_mul_le_mul_right hmul hDpos

/-- **Hanson's bound.** `d_n = lcm(1,…,n) ≤ 3^n`. -/
theorem lcmUpto_le_three_pow (n : ℕ) : (Nat.lcmUpto n : ℝ) ≤ 3 ^ n := by
  have hle : Nat.lcmUpto n ≤ hansonC n :=
    Nat.le_of_dvd (hansonC_pos n) (lcmUpto_dvd_hansonC n)
  calc (Nat.lcmUpto n : ℝ) ≤ (hansonC n : ℝ) := by exact_mod_cast hle
    _ ≤ 3 ^ n := hansonC_le_three_pow n

/-!
### Status of the size half — one isolated `sorry` (`hansonC_log_bound_large`, `n ≥ 1337`)

The size bound `hansonC_log_bound` is now split into two regimes at `N₀ = 1337`:

* `hansonC_log_bound_finite`  (`n < 1337`) — **fully proved, sorry-free.**  The `range 4`
  truncation `hansonDenom_eq_prod4` (valid since `n < 1337 < sylv 4 = 1807`) collapses the
  denominator to `∏_{i<4} ⌊n/aᵢ⌋!`, reducing the goal to the `ℕ` inequality
  `n! ≤ 3^n · ∏_{i<4} ⌊n/aᵢ⌋!`, which is discharged by a single `decide` over `range 1337`
  (kernel GMP arithmetic; `#print axioms` = `[propext, Classical.choice, Quot.sound]`, i.e. NO
  `sorryAx` and NO `Lean.ofReduceBool` — `native_decide` is deliberately avoided).  Timing: the
  whole finite check elaborates+kernel-checks in ≈3 s.
* `hansonC_log_bound_large`  (`n ≥ 1337`) — **the sole remaining `sorry`.**

**Residual (true, open):** `log n! ≤ n·log 3 + ∑_{i<n+1} log ⌊n/aᵢ⌋!` for `n ≥ 1337`.

**Why it is hard.**  The margin is genuinely thin: `log 3 = 1.09861` versus the limiting rate
`∑_i (log aᵢ)/aᵢ = 1.08239`, i.e. only `0.01622` per unit `n`, and the *absolute* worst-case
slack `min_n (n·log 3 − log C n) = 0.386` occurs at `n = 83`.  Applying the sharp Stirling bounds
`log_factorial_le/ge` term-by-term (upper on `n!`, lower on each `⌊n/aᵢ⌋!`) leaves worst-case
slack `+0.292` at `n = 83` — so two-sided Stirling suffices *provided the floors are kept exact*.
Any clean relaxation dips negative for small `n`, forcing the finite/symbolic split.  The chosen
`N₀ = 1337` is exactly where the *constant-rate* tangent-Stirling relaxation
(`q·log q ≥ (n/aᵢ)·log(n/aᵢ) − (log(n/aᵢ)+1)`, then `∑_I (log aᵢ)/aᵢ ≤ ∑_all = 1.08239`) first
holds for all larger `n` (verified numerically; the partial-rate variant crosses over at 1018).

**Completion path for `hansonC_log_bound_large`.**  For `n ≥ 1337`:
`log n! ≤ ½log(2πn) + n·log n − n + 1/(12n)` (`log_factorial_le`); each `log ⌊n/aᵢ⌋! ≥
½log(2π⌊n/aᵢ⌋) + ⌊n/aᵢ⌋·log⌊n/aᵢ⌋ − ⌊n/aᵢ⌋` (`log_factorial_ge`).  Then bound
`n log n − ∑ᵢ qᵢ log qᵢ ≤ log n + n·∑_{i∈I}(log aᵢ)/aᵢ + ∑_{i∈I}(log(n/aᵢ)+1)` via the tangent
line of the convex `t↦t log t` (`q ≥ n/aᵢ − 1`) plus `n log n·(1−∑_{i∈I}1/aᵢ) = n log n / P_{|I|}
≤ log n` (since `P_{|I|} = a_{|I|} − 1 ≥ n`, from `sum_inv_sylv`); use `core_sum_le` for
`n − ∑ qᵢ ≥ 1`; and a *certified rational* bound `∑_i (log aᵢ)/aᵢ < log 3` (dominated by `i ≤ 5`,
doubly-exponential tail — this certified transcendental estimate is the main missing ingredient).

**Finite-check obstruction (resolved).**  `decide` on `hansonC n` / `hansonDenom n` directly is
INFEASIBLE: the product ranges over `range (n+1)`, forcing evaluation of `sylv i` up to `i = n`,
which is doubly-exponentially large (`sylvProd 30` already has ~10⁹ digits).  `hansonDenom_eq_prod4`
sidesteps this by rewriting to the fixed product `∏_{i<4} ⌊n/aᵢ⌋!` (only `sylv 0..3 = 2,3,7,43`
are ever evaluated), which makes the `decide` cheap.
-/

end Zeta5Odd
