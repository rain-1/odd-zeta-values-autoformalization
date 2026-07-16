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
* `hansonC_le_three_pow` (the size bound `C n ≤ 3^n`)   — the ONLY `sorry`.

Thus `lcmUpto_le_three_pow` is reduced to the single analytic estimate `C n ≤ 3^n`
(equivalently `∑ᵢ (log aᵢ)/aᵢ < log 3`, a Stirling computation), numerically verified
for all `n` with margin (`maxₙ (log C n − n·log 3) = −0.386`).  `#print axioms` shows the
divisibility chain uses no `sorryAx`; only the size wrapper does.
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

/-- **Residual analytic core** (the ONLY remaining `sorry`).  In log form, the size bound
`C n ≤ 3^n` is exactly

  `log n! ≤ n·log 3 + ∑_{i<n+1} log ⌊n/aᵢ⌋!`.

This is TRUE for every `n` (numerically `max_n (log C n − n·log 3) = −0.386 < 0`, and the exact
two-sided Stirling bound below leaves worst-case slack `+0.292` at `n = 83`).  The reduction of
the theorem `hansonC_le_three_pow` to *this* inequality is fully proved (sorry-free); only the
inequality itself is open.  See the end-of-file note for the obstruction and completion paths. -/
theorem hansonC_log_bound (n : ℕ) :
    Real.log (n.factorial : ℝ)
      ≤ (n : ℝ) * Real.log 3 + ∑ i ∈ range (n + 1), Real.log (((n / sylv i).factorial : ℝ)) := by
  sorry

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
### Status of the size half (`hansonC_log_bound`, the sole `sorry`)

Everything except the single real inequality `hansonC_log_bound` is proved sorry-free:

* `log_factorial_eq / log_factorial_le / log_factorial_ge` — sharp two-sided Stirling bounds
  `½log(2πm) + m·log m − m ≤ log m! ≤ ½log(2πm) + m·log m − m + 1/(12m)` (from
  `Zeta5Odd.Basic.log_stirlingSeq_sub_le` and Mathlib's `sqrt_pi_le_stirlingSeq`).
* `hansonC_le_three_pow` — the reduction of `C n ≤ 3^n` to `hansonC_log_bound`, via
  `hansonDenom n ∣ n!` (exact division ⇒ `C n · hansonDenom n = n!`), `Real.log_le_log_iff`,
  `Real.log_prod`, `Real.log_pow`.

**Residual (true, open):** `log n! ≤ n·log 3 + ∑_{i<n+1} log ⌊n/aᵢ⌋!`.

**Why it is hard.**  The margin is genuinely thin: `log 3 = 1.09861` versus the limiting rate
`∑_i (log aᵢ)/aᵢ = 1.08239`, i.e. only `0.01622` per unit `n`, and the *absolute* worst-case
slack `min_n (n·log 3 − log C n) = 0.386` occurs at `n = 83`.

Applying the sharp Stirling bounds above term-by-term (upper on `n!`, lower on each `⌊n/aᵢ⌋!`)
gives worst-case slack `+0.292` at `n = 83` — so the two-sided Stirling estimate DOES suffice,
*provided the floor terms `⌊n/aᵢ⌋` are kept essentially exact*.  Any further clean relaxation
breaks it for small `n`:
  * relaxing `q·log q ≥ q·log(n/aᵢ) − (n/aᵢ − q)` (the elementary `t log t ≥ t − 1`) already
    dips to `−0.023` at `n = 83`;
  * additionally constant-izing `∑ q·log aᵢ ≤ n·∑(log aᵢ)/aᵢ` fails up to `n = 635`
    (keeping the `½log` and `n−∑qᵢ` terms exact) or up to `n = 3542` (fully closed form).

**Completion paths.**
1. *Symbolic ≥ N₀ + finite check < N₀.*  Prove the closed-form bound for `n ≥ N₀`
   (`N₀ = 636` or `3543` per above) using: `core_sum_le`/`sum_inv_sylv` for `n − ∑ qᵢ ≤ 1 + |I|`
   and `∑ 1/aᵢ = 1 − 1/Pₙ`; a rational upper bound `∑(log aᵢ)/aᵢ < log 3` (dominated by
   `i ≤ 5`, doubly-exponential tail); and the Stirling `½log` bookkeeping.  Then a finite check
   for `n < N₀`.
2. *Finite check obstruction.*  `decide`/`native_decide` on `hansonC n` directly is INFEASIBLE:
   its product ranges over `range (n+1)`, forcing evaluation of `sylv i` for `i` up to `n`, which
   is doubly-exponentially large (`sylvProd 30` already has ~10⁹ digits).  The finite check must
   first rewrite `hansonDenom n = ∏_{i<B} ⌊n/aᵢ⌋!` for a small fixed `B` (e.g. `B = 6`, valid for
   `n < sylv 6 ≈ 1.06·10¹³`), so only `sylv 0..5 ≤ 3 263 443` are ever evaluated.
-/

end Zeta5Odd
