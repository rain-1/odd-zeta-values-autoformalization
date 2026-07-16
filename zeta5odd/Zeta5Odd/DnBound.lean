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
* `hansonC_log_bound_finite` (`n < 1600`, `decide`)     — proved (sorry-free)
* `hansonC_log_bound_large`  (`n ≥ 1600`, Stirling)     — proved (sorry-free)

`lcmUpto_le_three_pow` (Hanson's bound `d_n ≤ 3^n`) is now **fully proved**: the whole range
`n < 1600` is machine-checked by `decide`, and `n ≥ 1600` is handled analytically by
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide`/`ofReduceBool`.

The large regime `n ≥ 1600` is assembled from sorry-free pieces:
* `sum_sylvTerm_lt_log_three` / `sum_sylvTerm_le_crat` — the certified transcendental rate estimate
  `∑ᵢ (log aᵢ)/aᵢ = 1.0824… < log 3`, via power-of-2 rational bounds on `log 7/43/1807`
  (`7²⁶<2⁷³`, …), a symbolic `(log 3)/3` term, and geometric tail domination;
* `hansonC_log_reduce` — the Stirling assembly: sharp two-sided Stirling (`log_factorial_le/ge`),
  the tangent-line inequality `mul_log_tangent`, `sum_inv_sylv`, and `core_sum_le` reduce the
  goal to a single boundary/growth inequality `n·rate + Eₙ,ₘ ≤ n·log 3`;
* `err_tangent_close` + `hanson_key` — the growth machinery.  `hanson_key` is a *self-bootstrapping*
  induction on the Sylvester index (the step needs no explicit bound on the index: the hypothesis
  supplies `(1+(k+1)/2)·log aₖ ≤ (2/125)·aₖ`, and the doubling `a_{k+1} ≥ aₖ²/2` absorbs the growth).
The threshold `N₀ = 1600` (`< sylv 4 = 1807`, so the `range 4` truncation still licenses the finite
`decide`) is where the closed-form Stirling relaxation first holds for all larger `n`.
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
/-- **Finite regime (fully proved, `decide`-backed).**  For `n < 1600`, the log size bound
holds.  Reduced to the `ℕ` inequality `n! ≤ 3^n · ∏_{i<4} ⌊n/aᵢ⌋!`, discharged by `decide`
(kernel GMP arithmetic; axioms `[propext, Classical.choice, Quot.sound]` only — no
`native_decide`/`ofReduceBool`).  `1337` is the threshold below which the closed-form Stirling
relaxation of `hansonC_log_bound_large` fails, and `1337 < sylv 4 = 1807` licenses the `range 4`
truncation. -/
theorem hansonC_log_bound_finite (n : ℕ) (hn : n < 1600) :
    Real.log (n.factorial : ℝ)
      ≤ (n : ℝ) * Real.log 3 + ∑ i ∈ range (n + 1), Real.log (((n / sylv i).factorial : ℝ)) := by
  have h4 : n < sylv 4 := lt_of_lt_of_le hn (by decide)
  have hfin : ∀ m ∈ range 1600,
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

/-! ### Certified rate bound `∑ᵢ (log aᵢ)/aᵢ < log 3`

The size half hinges on the transcendental estimate `∑ᵢ (log aᵢ)/aᵢ = 1.0824… < log 3`.
We certify it with a comfortable `0.016` margin by:
* bounding each `log aᵢ` (`a₂=7, a₃=43, a₄=1807`) by a *rational* multiple of `log 2` via a
  pure `ℕ` power inequality `aᵢ^b < 2^c` (`7²⁶ < 2⁷³`, `43⁷ < 2³⁸`, `1807 < 2¹¹`) and log
  monotonicity — no Taylor expansion needed;
* keeping the `a₁ = 3` term `(log 3)/3` symbolic (it cancels against the `log 3` on the right,
  leaving the clean numeric goal `coef·log 2 + tail < (2/3)·log 3`);
* dominating the doubly-exponential tail `∑_{i≥5}` by a geometric series (ratio `≤ 1/2`).
-/

section Rate
open Real

/-- Sylvester recurrence over `ℝ`: `a_{i+1} = aᵢ² − aᵢ + 1`. -/
theorem sylv_succ_real (i : ℕ) : (sylv (i + 1) : ℝ) = (sylv i : ℝ) ^ 2 - (sylv i : ℝ) + 1 := by
  have h1 : sylv (i + 1) = sylvProd i * (sylvProd i + 1) + 1 := rfl
  have h2 : (sylv i : ℝ) = (sylvProd i : ℝ) + 1 := by simp only [sylv]; push_cast; ring
  rw [h1]; push_cast
  rw [show ((sylvProd i : ℝ)) = (sylv i : ℝ) - 1 by rw [h2]; ring]
  ring

/-- `log 7 < (73/26)·log 2`, certified by `7²⁶ < 2⁷³`. -/
theorem log_seven_lt : Real.log 7 < (73 / 26 : ℝ) * Real.log 2 := by
  have hN : (7 : ℕ) ^ 26 < 2 ^ 73 := by norm_num
  have hlt : (7 : ℝ) ^ (26 : ℕ) < (2 : ℝ) ^ (73 : ℕ) := by exact_mod_cast hN
  have h := Real.log_lt_log (by positivity) hlt
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h; linarith

/-- `log 43 < (38/7)·log 2`, certified by `43⁷ < 2³⁸`. -/
theorem log_fortythree_lt : Real.log 43 < (38 / 7 : ℝ) * Real.log 2 := by
  have hN : (43 : ℕ) ^ 7 < 2 ^ 38 := by norm_num
  have hlt : (43 : ℝ) ^ (7 : ℕ) < (2 : ℝ) ^ (38 : ℕ) := by exact_mod_cast hN
  have h := Real.log_lt_log (by positivity) hlt
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h; linarith

/-- `log 1807 < 11·log 2`, certified by `1807 < 2¹¹`. -/
theorem log_1807_lt : Real.log 1807 < 11 * Real.log 2 := by
  have hlt : (1807 : ℝ) < (2 : ℝ) ^ (11 : ℕ) := by norm_num
  have h := Real.log_lt_log (by positivity) hlt
  rw [Real.log_pow] at h
  push_cast at h; linarith

theorem sylv_vals : sylv 0 = 2 ∧ sylv 1 = 3 ∧ sylv 2 = 7 ∧ sylv 3 = 43 ∧ sylv 4 = 1807
    ∧ sylv 5 = 3263443 := by decide

/-- Each rate term `(log aᵢ)/aᵢ` is nonnegative. -/
theorem sylvTerm_nonneg (i : ℕ) : 0 ≤ Real.log (sylv i) / (sylv i) := by
  apply div_nonneg
  · exact Real.log_nonneg (by exact_mod_cast (two_le_sylv i).trans' (by norm_num))
  · positivity

/-- Geometric decay of the tail: `(log a_{i+1})/a_{i+1} ≤ ½·(log aᵢ)/aᵢ` for `i ≥ 5`. -/
theorem sylvTerm_succ_le (i : ℕ) (hi : 5 ≤ i) :
    Real.log (sylv (i + 1)) / (sylv (i + 1)) ≤ Real.log (sylv i) / (sylv i) / 2 := by
  have h5 : (sylv 5 : ℝ) = 3263443 := by rw [sylv_vals.2.2.2.2.2]; norm_num
  have hmono : (sylv 5 : ℝ) ≤ (sylv i : ℝ) := by exact_mod_cast sylv_mono hi
  have ha : (3263443 : ℝ) ≤ (sylv i : ℝ) := by rw [← h5]; exact hmono
  set a : ℝ := (sylv i : ℝ) with hadef
  have ha0 : 0 < a := by linarith
  have hb : (sylv (i + 1) : ℝ) = a ^ 2 - a + 1 := by rw [hadef]; exact sylv_succ_real i
  have hbpos : 0 < a ^ 2 - a + 1 := by nlinarith
  have hb4a : 4 * a ≤ a ^ 2 - a + 1 := by nlinarith
  have hloga : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
  have hle : a ^ 2 - a + 1 ≤ a ^ 2 := by nlinarith
  have hlogb : Real.log (a ^ 2 - a + 1) ≤ 2 * Real.log a := by
    calc Real.log (a ^ 2 - a + 1) ≤ Real.log (a ^ 2) := Real.log_le_log hbpos hle
      _ = 2 * Real.log a := by rw [show a ^ 2 = a ^ (2 : ℕ) from rfl, Real.log_pow]; push_cast; ring
  rw [hb]
  calc Real.log (a ^ 2 - a + 1) / (a ^ 2 - a + 1)
      ≤ (2 * Real.log a) / (a ^ 2 - a + 1) := by gcongr
    _ ≤ (2 * Real.log a) / (4 * a) := by gcongr
    _ = Real.log a / a / 2 := by field_simp; ring

/-- Doubly-exponential decay solved: `(log a_{5+k})/a_{5+k} ≤ ((log a₅)/a₅)/2ᵏ`. -/
theorem sylvTerm_tail_geom (k : ℕ) :
    Real.log (sylv (5 + k)) / (sylv (5 + k))
      ≤ (Real.log (sylv 5) / (sylv 5)) / 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := sylvTerm_succ_le (5 + k) (by omega)
    calc Real.log (sylv (5 + (k + 1))) / (sylv (5 + (k + 1)))
        = Real.log (sylv ((5 + k) + 1)) / (sylv ((5 + k) + 1)) := by rw [Nat.add_succ]
      _ ≤ Real.log (sylv (5 + k)) / (sylv (5 + k)) / 2 := hstep
      _ ≤ ((Real.log (sylv 5) / (sylv 5)) / 2 ^ k) / 2 := by gcongr
      _ = (Real.log (sylv 5) / (sylv 5)) / 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- The whole tail `∑_{5≤i} (log aᵢ)/aᵢ` is bounded by `2·(log a₅)/a₅` (uniformly in the cutoff). -/
theorem sylvTerm_tail_sum (K : ℕ) :
    ∑ k ∈ range K, Real.log (sylv (5 + k)) / (sylv (5 + k))
      ≤ 2 * (Real.log (sylv 5) / (sylv 5)) := by
  have hnn : 0 ≤ Real.log (sylv 5) / (sylv 5) := sylvTerm_nonneg 5
  have hb : ∀ k ∈ range K, Real.log (sylv (5 + k)) / (sylv (5 + k))
      ≤ (Real.log (sylv 5) / (sylv 5)) * (2⁻¹ : ℝ) ^ k := by
    intro k _
    have h := sylvTerm_tail_geom k
    have heq : (Real.log (sylv 5) / (sylv 5)) / 2 ^ k
        = (Real.log (sylv 5) / (sylv 5)) * (2⁻¹ : ℝ) ^ k := by rw [inv_pow]; ring
    rwa [heq] at h
  calc ∑ k ∈ range K, Real.log (sylv (5 + k)) / (sylv (5 + k))
      ≤ ∑ k ∈ range K, (Real.log (sylv 5) / (sylv 5)) * (2⁻¹ : ℝ) ^ k :=
        Finset.sum_le_sum hb
    _ = (Real.log (sylv 5) / (sylv 5)) * ∑ k ∈ range K, (2⁻¹ : ℝ) ^ k := by
        rw [← Finset.mul_sum]
    _ ≤ (Real.log (sylv 5) / (sylv 5)) * 2 := by
        apply mul_le_mul_of_nonneg_left _ hnn
        rw [geom_sum_eq (by norm_num : (2⁻¹ : ℝ) ≠ 1)]
        have hp : (0:ℝ) ≤ (2⁻¹ : ℝ) ^ K := by positivity
        rw [div_le_iff_of_neg (by norm_num : (2⁻¹ : ℝ) - 1 < 0)]
        nlinarith [hp]
    _ = 2 * (Real.log (sylv 5) / (sylv 5)) := by ring

/-- **Certified rate bound (sorry-free).** For every truncation `N`,
`∑_{i<N} (log aᵢ)/aᵢ < log 3`.  This is Hanson's transcendental estimate `1.0824… < 1.0986…`. -/
theorem sum_sylvTerm_lt_log_three (N : ℕ) :
    ∑ i ∈ range N, Real.log (sylv i) / (sylv i) < Real.log 3 := by
  -- Uniform bound: partial sum ≤ (first five terms) + 2·(sixth term)
  have hsplit : ∑ i ∈ range N, Real.log (sylv i) / (sylv i)
      ≤ (∑ i ∈ range 5, Real.log (sylv i) / (sylv i))
        + 2 * (Real.log (sylv 5) / (sylv 5)) := by
    rcases lt_or_ge N 6 with hN | hN
    · have hsub : ∑ i ∈ range N, Real.log (sylv i) / (sylv i)
          ≤ ∑ i ∈ range 5, Real.log (sylv i) / (sylv i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (show N ≤ 5 by omega))
        intro i _ _
        exact sylvTerm_nonneg i
      have h2 : 0 ≤ 2 * (Real.log (sylv 5) / (sylv 5)) := by
        have := sylvTerm_nonneg 5; linarith
      linarith
    · rw [← Finset.sum_range_add_sum_Ico _ (by omega : 5 ≤ N),
        Finset.sum_Ico_eq_sum_range]
      have htail := sylvTerm_tail_sum (N - 5)
      gcongr
  -- Evaluate the first five terms and the sixth using the certified log bounds.
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := sylv_vals
  have hfive : (∑ i ∈ range 5, Real.log (sylv i) / (sylv i))
      = Real.log 2 / 2 + Real.log 3 / 3 + Real.log 7 / 7 + Real.log 43 / 43
        + Real.log 1807 / 1807 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, s0, s1, s2, s3, s4]
    push_cast; ring
  -- sixth term
  have hs5 : (sylv 5 : ℝ) = 3263443 := by rw [s5]; norm_num
  have h6 : 2 * (Real.log (sylv 5) / (sylv 5)) ≤ 2 * (22 * Real.log 2 / 3263443) := by
    rw [hs5]
    have hlog : Real.log 3263443 ≤ 22 * Real.log 2 := by
      have hlt : (3263443 : ℝ) < (2 : ℝ) ^ (22 : ℕ) := by norm_num
      have h := (Real.log_le_log (by norm_num) hlt.le)
      rw [Real.log_pow] at h; push_cast at h; linarith
    have : Real.log 3263443 / 3263443 ≤ 22 * Real.log 2 / 3263443 := by gcongr
    linarith
  rw [hfive] at hsplit
  -- Numeric close: use log2 < .6931471808, log3 > 1.0986122885, and the log-ratio bounds.
  have hl2 := Real.log_two_lt_d9
  have hl3 := Real.log_three_gt_d9
  have h7 := log_seven_lt
  have h43 := log_fortythree_lt
  have h1807 := log_1807_lt
  have hl2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [hsplit, h6, hl2, hl3, h7, h43, h1807, hl2pos]

/-- **Tangent-line (Gibbs) inequality** for the convex map `t ↦ t·log t`:
`t·log t + (log t + 1)(q − t) ≤ q·log q` for `q, t > 0`.  This is the lower bound "convex ≥
tangent" that turns `∑ qᵢ log qᵢ` into the closed form with rate `∑ (log aᵢ)/aᵢ`. -/
theorem mul_log_tangent (q t : ℝ) (hq : 0 < q) (ht : 0 < t) :
    t * Real.log t + (Real.log t + 1) * (q - t) ≤ q * Real.log q := by
  have hlog : Real.log (t / q) ≤ t / q - 1 := Real.log_le_sub_one_of_pos (div_pos ht hq)
  rw [Real.log_div ht.ne' hq.ne'] at hlog
  have h2 : q * (Real.log t - Real.log q) ≤ q * (t / q - 1) :=
    mul_le_mul_of_nonneg_left hlog hq.le
  rw [mul_sub, mul_sub, mul_div_cancel₀ _ hq.ne', mul_one] at h2
  have expand : t * Real.log t + (Real.log t + 1) * (q - t)
      = q * Real.log t + q - t := by ring
  rw [expand]; linarith [h2]

/-- `∏_{i<m} aᵢ = P_m` (`sylvProd` is the running product of Sylvester's sequence). -/
theorem sylvProd_eq_prod (m : ℕ) : sylvProd m = ∏ i ∈ range m, sylv i := by
  induction m with
  | zero => simp [sylvProd]
  | succ m ih => rw [Finset.prod_range_succ, ← ih, sylvProd_succ]

/-- **Numeric rate bound.** `∑_{i<N} (log aᵢ)/aᵢ ≤ C_rat` with `C_rat` an explicit rational
`< log 3`; the assembly needs the quantitative gap `log 3 − C_rat`, not just strictness. -/
theorem sum_sylvTerm_le_crat (N : ℕ) :
    ∑ i ∈ range N, Real.log (sylv i) / (sylv i)
      ≤ (1033446 / 1000000 : ℝ) * Real.log 2 + Real.log 3 / 3 := by
  have hsplit : ∑ i ∈ range N, Real.log (sylv i) / (sylv i)
      ≤ (∑ i ∈ range 5, Real.log (sylv i) / (sylv i))
        + 2 * (Real.log (sylv 5) / (sylv 5)) := by
    rcases lt_or_ge N 6 with hN | hN
    · have hsub : ∑ i ∈ range N, Real.log (sylv i) / (sylv i)
          ≤ ∑ i ∈ range 5, Real.log (sylv i) / (sylv i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (show N ≤ 5 by omega))
        intro i _ _; exact sylvTerm_nonneg i
      have h2 : 0 ≤ 2 * (Real.log (sylv 5) / (sylv 5)) := by
        have := sylvTerm_nonneg 5; linarith
      linarith
    · rw [← Finset.sum_range_add_sum_Ico _ (by omega : 5 ≤ N),
        Finset.sum_Ico_eq_sum_range]
      have htail := sylvTerm_tail_sum (N - 5)
      gcongr
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := sylv_vals
  have hfive : (∑ i ∈ range 5, Real.log (sylv i) / (sylv i))
      = Real.log 2 / 2 + Real.log 3 / 3 + Real.log 7 / 7 + Real.log 43 / 43
        + Real.log 1807 / 1807 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, s0, s1, s2, s3, s4]
    push_cast; ring
  have hs5 : (sylv 5 : ℝ) = 3263443 := by rw [s5]; norm_num
  have h6 : 2 * (Real.log (sylv 5) / (sylv 5)) ≤ 2 * (22 * Real.log 2 / 3263443) := by
    rw [hs5]
    have hlog : Real.log 3263443 ≤ 22 * Real.log 2 := by
      have hlt : (3263443 : ℝ) < (2 : ℝ) ^ (22 : ℕ) := by norm_num
      have h := (Real.log_le_log (by norm_num) hlt.le)
      rw [Real.log_pow] at h; push_cast at h; linarith
    have : Real.log 3263443 / 3263443 ≤ 22 * Real.log 2 / 3263443 := by gcongr
    linarith
  rw [hfive] at hsplit
  have h7 := log_seven_lt
  have h43 := log_fortythree_lt
  have h1807 := log_1807_lt
  have hl2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [hsplit, h6, h7, h43, h1807, hl2pos]

/-- `2^i ≤ P_i`: a crude single-exponential lower bound on the Sylvester products. -/
theorem two_pow_le_sylvProd (i : ℕ) : 2 ^ i ≤ sylvProd i := by
  induction i with
  | zero => simp [sylvProd]
  | succ i ih =>
    have hp := sylvProd_pos i
    calc 2 ^ (i + 1) = 2 ^ i * 2 := by ring
      _ ≤ sylvProd i * (sylvProd i + 1) := by
          apply Nat.mul_le_mul ih; omega
      _ = sylvProd (i + 1) := rfl

end Rate

section Assembly
open Real

/-- **Stirling assembly (sorry-free reduction).**  With `m` the number of Sylvester terms `≤ n`
(so `∑` over the goal's `range (n+1)` collapses to `range m`), the sharp two-sided Stirling
bounds, the tangent-line inequality, `sum_inv_sylv`, and `core_sum_le` reduce the goal to the
purely-analytic *growth* term `Eₙ,ₘ`: the whole Hanson size bound `log n! ≤ n·log 3 + ∑ …`
now follows from the single inequality `n·rate + Eₙ,ₘ ≤ n·log 3`. -/
theorem hansonC_log_reduce (n : ℕ) (hn : 2 ≤ n)
    (m : ℕ) (hmspec : n < sylv m) (hchar : ∀ i, i < m → sylv i ≤ n) :
    Real.log (n.factorial : ℝ)
      ≤ (∑ i ∈ range (n + 1), Real.log (((n / sylv i).factorial : ℝ)))
        + (n : ℝ) * (∑ i ∈ range m, Real.log (sylv i) / (sylv i))
        + ((1 / 2) * Real.log (2 * π * n) + 1 / (12 * n) + Real.log n - 1
           + ((m : ℝ) - 1) / 2 * Real.log n + (m : ℝ) * (1 - (1 / 2) * Real.log π)) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn_nn : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hqpos : ∀ i, i < m → 1 ≤ n / sylv i := fun i hi =>
    (Nat.one_le_div_iff (sylv_pos i)).mpr (hchar i hi)
  -- collapse the goal sum to `range m`
  have hgt : ∀ i, m ≤ i → n < sylv i := fun i hi => lt_of_lt_of_le hmspec (sylv_mono hi)
  have hmn : m ≤ n := by
    by_contra h; push_neg at h
    have h1 := hchar n h
    have h2 := lt_sylv_self n
    omega
  have hsplit : (∑ i ∈ range (n + 1), Real.log (((n / sylv i).factorial : ℝ)))
      = ∑ i ∈ range m, Real.log (((n / sylv i).factorial : ℝ)) := by
    symm
    apply Finset.sum_subset (Finset.range_subset_range.mpr (show m ≤ n + 1 by omega))
    intro i _ hi
    rw [Finset.mem_range] at hi
    have hlt : n < sylv i := hgt i (by omega)
    rw [Nat.div_eq_of_lt hlt, Nat.factorial_zero, Nat.cast_one, Real.log_one]
  rw [hsplit]
  -- Stirling upper bound on `log n!`
  have hUB := log_factorial_le n hn1
  -- Stirling lower bound on each `log ⌊n/aᵢ⌋!`, summed over `range m`
  have hLB : ∑ i ∈ range m, ((1 / 2) * Real.log π + (1 / 2) * Real.log (2 * ((n / sylv i : ℕ) : ℝ))
        + ((n / sylv i : ℕ) : ℝ) * Real.log ((n / sylv i : ℕ)) - ((n / sylv i : ℕ) : ℝ))
      ≤ ∑ i ∈ range m, Real.log (((n / sylv i).factorial : ℝ)) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    exact log_factorial_ge (n / sylv i) (hqpos i hi)
  -- === tangent-line lower bound on `∑ qᵢ log qᵢ` ===
  have htan : ∀ i ∈ range m,
      ((n : ℝ) / sylv i) * Real.log ((n : ℝ) / sylv i) - (Real.log ((n : ℝ) / sylv i) + 1)
        ≤ ((n / sylv i : ℕ) : ℝ) * Real.log ((n / sylv i : ℕ)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hsi : (0 : ℝ) < (sylv i : ℝ) := by exact_mod_cast sylv_pos i
    have hti : (0 : ℝ) < (n : ℝ) / sylv i := by positivity
    have hqiR : (1 : ℝ) ≤ ((n / sylv i : ℕ) : ℝ) := by exact_mod_cast hqpos i hi
    have hqipos : (0 : ℝ) < ((n / sylv i : ℕ) : ℝ) := by linarith
    have hqle : ((n / sylv i : ℕ) : ℝ) ≤ (n : ℝ) / sylv i := Nat.cast_div_le
    have hti1 : (1 : ℝ) ≤ (n : ℝ) / sylv i := le_trans hqiR hqle
    have hlogt_nn : 0 ≤ Real.log ((n : ℝ) / sylv i) := Real.log_nonneg hti1
    have hnlt : n < (n / sylv i + 1) * sylv i := by
      have hdm := Nat.div_add_mod n (sylv i)
      have hmod : n % sylv i < sylv i := Nat.mod_lt n (sylv_pos i)
      have heq : (n / sylv i + 1) * sylv i = sylv i * (n / sylv i) + sylv i := by ring
      omega
    have htlt : (n : ℝ) / sylv i < ((n / sylv i : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hsi]
      calc (n : ℝ) < (((n / sylv i : ℕ) + 1) * sylv i : ℕ) := by exact_mod_cast hnlt
        _ = (((n / sylv i : ℕ) : ℝ) + 1) * sylv i := by push_cast; ring
    have htang := mul_log_tangent ((n / sylv i : ℕ) : ℝ) ((n : ℝ) / sylv i) hqipos hti
    have e1 : (Real.log ((n : ℝ) / sylv i) + 1)
          * (((n / sylv i : ℕ) : ℝ) - (n : ℝ) / sylv i + 1)
        = (Real.log ((n : ℝ) / sylv i) + 1) * (((n / sylv i : ℕ) : ℝ) - (n : ℝ) / sylv i)
          + (Real.log ((n : ℝ) / sylv i) + 1) := by ring
    have hprod : 0 ≤ (Real.log ((n : ℝ) / sylv i) + 1)
        * (((n / sylv i : ℕ) : ℝ) - (n : ℝ) / sylv i + 1) :=
      mul_nonneg (by linarith) (by linarith)
    rw [e1] at hprod
    linarith [htang, hprod]
  have hAsum := Finset.sum_le_sum htan
  -- rewrite `∑ tᵢ log tᵢ` in terms of the rate `∑ (log aᵢ)/aᵢ`
  have htlogt : ∀ i ∈ range m, ((n : ℝ) / sylv i) * Real.log ((n : ℝ) / sylv i)
      = (n : ℝ) * Real.log n * (1 / sylv i) - (n : ℝ) * (Real.log (sylv i) / (sylv i)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hsi : (0 : ℝ) < (sylv i : ℝ) := by exact_mod_cast sylv_pos i
    rw [Real.log_div (ne_of_gt hnpos) (ne_of_gt hsi)]
    field_simp
  have hsumtlogt : ∑ i ∈ range m, ((n : ℝ) / sylv i) * Real.log ((n : ℝ) / sylv i)
      = (n : ℝ) * Real.log n * (∑ i ∈ range m, (1 : ℝ) / sylv i)
        - (n : ℝ) * (∑ i ∈ range m, Real.log (sylv i) / (sylv i)) := by
    rw [Finset.sum_congr rfl htlogt, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the `n log n · (1 − ∑ 1/aᵢ) = n log n / P_m ≤ log n` collapse
  have hsuminv : ∑ i ∈ range m, (1 : ℝ) / (sylv i) = 1 - 1 / (sylvProd m) := sum_inv_sylv m
  have hPpos : (0 : ℝ) < (sylvProd m : ℝ) := by exact_mod_cast sylvProd_pos m
  have hPm : (n : ℝ) ≤ (sylvProd m : ℝ) := by
    have : n ≤ sylvProd m := by simp only [sylv] at hmspec; omega
    exact_mod_cast this
  have hcollapse : (n : ℝ) * Real.log n
      - (n : ℝ) * Real.log n * (∑ i ∈ range m, (1 : ℝ) / sylv i) ≤ Real.log n := by
    rw [show (n : ℝ) * Real.log n - (n : ℝ) * Real.log n * (∑ i ∈ range m, (1 : ℝ) / sylv i)
          = (n : ℝ) * Real.log n * (1 - ∑ i ∈ range m, (1 : ℝ) / sylv i) by ring,
      hsuminv, show (1 : ℝ) - (1 - 1 / (sylvProd m)) = 1 / (sylvProd m) by ring, mul_one_div,
      div_le_iff₀ hPpos]
    nlinarith [mul_le_mul_of_nonneg_left hPm hlogn_nn]
  -- assemble (A):  n log n − ∑ qᵢ log qᵢ ≤ log n + n·rate + ∑ (log tᵢ + 1)
  have hA : (n : ℝ) * Real.log n
        - ∑ i ∈ range m, ((n / sylv i : ℕ) : ℝ) * Real.log ((n / sylv i : ℕ))
      ≤ Real.log n + (n : ℝ) * (∑ i ∈ range m, Real.log (sylv i) / (sylv i))
        + ∑ i ∈ range m, (Real.log ((n : ℝ) / sylv i) + 1) := by
    rw [Finset.sum_sub_distrib, hsumtlogt] at hAsum
    linarith [hAsum, hcollapse]
  -- (B):  ∑ qᵢ − n ≤ −1
  have hB : (∑ i ∈ range m, ((n / sylv i : ℕ) : ℝ)) - (n : ℝ) ≤ -1 := by
    have hcore := core_sum_le n hn1 m
    have h1 : ((∑ i ∈ range m, (n / sylv i : ℕ) : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hcore
    rw [Nat.cast_sub hn1] at h1
    push_cast at h1 ⊢
    linarith
  -- (half-log) per-term bound + summed, then ∑ log tᵢ ≤ (m−1) log n
  have hterm : ∀ i ∈ range m,
      (Real.log ((n : ℝ) / sylv i) + 1
        - ((1 / 2) * Real.log π + (1 / 2) * Real.log (2 * ((n / sylv i : ℕ) : ℝ))))
      ≤ (1 / 2) * Real.log ((n : ℝ) / sylv i) + (1 - (1 / 2) * Real.log π) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hsi : (0 : ℝ) < (sylv i : ℝ) := by exact_mod_cast sylv_pos i
    have hti : (0 : ℝ) < (n : ℝ) / sylv i := by positivity
    have hqiR : (1 : ℝ) ≤ ((n / sylv i : ℕ) : ℝ) := by exact_mod_cast hqpos i hi
    have hqle : ((n / sylv i : ℕ) : ℝ) ≤ (n : ℝ) / sylv i := Nat.cast_div_le
    have hnlt : n < (n / sylv i + 1) * sylv i := by
      have hdm := Nat.div_add_mod n (sylv i)
      have hmod : n % sylv i < sylv i := Nat.mod_lt n (sylv_pos i)
      have heq : (n / sylv i + 1) * sylv i = sylv i * (n / sylv i) + sylv i := by ring
      omega
    have htlt : (n : ℝ) / sylv i < ((n / sylv i : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hsi]
      calc (n : ℝ) < (((n / sylv i : ℕ) + 1) * sylv i : ℕ) := by exact_mod_cast hnlt
        _ = (((n / sylv i : ℕ) : ℝ) + 1) * sylv i := by push_cast; ring
    have h2q : (n : ℝ) / sylv i ≤ 2 * ((n / sylv i : ℕ) : ℝ) := by linarith
    have hlogmono : Real.log ((n : ℝ) / sylv i) ≤ Real.log (2 * ((n / sylv i : ℕ) : ℝ)) :=
      Real.log_le_log hti h2q
    linarith [hlogmono]
  have htermsum := Finset.sum_le_sum hterm
  have hsumlogt : ∑ i ∈ range m, Real.log ((n : ℝ) / sylv i) ≤ ((m : ℝ) - 1) * Real.log n := by
    have hexp : ∀ i ∈ range m, Real.log ((n : ℝ) / sylv i) = Real.log n - Real.log (sylv i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hsi : (0 : ℝ) < (sylv i : ℝ) := by exact_mod_cast sylv_pos i
      rw [Real.log_div (ne_of_gt hnpos) (ne_of_gt hsi)]
    rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have hprodlog : ∑ i ∈ range m, Real.log (sylv i) = Real.log ((sylvProd m : ℝ)) := by
      rw [sylvProd_eq_prod, Nat.cast_prod,
        Real.log_prod (fun i _ => Nat.cast_ne_zero.mpr (sylv_pos i).ne')]
    rw [hprodlog]
    have hlogPm : Real.log n ≤ Real.log ((sylvProd m : ℝ)) := Real.log_le_log hnpos hPm
    nlinarith [hlogPm]
  -- combine the half-log pieces
  have hRHSsum : ∑ i ∈ range m, ((1 / 2) * Real.log ((n : ℝ) / sylv i) + (1 - (1 / 2) * Real.log π))
      = (1 / 2) * (∑ i ∈ range m, Real.log ((n : ℝ) / sylv i))
        + (m : ℝ) * (1 - (1 / 2) * Real.log π) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- also decompose `∑ (log tᵢ + 1)` = ∑ log tᵢ + m
  have hlogt1 : ∑ i ∈ range m, (Real.log ((n : ℝ) / sylv i) + 1)
      = (∑ i ∈ range m, Real.log ((n : ℝ) / sylv i)) + (m : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  -- decompose the summed Stirling lower bound `L`
  have hLdecomp : ∑ i ∈ range m, ((1 / 2) * Real.log π
        + (1 / 2) * Real.log (2 * ((n / sylv i : ℕ) : ℝ))
        + ((n / sylv i : ℕ) : ℝ) * Real.log ((n / sylv i : ℕ)) - ((n / sylv i : ℕ) : ℝ))
      = (m : ℝ) * ((1 / 2) * Real.log π)
        + (∑ i ∈ range m, (1 / 2) * Real.log (2 * ((n / sylv i : ℕ) : ℝ)))
        + (∑ i ∈ range m, ((n / sylv i : ℕ) : ℝ) * Real.log ((n / sylv i : ℕ)))
        - (∑ i ∈ range m, ((n / sylv i : ℕ) : ℝ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- `∑ term_i` where `term_i = (log t_i + 1) − ½logπ − ½log(2 q_i)`:  its value in the pieces
  have htermval : ∑ i ∈ range m, (Real.log ((n : ℝ) / sylv i) + 1
        - ((1 / 2) * Real.log π + (1 / 2) * Real.log (2 * ((n / sylv i : ℕ) : ℝ))))
      = (∑ i ∈ range m, Real.log ((n : ℝ) / sylv i)) + (m : ℝ)
        - (m : ℝ) * ((1 / 2) * Real.log π)
        - (∑ i ∈ range m, (1 / 2) * Real.log (2 * ((n / sylv i : ℕ) : ℝ))) := by
    rw [Finset.sum_sub_distrib, hlogt1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  -- `π`-log identity
  have hlogid : (1 / 2) * Real.log π + (1 / 2) * Real.log (2 * (n : ℝ))
      = (1 / 2) * Real.log (2 * π * n) := by
    have h := Real.log_mul (ne_of_gt Real.pi_pos) (show (2 * (n : ℝ)) ≠ 0 by positivity)
    rw [show (2 : ℝ) * π * (n : ℝ) = π * (2 * (n : ℝ)) by ring, h]; ring
  -- Now `log n! ≤ ∑ log q_i! + (U − L)`, and `U − L ≤ n·rate + ERR`.
  -- Push everything into one linear combination.
  have hfinal : ((1 / 2) * Real.log π + (1 / 2) * Real.log (2 * (n : ℝ))
        + (n : ℝ) * Real.log n - (n : ℝ) + 1 / (12 * n))
      - (∑ i ∈ range m, ((1 / 2) * Real.log π
          + (1 / 2) * Real.log (2 * ((n / sylv i : ℕ) : ℝ))
          + ((n / sylv i : ℕ) : ℝ) * Real.log ((n / sylv i : ℕ)) - ((n / sylv i : ℕ) : ℝ)))
      ≤ (n : ℝ) * (∑ i ∈ range m, Real.log (sylv i) / (sylv i))
        + ((1 / 2) * Real.log (2 * π * n) + 1 / (12 * n) + Real.log n - 1
           + ((m : ℝ) - 1) / 2 * Real.log n + (m : ℝ) * (1 - (1 / 2) * Real.log π)) := by
    rw [hLdecomp]
    have htss := htermsum
    rw [hRHSsum, htermval] at htss
    -- htss now: ∑ log t_i + m − (m/2)logπ − ∑½log(2q_i) ≤ ½ ∑ log t_i + m(1−½logπ)
    nlinarith [hA, hB, htss, hsumlogt, hlogid, hlogn_nn]
  linarith [hUB, hLB, hfinal]

end Assembly

section Growth
open Real

/-- `log 1807 < (65/6)·log 2`, tighter than `11·log 2`, certified by `1807⁶ < 2⁶⁵`. -/
theorem log_1807_tight : Real.log 1807 < (65 / 6 : ℝ) * Real.log 2 := by
  have hN : (1807 : ℕ) ^ 6 < 2 ^ 65 := by norm_num
  have hlt : (1807 : ℝ) ^ (6 : ℕ) < (2 : ℝ) ^ (65 : ℕ) := by exact_mod_cast hN
  have h := Real.log_lt_log (by positivity) hlt
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h; linarith

/-- `log 1600 < (32/3)·log 2`, certified by `1600³ < 2³²`. -/
theorem log_1600_tight : Real.log 1600 < (32 / 3 : ℝ) * Real.log 2 := by
  have hN : (1600 : ℕ) ^ 3 < 2 ^ 32 := by norm_num
  have hlt : (1600 : ℝ) ^ (3 : ℕ) < (2 : ℝ) ^ (32 : ℕ) := by exact_mod_cast hN
  have h := Real.log_lt_log (by positivity) hlt
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h; linarith

/-- `7 < log 1807` (since `e⁷ < 1807`). -/
theorem seven_lt_log_1807 : (7 : ℝ) < Real.log 1807 := by
  have he : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
  have h1 : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h3 : Real.exp 1 ^ 7 < (2.72 : ℝ) ^ 7 := by gcongr
  have h2 : (2.72 : ℝ) ^ 7 < 1807 := by norm_num
  rw [Real.lt_log_iff_exp_lt (by norm_num), he]
  linarith [h3, h2]

/-- `log 3 < log π`  and  `log π ≤ 2·log 2`  (from `3 < π ≤ 4`). -/
theorem log3_lt_logpi : Real.log 3 < Real.log π :=
  Real.log_lt_log (by norm_num) Real.pi_gt_three

theorem logpi_le_two_log2 : Real.log π ≤ 2 * Real.log 2 := by
  have h := Real.log_le_log Real.pi_pos Real.pi_le_four
  rwa [Real.log_four_eq] at h

/-- **Tangent-line close.**  From the boundary inequality `hkey` at `n₀` and `hcoef`, the Stirling
growth term `Eₙ,ₘ` (in the exact form produced by `hansonC_log_reduce`) is `≤ (2/125)·nn` for all
`nn ≥ n₀`.  Uses concavity of `log` (`log nn ≤ log n₀ + nn/n₀ − 1`). -/
theorem err_tangent_close (M nn n0 : ℝ) (hM : 0 ≤ M) (hn0 : 0 < n0) (hle : n0 ≤ nn)
    (hcoef : 1 + M / 2 ≤ (2 / 125) * n0)
    (hkey : (1 + M / 2) * Real.log n0 + M * (1 - (1 / 2) * Real.log π)
        + ((1 / 2) * Real.log (2 * π) - 1) + 1 / (12 * n0) ≤ (2 / 125) * n0) :
    (1 / 2) * Real.log (2 * π * nn) + 1 / (12 * nn) + Real.log nn - 1
        + (M - 1) / 2 * Real.log nn + M * (1 - (1 / 2) * Real.log π) ≤ (2 / 125) * nn := by
  have hnnpos : 0 < nn := lt_of_lt_of_le hn0 hle
  have hsplit : Real.log (2 * π * nn) = Real.log (2 * π) + Real.log nn :=
    Real.log_mul (by positivity) (ne_of_gt hnnpos)
  rw [hsplit]
  set u : ℝ := nn / n0 with hudef
  have hun : nn = u * n0 := by rw [hudef]; field_simp
  have hu1 : 1 ≤ u := by rw [hudef, le_div_iff₀ hn0]; linarith
  have htanu : Real.log nn ≤ Real.log n0 + u - 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < nn / n0 by positivity)
    rw [Real.log_div (ne_of_gt hnnpos) (ne_of_gt hn0)] at h
    rw [← hudef] at h; linarith
  have hK : (0 : ℝ) ≤ 1 + M / 2 := by linarith
  have htanK := mul_le_mul_of_nonneg_left htanu hK
  have hprod : 0 ≤ (u - 1) * ((2 / 125) * n0 - (1 + M / 2)) :=
    mul_nonneg (by linarith) (by linarith)
  have h12 : 1 / (12 * nn) ≤ 1 / (12 * n0) := by
    apply one_div_le_one_div_of_le (by positivity); linarith
  rw [show (1 / 2) * (Real.log (2 * π) + Real.log nn) + 1 / (12 * nn) + Real.log nn - 1
        + (M - 1) / 2 * Real.log nn + M * (1 - (1 / 2) * Real.log π)
      = (1 + M / 2) * Real.log nn + M * (1 - (1 / 2) * Real.log π)
        + ((1 / 2) * Real.log (2 * π) - 1) + 1 / (12 * nn) by ring]
  nlinarith [htanK, hprod, hkey, hun, h12, hK, mul_nonneg hK (sub_nonneg.mpr hu1)]

set_option maxHeartbeats 2000000 in
/-- **The self-bootstrapping boundary inequality (KEY).**  For every Sylvester index `k ≥ 4`,
the closed-form boundary term at `n₀ = a_k = sylv k` is `≤ (2/125)·a_k`.  The induction step
does *not* need any explicit bound on `k`: the hypothesis at `k` gives
`(1+(k+1)/2)·log a_k ≤ (2/125)·a_k`, and the doubling `a_{k+1} ≥ a_k²/2` supplies the extra
factor `a_k/2 ≥ 900` that absorbs the growth from `k` to `k+1`. -/
theorem hanson_key (k : ℕ) (hk : 4 ≤ k) :
    (1 + ((k : ℝ) + 1) / 2) * Real.log (sylv k)
      + ((k : ℝ) + 1) * (1 - (1 / 2) * Real.log π)
      + ((1 / 2) * Real.log (2 * π) - 1) + 1 / (12 * (sylv k))
    ≤ (2 / 125 : ℝ) * (sylv k) := by
  have hlpi := log3_lt_logpi
  have hlpi2 := logpi_le_two_log2
  have hl2u := Real.log_two_lt_d9
  have hl2l := Real.log_two_gt_d9
  have hl3l := Real.log_three_gt_d9
  induction k, hk using Nat.le_induction with
  | base =>
    -- base k = 4, sylv 4 = 1807
    have hs4 : (sylv 4 : ℝ) = 1807 := by rw [show sylv 4 = 1807 from by decide]; norm_num
    rw [hs4]
    have h1807 := log_1807_tight
    have hlog2pi : Real.log (2 * π) = Real.log 2 + Real.log π :=
      Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)
    rw [hlog2pi]
    push_cast
    nlinarith [h1807, hlpi, hl2u, hl3l]
  | succ k hk ih =>
    -- s = sylv k, S = sylv (k+1) = s² − s + 1
    set s : ℝ := (sylv k : ℝ) with hsdef
    have hSeq : (sylv (k + 1) : ℝ) = s ^ 2 - s + 1 := by rw [hsdef]; exact sylv_succ_real k
    have hs1807 : (1807 : ℝ) ≤ s := by
      rw [hsdef]
      have : sylv 4 ≤ sylv k := sylv_mono hk
      have h4 : (sylv 4 : ℝ) = 1807 := by rw [show sylv 4 = 1807 from by decide]; norm_num
      calc (1807 : ℝ) = (sylv 4 : ℝ) := h4.symm
        _ ≤ (sylv k : ℝ) := by exact_mod_cast this
    have hspos : (0 : ℝ) < s := by linarith
    have hSge : s ^ 2 / 2 ≤ (sylv (k + 1) : ℝ) := by rw [hSeq]; nlinarith
    have hSle : (sylv (k + 1) : ℝ) ≤ s ^ 2 := by rw [hSeq]; nlinarith
    have hSpos : (0 : ℝ) < (sylv (k + 1) : ℝ) := by rw [hSeq]; nlinarith
    have hlogS : Real.log (sylv (k + 1)) ≤ 2 * Real.log s := by
      calc Real.log (sylv (k + 1)) ≤ Real.log (s ^ 2) := Real.log_le_log hSpos hSle
        _ = 2 * Real.log s := by rw [show s ^ 2 = s ^ (2 : ℕ) from rfl, Real.log_pow]; push_cast; ring
    have hlogs7 : (7 : ℝ) ≤ Real.log s := by
      have h1 := seven_lt_log_1807
      have h2 : Real.log 1807 ≤ Real.log s := Real.log_le_log (by norm_num) hs1807
      linarith
    have hlogs_pos : (0 : ℝ) ≤ Real.log s := by linarith
    have hkpos : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hk4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hmul : Real.log (2 * π) = Real.log 2 + Real.log π :=
      Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)
    -- crude two-sided bounds on `b := 1 − ½logπ` and `C₀ := ½log(2π) − 1`
    have hb_lo : (3 : ℝ) / 10 ≤ 1 - (1 / 2) * Real.log π := by nlinarith [hlpi2, hl2u]
    have hb_ub : (1 - (1 / 2) * Real.log π) ≤ 1 / 2 := by nlinarith [hlpi, hl3l]
    have hC0_lo : (-(1 : ℝ) / 8) ≤ (1 / 2) * Real.log (2 * π) - 1 := by
      rw [hmul]; nlinarith [hl2l, hlpi, hl3l]
    have hC0_ub : (1 / 2) * Real.log (2 * π) - 1 ≤ (1 : ℝ) / 20 := by
      rw [hmul]; nlinarith [hlpi2, hl2u]
    -- IH ⟹ the weak bootstrap  (1+(k+1)/2)·log s ≤ (2/125)·s
    have hIHw : (1 + ((k : ℝ) + 1) / 2) * Real.log s ≤ (2 / 125) * s := by
      have h12s : (0 : ℝ) ≤ 1 / (12 * s) := by positivity
      nlinarith [ih, hC0_lo, h12s, hk4,
        mul_nonneg (show (0:ℝ) ≤ (k:ℝ) + 1 by linarith)
          (show (0:ℝ) ≤ (1 - (1/2) * Real.log π) - 3/10 by linarith [hb_lo])]
    -- multiply by s and use the doubling `S ≥ s²/2`
    have hbig : (1 + ((k : ℝ) + 1) / 2) * Real.log s * s ≤ (2 / 125) * s ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hIHw hspos.le]
    have h_a : ((k : ℝ) + 3) / 4 * s * Real.log s ≤ (1 / 125) * s ^ 2 := by nlinarith [hbig]
    have h_b : (1 / 125) * s ^ 2 ≤ (2 / 125) * (sylv (k + 1) : ℝ) := by nlinarith [hSge]
    have hTone : (1 : ℝ) ≤ (sylv (k + 1) : ℝ) := by exact_mod_cast sylv_pos (k + 1)
    have h12T : 1 / (12 * (sylv (k + 1) : ℝ)) ≤ 1 / 12 := by
      refine one_div_le_one_div_of_le (by norm_num) ?_; linarith
    -- `log T` coefficient bound (T = sylv (k+1))
    have hlogTcoef : (1 + ((k : ℝ) + 2) / 2) * Real.log (sylv (k + 1))
        ≤ ((k : ℝ) + 4) * Real.log s := by
      have hc : (0 : ℝ) ≤ 1 + ((k : ℝ) + 2) / 2 := by positivity
      calc (1 + ((k : ℝ) + 2) / 2) * Real.log (sylv (k + 1))
          ≤ (1 + ((k : ℝ) + 2) / 2) * (2 * Real.log s) := mul_le_mul_of_nonneg_left hlogS hc
        _ = ((k : ℝ) + 4) * Real.log s := by ring
    -- the bounded remainder `K₁`
    have hK1 : ((k : ℝ) + 2) * (1 - (1 / 2) * Real.log π) + ((1 / 2) * Real.log (2 * π) - 1)
        + 1 / (12 * (sylv (k + 1) : ℝ)) ≤ ((k : ℝ) + 2) * (1 / 2) + 1 / 20 + 1 / 12 := by
      have hm := mul_le_mul_of_nonneg_left hb_ub (show (0 : ℝ) ≤ (k : ℝ) + 2 by linarith)
      linarith [hm, hC0_ub, h12T]
    -- the trivial-margin step: `(k+4)·log s + K₁ ≤ (k+3)/4·s·log s`
    have hstep1 : ((k : ℝ) + 3) / 4 * 1807 * Real.log s ≤ ((k : ℝ) + 3) / 4 * s * Real.log s :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs1807 (by positivity)) hlogs_pos
    have hklog : (7 : ℝ) * (k : ℝ) ≤ (k : ℝ) * Real.log s := by
      have := mul_le_mul_of_nonneg_left hlogs7 hkpos; linarith
    have hstep2 : ((k : ℝ) + 4) * Real.log s + (((k : ℝ) + 2) * (1 / 2) + 1 / 20 + 1 / 12)
        ≤ ((k : ℝ) + 3) / 4 * 1807 * Real.log s := by linarith [hlogs7, hkpos, hk4, hklog]
    have h_c : ((k : ℝ) + 4) * Real.log s + (((k : ℝ) + 2) * (1 / 2) + 1 / 20 + 1 / 12)
        ≤ ((k : ℝ) + 3) / 4 * s * Real.log s := le_trans hstep2 hstep1
    have hcombine : (1 + ((k : ℝ) + 2) / 2) * Real.log (sylv (k + 1))
          + (((k : ℝ) + 2) * (1 - (1 / 2) * Real.log π) + ((1 / 2) * Real.log (2 * π) - 1)
             + 1 / (12 * (sylv (k + 1) : ℝ)))
        ≤ (2 / 125) * (sylv (k + 1) : ℝ) := by
      calc (1 + ((k : ℝ) + 2) / 2) * Real.log (sylv (k + 1))
            + (((k : ℝ) + 2) * (1 - (1 / 2) * Real.log π) + ((1 / 2) * Real.log (2 * π) - 1)
               + 1 / (12 * (sylv (k + 1) : ℝ)))
          ≤ ((k : ℝ) + 4) * Real.log s + (((k : ℝ) + 2) * (1 / 2) + 1 / 20 + 1 / 12) := by
            linarith [hlogTcoef, hK1]
        _ ≤ ((k : ℝ) + 3) / 4 * s * Real.log s := h_c
        _ ≤ (1 / 125) * s ^ 2 := h_a
        _ ≤ (2 / 125) * (sylv (k + 1) : ℝ) := h_b
    push_cast
    linarith [hcombine]

end Growth

/-- **Large regime — fully proved.**  For `n ≥ 1600` the log size bound follows from the
sorry-free Stirling assembly `hansonC_log_reduce`, the certified rate bound `sum_sylvTerm_le_crat`,
and the growth machinery (`err_tangent_close` + `hanson_key`) which discharges the boundary
inequality `n·rate + Eₙ,ₘ ≤ n·log 3`. -/
theorem hansonC_log_bound_large (n : ℕ) (hn : 1600 ≤ n) :
    Real.log (n.factorial : ℝ)
      ≤ (n : ℝ) * Real.log 3 + ∑ i ∈ range (n + 1), Real.log (((n / sylv i).factorial : ℝ)) := by
  open Real in
  have hn2 : 2 ≤ n := by omega
  have hnpos : (0 : ℝ) ≤ (n : ℝ) := by positivity
  -- the Sylvester count `m`
  have hex : ∃ k, n < sylv k := ⟨n, lt_sylv_self n⟩
  set m := Nat.find hex with hmdef
  have hmspec : n < sylv m := Nat.find_spec hex
  have hchar : ∀ i, i < m → sylv i ≤ n := fun i hi => by
    have := Nat.find_min hex hi; omega
  have hm4 : 4 ≤ m := by
    by_contra h; push_neg at h
    have hmono : sylv m ≤ sylv 3 := sylv_mono (by omega)
    have h3 : sylv 3 = 43 := by decide
    have : n < sylv 3 := lt_of_lt_of_le hmspec hmono
    omega
  -- the Stirling reduction and the certified rate bound
  have hred := hansonC_log_reduce n hn2 m hmspec hchar
  have hrate := sum_sylvTerm_le_crat m
  have hnrate : (n : ℝ) * (∑ i ∈ range m, Real.log (sylv i) / (sylv i))
      ≤ (n : ℝ) * ((1033446 / 1000000 : ℝ) * Real.log 2 + Real.log 3 / 3) :=
    mul_le_mul_of_nonneg_left hrate hnpos
  -- the certified numeric gap  `2/125 ≤ log 3 − C_rat`
  have hgap : (2 / 125 : ℝ)
      ≤ Real.log 3 - ((1033446 / 1000000 : ℝ) * Real.log 2 + Real.log 3 / 3) := by
    nlinarith [Real.log_two_lt_d9, Real.log_three_gt_d9]
  have hgapn := mul_le_mul_of_nonneg_right hgap hnpos
  -- pi/log helper bounds
  have hlpi := log3_lt_logpi
  have hlpi2 := logpi_le_two_log2
  have hl2u := Real.log_two_lt_d9
  have hl3l := Real.log_three_gt_d9
  have hmul : Real.log (2 * π) = Real.log 2 + Real.log π :=
    Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)
  -- **growth**:  `Eₙ,ₘ ≤ (2/125)·n`
  have hERR : (1 / 2) * Real.log (2 * π * n) + 1 / (12 * n) + Real.log n - 1
        + ((m : ℝ) - 1) / 2 * Real.log n + (m : ℝ) * (1 - (1 / 2) * Real.log π)
      ≤ (2 / 125) * (n : ℝ) := by
    have hMnn : (0 : ℝ) ≤ (m : ℝ) := by positivity
    rcases Nat.lt_or_ge m 5 with h5 | h5
    · -- m = 4, tangent at n₀ = 1600
      have hm4' : m = 4 := by omega
      have hmR : (m : ℝ) = 4 := by rw [hm4']; norm_num
      have hn1600 : (1600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hcoef : 1 + (m : ℝ) / 2 ≤ (2 / 125) * 1600 := by rw [hmR]; norm_num
      have hkey : (1 + (m : ℝ) / 2) * Real.log 1600 + (m : ℝ) * (1 - (1 / 2) * Real.log π)
          + ((1 / 2) * Real.log (2 * π) - 1) + 1 / (12 * (1600 : ℝ)) ≤ (2 / 125) * 1600 := by
        rw [hmR, hmul]
        nlinarith [log_1600_tight, hlpi, hl2u, hl3l]
      exact err_tangent_close (m : ℝ) (n : ℝ) 1600 hMnn (by norm_num) hn1600 hcoef hkey
    · -- m ≥ 5, tangent at n₀ = sylv (m-1)
      have hk : 4 ≤ m - 1 := by omega
      have hmc : (m : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by
        have h1 : 1 ≤ m := by omega
        rw [Nat.cast_sub h1]; norm_num
      have hle : (sylv (m - 1) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hchar (m - 1) (by omega)
      have hn0pos : (0 : ℝ) < (sylv (m - 1) : ℝ) := by exact_mod_cast sylv_pos (m - 1)
      -- KEY at n₀ = sylv (m-1) from `hanson_key`
      have hkey : (1 + (m : ℝ) / 2) * Real.log (sylv (m - 1))
          + (m : ℝ) * (1 - (1 / 2) * Real.log π) + ((1 / 2) * Real.log (2 * π) - 1)
          + 1 / (12 * (sylv (m - 1) : ℝ)) ≤ (2 / 125) * (sylv (m - 1) : ℝ) := by
        rw [hmc]; exact hanson_key (m - 1) hk
      -- coefficient bound `1 + m/2 ≤ (2/125)·sylv(m-1)` (log ≥ 1, remainder ≥ 0)
      have hs1807 : (1807 : ℝ) ≤ (sylv (m - 1) : ℝ) := by
        have : sylv 4 ≤ sylv (m - 1) := sylv_mono hk
        have h4 : sylv 4 = 1807 := by decide
        calc (1807 : ℝ) = (sylv 4 : ℝ) := by rw [h4]; norm_num
          _ ≤ (sylv (m - 1) : ℝ) := by exact_mod_cast this
      have hlog1 : (1 : ℝ) ≤ Real.log (sylv (m - 1)) := by
        have := seven_lt_log_1807
        have h2 : Real.log 1807 ≤ Real.log (sylv (m - 1)) := Real.log_le_log (by norm_num) hs1807
        linarith
      have hb_lo : (3 : ℝ) / 10 ≤ 1 - (1 / 2) * Real.log π := by nlinarith [hlpi2, hl2u]
      have hC0_lo : (-(1 : ℝ) / 8) ≤ (1 / 2) * Real.log (2 * π) - 1 := by
        rw [hmul]; nlinarith [Real.log_two_gt_d9, hlpi, hl3l]
      have hmge5 : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h5
      have hcoef : 1 + (m : ℝ) / 2 ≤ (2 / 125) * (sylv (m - 1) : ℝ) := by
        have h12 : (0 : ℝ) ≤ 1 / (12 * (sylv (m - 1) : ℝ)) := by positivity
        nlinarith [hkey, hlog1, hb_lo, hC0_lo, hmge5, hMnn, h12,
          mul_nonneg hMnn (show (0 : ℝ) ≤ (1 - (1 / 2) * Real.log π) - 3 / 10 by linarith),
          mul_le_mul_of_nonneg_left hlog1 (show (0 : ℝ) ≤ 1 + (m : ℝ) / 2 by positivity)]
      exact err_tangent_close (m : ℝ) (n : ℝ) (sylv (m - 1)) hMnn hn0pos hle hcoef hkey
  -- combine reduction + rate + growth
  have hERRn : (1 / 2) * Real.log (2 * π * n) + 1 / (12 * n) + Real.log n - 1
        + ((m : ℝ) - 1) / 2 * Real.log n + (m : ℝ) * (1 - (1 / 2) * Real.log π)
      ≤ (Real.log 3 - ((1033446 / 1000000 : ℝ) * Real.log 2 + Real.log 3 / 3)) * (n : ℝ) :=
    le_trans hERR hgapn
  nlinarith [hred, hnrate, hERRn]

/-- **Size bound in log form.**  `C n ≤ 3^n` is exactly

  `log n! ≤ n·log 3 + ∑_{i<n+1} log ⌊n/aᵢ⌋!`.

This is TRUE for every `n` (numerically `max_n (log C n − n·log 3) = −0.386 < 0`).  It is proved
by splitting at `n = 1600`: the finite regime `n < 1600` is fully machine-checked
(`hansonC_log_bound_finite`, `decide`-backed, sorry-free), and the large regime `n ≥ 1600` is
proved analytically (`hansonC_log_bound_large`, sorry-free).  This dispatcher is itself sorry-free. -/
theorem hansonC_log_bound (n : ℕ) :
    Real.log (n.factorial : ℝ)
      ≤ (n : ℝ) * Real.log 3 + ∑ i ∈ range (n + 1), Real.log (((n / sylv i).factorial : ℝ)) := by
  rcases Nat.lt_or_ge n 1600 with h | h
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
### Status of the size half — fully proved, sorry-free (`N₀ = 1600`)

The size bound `hansonC_log_bound` is split into two regimes at `N₀ = 1600`, both sorry-free:

* `hansonC_log_bound_finite`  (`n < 1600`) — the `range 4` truncation `hansonDenom_eq_prod4`
  (valid since `n < 1600 < sylv 4 = 1807`) collapses the denominator to `∏_{i<4} ⌊n/aᵢ⌋!`,
  reducing the goal to the `ℕ` inequality `n! ≤ 3^n · ∏_{i<4} ⌊n/aᵢ⌋!`, discharged by a single
  `decide` over `range 1600` (kernel GMP arithmetic; no `native_decide`).
* `hansonC_log_bound_large`  (`n ≥ 1600`) — the analytic Stirling argument (see below).

**Why the margin is thin.**  `log 3 = 1.09861` versus the limiting rate
`∑_i (log aᵢ)/aᵢ = 1.08239`, only `0.01622` per unit `n`.  Applying the sharp Stirling bounds
`log_factorial_le/ge` term-by-term (upper on `n!`, lower on each `⌊n/aᵢ⌋!`) with the tangent line
of the convex `t↦t log t` yields a closed-form relaxation that first holds for all `n ≥ N₀`; the
looser (but fully formalizable) constants used here push the crossover to `N₀ = 1600 < 1807`.

**Proof of `hansonC_log_bound_large`.**  For `n ≥ 1600`, with `m = #{i : aᵢ ≤ n}`:
1. `hansonC_log_reduce` (sorry-free) — `log n! ≤ ½log(2πn) + n log n − n + 1/(12n)`
   (`log_factorial_le`); each `log ⌊n/aᵢ⌋! ≥ ½log(2π⌊n/aᵢ⌋)+⌊n/aᵢ⌋ log⌊n/aᵢ⌋−⌊n/aᵢ⌋`
   (`log_factorial_ge`); bound `n log n − ∑ qᵢ log qᵢ` via `mul_log_tangent` and
   `n log n·(1−∑_{i<m}1/aᵢ) = n log n / Pₘ ≤ log n` (`sum_inv_sylv`, `Pₘ ≥ n`); `core_sum_le`
   for `n − ∑ qᵢ ≥ 1`.  This reduces the whole bound to `n·rate + Eₙ,ₘ ≤ n·log 3`.
2. `sum_sylvTerm_le_crat` (sorry-free) — the certified rational rate `∑_{i<m}(log aᵢ)/aᵢ ≤ C_rat`
   with `C_rat < log 3`, via `aᵢ^b < 2^c` power-of-2 bounds and a geometric tail.
3. `err_tangent_close` + `hanson_key` (sorry-free) — the growth term `Eₙ,ₘ ≤ (2/125)·n < (log3−C_rat)·n`.
   `hanson_key` is a self-bootstrapping induction on the Sylvester index whose step needs no explicit
   index bound, using the doubling `a_{k+1} ≥ aₖ²/2`.

Quot.sound]` — no `sorryAx`, no `native_decide`/`ofReduceBool`.

**Finite-check note.**  `decide` on `hansonC n` / `hansonDenom n` directly is INFEASIBLE (the
product forces evaluating `sylv i` up to `i = n`, doubly-exponentially large).
`hansonDenom_eq_prod4` sidesteps this via the fixed product `∏_{i<4} ⌊n/aᵢ⌋!` (only `sylv 0..3`).
-/

end Zeta5Odd


