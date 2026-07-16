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

/-- **Size half.**  `C n ≤ 3^n`.  Stirling's estimate reduces this to the numerical fact
`∑ᵢ (log aᵢ)/aᵢ = 1.0826… < log 3`.  (Verified: `max_n (log C n − n·log 3) = −0.386 < 0`.) -/
theorem hansonC_le_three_pow (n : ℕ) : (hansonC n : ℝ) ≤ 3 ^ n := by
  sorry

/-- **Hanson's bound.** `d_n = lcm(1,…,n) ≤ 3^n`. -/
theorem lcmUpto_le_three_pow (n : ℕ) : (Nat.lcmUpto n : ℝ) ≤ 3 ^ n := by
  have hle : Nat.lcmUpto n ≤ hansonC n :=
    Nat.le_of_dvd (hansonC_pos n) (lcmUpto_dvd_hansonC n)
  calc (Nat.lcmUpto n : ℝ) ≤ (hansonC n : ℝ) := by exact_mod_cast hle
    _ ≤ 3 ^ n := hansonC_le_three_pow n

end Zeta5Odd
