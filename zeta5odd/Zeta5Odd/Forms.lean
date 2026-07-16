/-
Arithmetic core: paper Lemmas 1–3 plus the ζ(3)-elimination.

`R_n(t)` (paper e02) with `s = 2q−1`, the bridge `R(n+1+k) = c q n k`,
`R(n+1/2+k) = chat q n k`, the partial-fraction decomposition `R(t) = Σ a_{i,k}/(t+k)^i`
(e04) with the well-poised symmetry `a_{i,k} = (−1)^{i-1} a_{i,n−k}` (Lemmas 1–2), and the
resulting representations of `r_n`, `r̂_n` as ℤ[1/d_n]-combinations of odd zeta values
(Lemma 3, e07/e08).  The `7 = 2^3−1` twist cancels the ζ(3) term.

For `q = 17` (`s = 33`) this yields: `d_n^{33}·(7 r_n − r̂_n)` is an integer combination of
`ζ(5),…,ζ(33)` plus an integer constant.

STATUS (this pass):
  * `elim_integer`  — PROVED from `repr_combined` (the ζ(3)-elimination algebra).
  * `dvd_lcmUpto`, `harmonic_integrality` — PROVED (self-contained arithmetic used by Lemma 3).
  * `oddIdx3`, `oddIdx3_eq_insert`, `three_notMem_oddIdx` — PROVED bookkeeping.
  * `Rn`, `Rn_eq_c`, `Rn_eq_chat`, `partialFraction_exists`, `repr_combined`
      — STATED, proofs `sorry` (the analytic heart: partial fractions + Lemma 3 assembly).
-/
import Mathlib
import Zeta5Odd.Basic
import Zeta5Odd.ZetaValues

namespace Zeta5Odd

open scoped BigOperators Nat

/-! ### The odd index set including `3` -/

/-- Odd indices from 3 to 33 — the zeta values that appear in `r_n`, `r̂_n` individually
(before the ζ(3)-elimination).  `oddIdx3 = {3} ∪ oddIdx`. -/
def oddIdx3 : Finset ℕ := (Finset.Icc 3 33).filter (fun j => Odd j)

lemma three_notMem_oddIdx : (3 : ℕ) ∉ oddIdx := by decide

lemma oddIdx3_eq_insert : oddIdx3 = insert 3 oddIdx := by decide

/-! ### `Nat.lcmUpto` divisibility and harmonic-sum integrality -/

/-- Every `ℓ` with `1 ≤ ℓ ≤ n` divides `d_n = lcm(1,…,n)`. -/
theorem dvd_lcmUpto {ℓ n : ℕ} (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ n) : ℓ ∣ Nat.lcmUpto n := by
  have hmem : ℓ ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨h1, h2⟩
  have := Finset.dvd_lcm (f := id) hmem
  simpa [Nat.lcmUpto] using this

/-- Harmonic-sum integrality (paper Lemma 3, first inclusion):
`d_n^i · Σ_{ℓ=1}^{k} 1/ℓ^i ∈ ℤ` for `0 ≤ k ≤ n`, `i ≥ 1`. -/
theorem harmonic_integrality (n i k : ℕ) (hk : k ≤ n) :
    ∃ z : ℤ, (Nat.lcmUpto n : ℝ) ^ i * (∑ ℓ ∈ Finset.Icc 1 k, (1 : ℝ) / (ℓ : ℝ) ^ i) = z := by
  refine ⟨∑ ℓ ∈ Finset.Icc 1 k, ((Nat.lcmUpto n / ℓ : ℕ) ^ i : ℤ), ?_⟩
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  obtain ⟨hℓ1, hℓk⟩ := Finset.mem_Icc.mp hℓ
  have hdvd : ℓ ∣ Nat.lcmUpto n := dvd_lcmUpto hℓ1 (hℓk.trans hk)
  have hℓ0 : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
  rw [Int.cast_pow, Int.cast_natCast, Nat.cast_div hdvd hℓ0, div_pow, mul_one_div]

/-! ### The rational function `R_n(t)` (paper e02) and its bridge to `c`, `chat`

Paper eq. (e02), first line, with `s = 2q − 1` (so the pole order at each `t = −k` is `s`):
`R_n(t) = n!^{s-5} ∏_{j=1}^n(t−j) · ∏_{j=1}^n(t+n+j) · 2^{6n} ∏_{j=1}^{3n}(t−n−½+j) / ∏_{j=0}^n (t+j)^s`. -/
noncomputable def Rn (q n : ℕ) (t : ℝ) : ℝ :=
  (n ! : ℝ) ^ (2 * q - 6)
      * (∏ j ∈ Finset.Icc 1 n, (t - (j : ℝ)))
      * (∏ j ∈ Finset.Icc 1 n, (t + (n : ℝ) + (j : ℝ)))
      * 2 ^ (6 * n)
      * (∏ j ∈ Finset.Icc 1 (3 * n), (t - (n : ℝ) - 1 / 2 + (j : ℝ)))
    / (∏ j ∈ Finset.range (n + 1), (t + (j : ℝ)) ^ (2 * q - 1))

/-- Bridge (paper: `R_n(ν) = 0` for `ν = 1,…,n`, so `r_n = Σ_{k≥0} R_n(n+1+k)`):
the `k`-th summand of `r q n` is `R_n(n+1+k)`. -/
theorem Rn_eq_c (q n k : ℕ) : Rn q n ((n : ℝ) + 1 + (k : ℝ)) = c q n k := by
  sorry

/-- Bridge for the twisted form: the `k`-th summand of `rhat q n` is `R_n(n+½+k)`. -/
theorem Rn_eq_chat (q n k : ℕ) : Rn q n ((n : ℝ) + 1 / 2 + (k : ℝ)) = chat q n k := by
  sorry

/-! ### Partial fractions with the coefficients `a_{i,k}` (paper e04 + Lemmas 1, 2) -/

/-- **Partial-fraction data (paper e04 + Lemmas 1–2).**
There is a coefficient array `a : (i,k) ↦ a_{i,k}` (`1 ≤ i ≤ s = 33`, `0 ≤ k ≤ n`) with:
  * (e04) the decomposition `R_n(t) = Σ_i Σ_k a_{i,k}/(t+k)^i` off the poles;
  * (Lemma 1) integrality `d_n^{s−i} · a_{i,k} ∈ ℤ`;
  * (Lemma 2) well-poised symmetry `a_{i,k} = (−1)^{i−1} a_{i,n−k}`. -/
theorem partialFraction_exists (n : ℕ) :
    ∃ a : ℕ → ℕ → ℝ,
      (∀ t : ℝ, (∀ k ∈ Finset.range (n + 1), t + (k : ℝ) ≠ 0) →
          Rn 17 n t
            = ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1),
                a i k / (t + (k : ℝ)) ^ i)
      ∧ (∀ i ∈ Finset.Icc 1 33, ∀ k ∈ Finset.range (n + 1),
          ∃ z : ℤ, (Nat.lcmUpto n : ℝ) ^ (33 - i) * a i k = z)
      ∧ (∀ i ∈ Finset.Icc 1 33, ∀ k ∈ Finset.range (n + 1),
          a i k = (-1) ^ (i - 1) * a i (n - k)) := by
  sorry

/-! ### Lemma 3: the ζ-representations of `r_n` and `r̂_n` (paper e07, e08)

Multiplying the paper's e07/e08 through by `d_n^{33}` and using
`d_n^{33}·a_i = d_n^i·(d_n^{33−i} a_i)` with `d_n^{33−i} a_i ∈ ℤ` (odd `i ∈ {3,…,33}`),
`d_n^{33} a_0, d_n^{33} â_0 ∈ ℤ`, and Lemma 2 (only odd `i` survive), gives integer
coefficients `B i` (shared between the two forms) and constants `B0`, `Bhat0`. -/
theorem repr_combined (n : ℕ) :
    ∃ (B : ℕ → ℤ) (B0 Bhat0 : ℤ),
      (Nat.lcmUpto n : ℝ) ^ 33 * r 17 n
          = (∑ i ∈ oddIdx3, (Nat.lcmUpto n : ℝ) ^ i * (B i : ℝ) * zetaVal i) + (B0 : ℝ)
      ∧ (Nat.lcmUpto n : ℝ) ^ 33 * rhat 17 n
          = (∑ i ∈ oddIdx3, (Nat.lcmUpto n : ℝ) ^ i * (B i : ℝ) * ((2 : ℝ) ^ i - 1) * zetaVal i)
              + (Bhat0 : ℝ) := by
  sorry

/-! ### The ζ(3)-elimination -/

/-- **Arithmetic core (paper Lemmas 1–3 + ζ(3)-elimination), `q = 17`, `s = 33`.**
`d_n^{33}·(7 r_n − r̂_n)` is an ℤ-linear combination of the odd zeta values
`ζ(5),…,ζ(33)` plus an integer constant. -/
theorem elim_integer (n : ℕ) :
    ∃ (A : ℕ → ℤ) (A0 : ℤ),
      (Nat.lcmUpto n : ℝ) ^ (33 : ℕ) * (7 * r 17 n - rhat 17 n)
        = (∑ j ∈ oddIdx, (A j : ℝ) * zetaVal j) + (A0 : ℝ) := by
  obtain ⟨B, B0, Bhat0, hr, hrh⟩ := repr_combined n
  set d : ℕ := Nat.lcmUpto n with hd
  refine ⟨fun j => (d : ℤ) ^ j * B j * (8 - 2 ^ j), 7 * B0 - Bhat0, ?_⟩
  -- Per-term combination `7·(coeff of r) − (coeff of r̂) = coeff·(8 − 2^i)`.
  have hsum :
      7 * (∑ i ∈ oddIdx3, (d : ℝ) ^ i * (B i : ℝ) * zetaVal i)
        - (∑ i ∈ oddIdx3, (d : ℝ) ^ i * (B i : ℝ) * ((2 : ℝ) ^ i - 1) * zetaVal i)
      = ∑ i ∈ oddIdx3, (d : ℝ) ^ i * (B i : ℝ) * ((8 : ℝ) - 2 ^ i) * zetaVal i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  -- Assemble `d^33·(7 r − r̂)`.
  have combine :
      (d : ℝ) ^ 33 * (7 * r 17 n - rhat 17 n)
        = (∑ i ∈ oddIdx3, (d : ℝ) ^ i * (B i : ℝ) * ((8 : ℝ) - 2 ^ i) * zetaVal i)
            + (7 * (B0 : ℝ) - (Bhat0 : ℝ)) := by
    have lhs_eq : (d : ℝ) ^ 33 * (7 * r 17 n - rhat 17 n)
        = 7 * ((d : ℝ) ^ 33 * r 17 n) - (d : ℝ) ^ 33 * rhat 17 n := by ring
    rw [lhs_eq, hr, hrh]
    linear_combination hsum
  rw [combine]
  -- Drop the `i = 3` term (it vanishes: `8 − 2^3 = 0`) and match casts.
  have hF3 : (d : ℝ) ^ 3 * (B 3 : ℝ) * ((8 : ℝ) - 2 ^ 3) * zetaVal 3 = 0 := by
    rw [show (8 : ℝ) - 2 ^ 3 = 0 by norm_num]; ring
  rw [oddIdx3_eq_insert, Finset.sum_insert three_notMem_oddIdx, hF3, zero_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  · push_cast
    ring

end Zeta5Odd
