/-
Formalization probe: Lemma 4 of W. Zudilin, "One of the odd zeta values from
ζ(5) to ζ(25) is irrational. By elementary means" (arXiv:1801.09895).

This lemma is the *only* step of the paper whose proof is not self-contained
(it delegates the localization argument to de Bruijn, "Asymptotic methods",
Section 3.4).  Per our survey, it carries essentially all the risk of the
full formalization; hence it goes first.

Throughout, s = 2q - 1 is the odd parameter of the construction (s ≥ 7,
i.e. q ≥ 4).  The paper's proof localizes the sums r_n = ∑ c_k and
r̂_n = ∑ ĉ_k in a window of width γ√n around k₀ ≈ x₀ n.  We formalize a
*weaker* localization at scale εn, which suffices because:
  * the nth-root limits absorb all subexponential factors, and
  * the ratio limit r_n / r̂_n → 1 only needs the termwise ratio
    c_k / ĉ_k ≈ f(k/n) to be within δ of f(x₀) = 1 on a window carrying
    all but an exponentially small fraction of both sums.

Proof plan (bottom of file): `sum_localizes`, `term_ratio_on_window`,
`tendsto_root_r`, `tendsto_ratio`.
-/
import Mathlib

open Filter Finset
open scoped Nat Topology

namespace Zeta5Odd

/-! ### The summands and the series -/

/-- Summand `c k = R_n(n+1+k)` of `r n`, eq. (e09) of the paper, with
`s - 5 = 2q - 6` and `s + 1 = 2q`. -/
noncomputable def c (q n k : ℕ) : ℝ :=
  (n ! : ℝ) ^ (2 * q - 6) * ((6 * n + 2 * k + 2)! : ℝ) * ((n + k)! : ℝ) ^ (2 * q) /
    (2 * ((2 * k + 1)! : ℝ) * ((2 * n + k + 1)! : ℝ) ^ (2 * q))

/-- Summand `ĉ k = R_n(n + 1/2 + k)` of `r̂ n`: the half-integer products,
written via doubled indices to stay inside `Nat.factorial`:
`∏_{j=0}^{6n} (k + (j+1)/2) = (6n+2k+1)! / ((2k)! · 2^(6n+1))` and
`∏_{j=0}^{n} (n+k+(2j+1)/2) = (∏_{j=n+k}^{2n+k} (2j+1)) / 2^(n+1)`. -/
noncomputable def chat (q n k : ℕ) : ℝ :=
  2 ^ (6 * n) * (n ! : ℝ) ^ (2 * q - 6) *
    (((6 * n + 2 * k + 1)! : ℝ) / ((2 * k)! : ℝ) / 2 ^ (6 * n + 1)) /
    ((∏ j ∈ range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ)) / 2 ^ (n + 1)) ^ (2 * q)

/-- The linear form `r n = ∑_{ν>n} R_n(ν)`. -/
noncomputable def r (q n : ℕ) : ℝ := ∑' k, c q n k

/-- The twisted linear form `r̂ n = ∑_{ν>n} R_n(ν - 1/2)`. -/
noncomputable def rhat (q n : ℕ) : ℝ := ∑' k, chat q n k

/-! ### The limit profile -/

/-- Square root of the limiting term ratio `c_{k+1}/c_k` at `k ≈ xn`. -/
noncomputable def f (q : ℕ) (x : ℝ) : ℝ := (x + 3) / x * ((x + 1) / (x + 2)) ^ q

/-- The limiting exponential rate `lim r_n^{1/n} = g x₀`. -/
noncomputable def g (q : ℕ) (x : ℝ) : ℝ :=
  2 ^ 6 * (x + 3) ^ 6 * (x + 1) ^ (2 * q) / (x + 2) ^ (4 * q)

/-! ### Elementary facts -/

theorem c_pos (q n k : ℕ) : 0 < c q n k := by
  have h₁ : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have h₂ : (0 : ℝ) < ((6 * n + 2 * k + 2)! : ℝ) := by
    exact_mod_cast (6 * n + 2 * k + 2).factorial_pos
  have h₃ : (0 : ℝ) < ((n + k)! : ℝ) := by exact_mod_cast (n + k).factorial_pos
  have h₄ : (0 : ℝ) < ((2 * k + 1)! : ℝ) := by
    exact_mod_cast (2 * k + 1).factorial_pos
  have h₅ : (0 : ℝ) < ((2 * n + k + 1)! : ℝ) := by
    exact_mod_cast (2 * n + k + 1).factorial_pos
  unfold c
  positivity

theorem chat_pos (q n k : ℕ) : 0 < chat q n k := by
  have h₁ : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have h₂ : (0 : ℝ) < ((6 * n + 2 * k + 1)! : ℝ) := by
    exact_mod_cast (6 * n + 2 * k + 1).factorial_pos
  have h₃ : (0 : ℝ) < ((2 * k)! : ℝ) := by exact_mod_cast (2 * k).factorial_pos
  have h₄ : (0 : ℝ) < ∏ j ∈ range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ) := by
    apply prod_pos
    intro j _
    exact_mod_cast Nat.succ_pos _
  unfold chat
  positivity

/-- The summands decay like `k^(6n + 1 - 2q(n+1))`; for `q ≥ 4` this is
summable (comparison with `k⁻²`). -/
theorem summable_c (q n : ℕ) (hq : 4 ≤ q) : Summable (c q n) := by
  sorry

theorem summable_chat (q n : ℕ) (hq : 4 ≤ q) : Summable (chat q n) := by
  sorry

theorem r_pos (q n : ℕ) (hq : 4 ≤ q) : 0 < r q n :=
  (summable_c q n hq).tsum_pos (fun k => (c_pos q n k).le) 0 (c_pos q n 0)

theorem rhat_pos (q n : ℕ) (hq : 4 ≤ q) : 0 < rhat q n :=
  (summable_chat q n hq).tsum_pos (fun k => (chat_pos q n k).le) 0 (chat_pos q n 0)

/-- `f` has a unique positive fixed point of level 1 (paper, proof of
Lemma 4: `f` decreases from +∞ then increases to 1⁻, so crosses 1 once). -/
theorem existsUnique_x0 (q : ℕ) (hq : 4 ≤ q) :
    ∃! x : ℝ, 0 < x ∧ f q x = 1 := by
  sorry

/-! ### Lemma 4, split into the four working pieces

All statements take the crossing point `x₀` as a hypothesis
(`existsUnique_x0` produces it), so the pieces are independent. -/

/-- Piece 1 (εn-localization): for every ε > 0, the tail of `r n` outside
the window `|k - x₀ n| ≤ εn` is exponentially negligible relative to the
whole sum.  This replaces de Bruijn's γ√n localization. -/
theorem sum_localizes (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
        (∑' k : {k : ℕ // (k : ℝ) < (x₀ - ε) * n ∨ (x₀ + ε) * n < (k : ℝ)},
          c q n k) / r q n)
      atTop (𝓝 0) := by
  sorry

/-- Piece 2 (termwise ratio on the window): uniformly over
`|k - x₀ n| ≤ εn`, the ratio `c k / ĉ k` is eventually within `δ(ε)` of 1,
where `δ(ε) → 0` with `ε`.  Needs two-sided Wallis/Stirling bounds for the
central-binomial expression (e10) of the paper. -/
theorem term_ratio_on_window (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (x₀ - ε) * n ≤ k → (k : ℝ) ≤ (x₀ + ε) * n →
      |c q n k / chat q n k - 1| ≤ δ := by
  sorry

/-- Lemma 4, first claim for `r`. -/
theorem tendsto_root_r (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    Tendsto (fun n : ℕ => r q n ^ (1 / (n : ℝ))) atTop (𝓝 (g q x₀)) := by
  sorry

/-- Lemma 4, first claim for `r̂`. -/
theorem tendsto_root_rhat (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    Tendsto (fun n : ℕ => rhat q n ^ (1 / (n : ℝ))) atTop (𝓝 (g q x₀)) := by
  sorry

/-- Lemma 4, second claim: the two linear forms are asymptotically equal.
This is what makes `7 r_n - r̂_n > 0` eventually, hence nonvanishing. -/
theorem tendsto_ratio (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    Tendsto (fun n : ℕ => r q n / rhat q n) atTop (𝓝 1) := by
  sorry

end Zeta5Odd
