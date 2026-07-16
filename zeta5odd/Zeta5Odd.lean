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
  -- Exponent gap: `2q(n+1) ≥ 6n+3+2`, so the summand decays at least like `k⁻²`.
  have hexp : 6 * n + 1 + 2 ≤ (n + 1) * (2 * q) := by nlinarith [Nat.zero_le n]
  -- Pointwise majorant `c q n k ≤ P₂ / (2 (k+1)²)` with `P₂ = n!^(2q-6)·(6n+2)^(6n+1)`.
  set P₂ : ℕ := (n !) ^ (2 * q - 6) * (6 * n + 2) ^ (6 * n + 1) with hP₂
  have hmaj : ∀ k, c q n k ≤ (P₂ : ℝ) / (2 * ((k : ℝ) + 1) ^ 2) := by
    intro k
    -- Split the two "long" factorials via `factorial_mul_ascFactorial`.
    have eA : (6 * n + 2 * k + 2)! = (2 * k + 1)! * (2 * k + 2).ascFactorial (6 * n + 1) := by
      rw [show 6 * n + 2 * k + 2 = (2 * k + 1) + (6 * n + 1) from by omega]
      exact (Nat.factorial_mul_ascFactorial (2 * k + 1) (6 * n + 1)).symm
    have eB : (2 * n + k + 1)! = (n + k)! * (n + k + 1).ascFactorial (n + 1) := by
      rw [show 2 * n + k + 1 = (n + k) + (n + 1) from by omega]
      exact (Nat.factorial_mul_ascFactorial (n + k) (n + 1)).symm
    -- Upper bound for the ascending factorial in the numerator.
    have hA : (2 * k + 2).ascFactorial (6 * n + 1)
        ≤ (6 * n + 2) ^ (6 * n + 1) * (k + 1) ^ (6 * n + 1) := by
      calc (2 * k + 2).ascFactorial (6 * n + 1)
          ≤ ((2 * k + 1) + (6 * n + 1)) ^ (6 * n + 1) :=
            Nat.ascFactorial_le_pow_add (2 * k + 1) (6 * n + 1)
        _ = (6 * n + 2 * k + 2) ^ (6 * n + 1) := by congr 1; omega
        _ ≤ ((6 * n + 2) * (k + 1)) ^ (6 * n + 1) :=
            Nat.pow_le_pow_left (by nlinarith [Nat.zero_le (n * k)]) _
        _ = (6 * n + 2) ^ (6 * n + 1) * (k + 1) ^ (6 * n + 1) := by rw [Nat.mul_pow]
    -- Lower bound for the ascending factorial in the denominator (raised to `2q`).
    have hB : (k + 1) ^ ((n + 1) * (2 * q))
        ≤ ((n + k + 1).ascFactorial (n + 1)) ^ (2 * q) := by
      calc (k + 1) ^ ((n + 1) * (2 * q))
          = ((k + 1) ^ (n + 1)) ^ (2 * q) := by rw [pow_mul]
        _ ≤ ((n + k + 1) ^ (n + 1)) ^ (2 * q) :=
            Nat.pow_le_pow_left (Nat.pow_le_pow_left (by omega) _) _
        _ ≤ ((n + k + 1).ascFactorial (n + 1)) ^ (2 * q) :=
            Nat.pow_le_pow_left (Nat.pow_succ_le_ascFactorial _ _) _
    -- Core reduced inequality (common factorial factors cancelled).
    have hcore : (2 * k + 2).ascFactorial (6 * n + 1) * (k + 1) ^ 2
        ≤ (6 * n + 2) ^ (6 * n + 1) * ((n + k + 1).ascFactorial (n + 1)) ^ (2 * q) := by
      calc (2 * k + 2).ascFactorial (6 * n + 1) * (k + 1) ^ 2
          ≤ ((6 * n + 2) ^ (6 * n + 1) * (k + 1) ^ (6 * n + 1)) * (k + 1) ^ 2 :=
            Nat.mul_le_mul_right _ hA
        _ = (6 * n + 2) ^ (6 * n + 1) * (k + 1) ^ (6 * n + 1 + 2) := by rw [mul_assoc, ← pow_add]
        _ ≤ (6 * n + 2) ^ (6 * n + 1) * (k + 1) ^ ((n + 1) * (2 * q)) :=
            Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_right (by omega) hexp)
        _ ≤ (6 * n + 2) ^ (6 * n + 1) * ((n + k + 1).ascFactorial (n + 1)) ^ (2 * q) :=
            Nat.mul_le_mul (le_refl _) hB
    -- The full Nat inequality after cross-multiplication.
    have keyN2 : (n !) ^ (2 * q - 6) * (6 * n + 2 * k + 2)! * (n + k)! ^ (2 * q) * (2 * (k + 1) ^ 2)
        ≤ P₂ * (2 * (2 * k + 1)! * (2 * n + k + 1)! ^ (2 * q)) := by
      rw [eA, eB, hP₂]
      calc (n !) ^ (2 * q - 6) * ((2 * k + 1)! * (2 * k + 2).ascFactorial (6 * n + 1))
              * (n + k)! ^ (2 * q) * (2 * (k + 1) ^ 2)
          = (2 * (n !) ^ (2 * q - 6) * (2 * k + 1)! * (n + k)! ^ (2 * q))
              * ((2 * k + 2).ascFactorial (6 * n + 1) * (k + 1) ^ 2) := by ring
        _ ≤ (2 * (n !) ^ (2 * q - 6) * (2 * k + 1)! * (n + k)! ^ (2 * q))
              * ((6 * n + 2) ^ (6 * n + 1) * ((n + k + 1).ascFactorial (n + 1)) ^ (2 * q)) :=
            Nat.mul_le_mul (le_refl _) hcore
        _ = (n !) ^ (2 * q - 6) * (6 * n + 2) ^ (6 * n + 1)
              * (2 * (2 * k + 1)! * ((n + k)! * (n + k + 1).ascFactorial (n + 1)) ^ (2 * q)) := by
            rw [mul_pow]; ring
    -- Transfer to ℝ and finish.
    rw [c, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (n ! : ℝ) ^ (2 * q - 6) * ((6 * n + 2 * k + 2)! : ℝ) * ((n + k)! : ℝ) ^ (2 * q)
            * (2 * ((k : ℝ) + 1) ^ 2)
        = (((n !) ^ (2 * q - 6) * (6 * n + 2 * k + 2)! * (n + k)! ^ (2 * q)
            * (2 * (k + 1) ^ 2) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((P₂ * (2 * (2 * k + 1)! * (2 * n + k + 1)! ^ (2 * q)) : ℕ) : ℝ) := by
            exact_mod_cast keyN2
      _ = (P₂ : ℝ) * (2 * ((2 * k + 1)! : ℝ) * ((2 * n + k + 1)! : ℝ) ^ (2 * q)) := by
            push_cast; ring
  -- Majorant is summable (`p`-series with `p = 2`).
  have hsum : Summable (fun k : ℕ => (P₂ : ℝ) / (2 * ((k : ℝ) + 1) ^ 2)) := by
    have h1 : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
      have h0 : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      refine ((summable_nat_add_iff 1).mpr h0).congr (fun k => ?_)
      push_cast; ring
    refine (h1.mul_left ((P₂ : ℝ) / 2)).congr (fun k => ?_)
    rw [div_mul_div_comm, mul_one]
  exact hsum.of_nonneg_of_le (fun k => (c_pos q n k).le) hmaj

theorem summable_chat (q n : ℕ) (hq : 4 ≤ q) : Summable (chat q n) := by
  have hexp : 6 * n + 1 + 2 ≤ (n + 1) * (2 * q) := by nlinarith [Nat.zero_le n]
  -- `k`-independent positive constant (all the `2`-powers and `n!` factors).
  set KE : ℝ := 2 ^ (6 * n) * (n ! : ℝ) ^ (2 * q - 6) * (2 ^ (n + 1)) ^ (2 * q) / 2 ^ (6 * n + 1)
    with hKE
  have hKE_pos : 0 < KE := by rw [hKE]; positivity
  set Cmaj : ℝ := KE * (((6 * n + 2) ^ (6 * n + 1) : ℕ) : ℝ) with hCmaj
  have hCmaj_nonneg : 0 ≤ Cmaj := by rw [hCmaj]; positivity
  have hmaj : ∀ k, chat q n k ≤ Cmaj / ((k : ℝ) + 1) ^ 2 := by
    intro k
    -- Rewrite `chat` as `KE · (AR) / PR^(2q)`.
    have hchat : chat q n k
        = KE * (((6 * n + 2 * k + 1)! : ℝ) / ((2 * k)! : ℝ))
            / (∏ j ∈ range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ)) ^ (2 * q) := by
      rw [hKE, chat, div_pow]; field_simp
    -- Upper bound for the numerator ratio `AR`.
    have hAR : ((6 * n + 2 * k + 1)! : ℝ) / ((2 * k)! : ℝ)
        ≤ (((6 * n + 2) ^ (6 * n + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) ^ (6 * n + 1) := by
      have hnat : (6 * n + 2 * k + 1)!
          ≤ (6 * n + 2) ^ (6 * n + 1) * (k + 1) ^ (6 * n + 1) * (2 * k)! := by
        calc (6 * n + 2 * k + 1)!
            = (2 * k)! * (2 * k + 1).ascFactorial (6 * n + 1) := by
              rw [show 6 * n + 2 * k + 1 = (2 * k) + (6 * n + 1) from by omega]
              exact (Nat.factorial_mul_ascFactorial (2 * k) (6 * n + 1)).symm
          _ ≤ (2 * k)! * ((6 * n + 2) ^ (6 * n + 1) * (k + 1) ^ (6 * n + 1)) := by
              apply Nat.mul_le_mul (le_refl _)
              calc (2 * k + 1).ascFactorial (6 * n + 1)
                  ≤ ((2 * k) + (6 * n + 1)) ^ (6 * n + 1) :=
                    Nat.ascFactorial_le_pow_add (2 * k) (6 * n + 1)
                _ = (6 * n + 2 * k + 1) ^ (6 * n + 1) := by congr 1; omega
                _ ≤ ((6 * n + 2) * (k + 1)) ^ (6 * n + 1) :=
                    Nat.pow_le_pow_left (by nlinarith [Nat.zero_le (n * k)]) _
                _ = (6 * n + 2) ^ (6 * n + 1) * (k + 1) ^ (6 * n + 1) := by rw [Nat.mul_pow]
          _ = (6 * n + 2) ^ (6 * n + 1) * (k + 1) ^ (6 * n + 1) * (2 * k)! := by ring
      rw [div_le_iff₀ (by positivity)]
      calc ((6 * n + 2 * k + 1)! : ℝ)
          ≤ (((6 * n + 2) ^ (6 * n + 1) * (k + 1) ^ (6 * n + 1) * (2 * k)! : ℕ) : ℝ) := by
            exact_mod_cast hnat
        _ = (((6 * n + 2) ^ (6 * n + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) ^ (6 * n + 1) * ((2 * k)! : ℝ) := by
            push_cast; ring
    -- Lower bound for the denominator product `PR`.
    have hPR : ((k : ℝ) + 1) ^ (n + 1)
        ≤ ∏ j ∈ range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ) := by
      rw [show ((k : ℝ) + 1) ^ (n + 1) = ∏ _j ∈ range (n + 1), ((k : ℝ) + 1) by
        rw [prod_const, card_range]]
      apply Finset.prod_le_prod
      · intro i _; positivity
      · intro i _; push_cast; nlinarith [Nat.zero_le i, Nat.zero_le n]
    -- Denominator lower bound raised to `2q`.
    have hdenb : ((k : ℝ) + 1) ^ ((n + 1) * (2 * q))
        ≤ (∏ j ∈ range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ)) ^ (2 * q) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hPR (2 * q)
    -- Assemble.
    rw [hchat]
    calc KE * (((6 * n + 2 * k + 1)! : ℝ) / ((2 * k)! : ℝ))
            / (∏ j ∈ range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ)) ^ (2 * q)
        ≤ KE * ((((6 * n + 2) ^ (6 * n + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) ^ (6 * n + 1))
            / ((k : ℝ) + 1) ^ ((n + 1) * (2 * q)) :=
          div_le_div₀ (mul_nonneg hKE_pos.le (by positivity))
            (mul_le_mul_of_nonneg_left hAR hKE_pos.le) (by positivity) hdenb
      _ = Cmaj * (((k : ℝ) + 1) ^ (6 * n + 1) / ((k : ℝ) + 1) ^ ((n + 1) * (2 * q))) := by
            rw [hCmaj]; ring
      _ ≤ Cmaj * (1 / ((k : ℝ) + 1) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hCmaj_nonneg
            rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
            exact pow_le_pow_right₀ (by simp) hexp
      _ = Cmaj / ((k : ℝ) + 1) ^ 2 := by ring
  -- The majorant is summable.
  have hsum : Summable (fun k : ℕ => Cmaj / ((k : ℝ) + 1) ^ 2) := by
    have h1 : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
      have h0 : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      refine ((summable_nat_add_iff 1).mpr h0).congr (fun k => ?_)
      push_cast; ring
    refine (h1.mul_left Cmaj).congr (fun k => ?_)
    rw [mul_one_div]
  exact hsum.of_nonneg_of_le (fun k => (chat_pos q n k).le) hmaj

theorem r_pos (q n : ℕ) (hq : 4 ≤ q) : 0 < r q n :=
  (summable_c q n hq).tsum_pos (fun k => (c_pos q n k).le) 0 (c_pos q n 0)

theorem rhat_pos (q n : ℕ) (hq : 4 ≤ q) : 0 < rhat q n :=
  (summable_chat q n hq).tsum_pos (fun k => (chat_pos q n k).le) 0 (chat_pos q n 0)

/-- `f` has a unique positive fixed point of level 1 (paper, proof of
Lemma 4: `f` decreases from +∞ then increases to 1⁻, so crosses 1 once). -/
theorem existsUnique_x0 (q : ℕ) (hq : 4 ≤ q) :
    ∃! x : ℝ, 0 < x ∧ f q x = 1 := by
  set qr : ℝ := (q : ℝ) with hqr
  have hqr4 : (4 : ℝ) ≤ qr := by rw [hqr]; exact_mod_cast hq
  -- N and its logarithmic-derivative role.
  set N : ℝ → ℝ := fun x => (qr - 3) * x ^ 2 + 3 * (qr - 3) * x - 6 with hN
  set L : ℝ → ℝ := fun x =>
    Real.log (x + 3) - Real.log x + qr * (Real.log (x + 1) - Real.log (x + 2)) with hL
  -- f x = 1 ↔ L x = 0, for x > 0.
  have hfpos : ∀ x : ℝ, 0 < x → 0 < f q x := by
    intro x hx
    have : (0:ℝ) < (x+1)/(x+2) := by positivity
    unfold f; positivity
  have hLlog : ∀ x : ℝ, 0 < x → Real.log (f q x) = L x := by
    intro x hx
    have h1 : (0:ℝ) < x + 3 := by linarith
    have h2 : (0:ℝ) < x + 1 := by linarith
    have h3 : (0:ℝ) < x + 2 := by linarith
    unfold f
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_div (by positivity) (by positivity), hL]
  have hf1 : ∀ x : ℝ, 0 < x → (f q x = 1 ↔ L x = 0) := by
    intro x hx
    rw [← hLlog x hx]
    constructor
    · intro h; rw [h]; exact Real.log_one
    · intro h; exact Real.eq_one_of_pos_of_log_eq_zero (hfpos x hx) h
  -- Derivative of L: sign given by N.
  have hLderiv : ∀ x : ℝ, 0 < x →
      HasDerivAt L (N x / (x * (x + 1) * (x + 2) * (x + 3))) x := by
    intro x hx
    have e3 : HasDerivAt (fun y : ℝ => Real.log (y + 3)) (1 / (x + 3)) x := by
      have := ((hasDerivAt_id x).add_const (3:ℝ)).log (by positivity)
      simpa using this
    have e0 : HasDerivAt (fun y : ℝ => Real.log y) (1 / x) x := by
      simpa using (Real.hasDerivAt_log (by positivity : x ≠ 0))
    have e1 : HasDerivAt (fun y : ℝ => Real.log (y + 1)) (1 / (x + 1)) x := by
      have := ((hasDerivAt_id x).add_const (1:ℝ)).log (by positivity)
      simpa using this
    have e2 : HasDerivAt (fun y : ℝ => Real.log (y + 2)) (1 / (x + 2)) x := by
      have := ((hasDerivAt_id x).add_const (2:ℝ)).log (by positivity)
      simpa using this
    have hd := (e3.sub e0).add ((e1.sub e2).const_mul qr)
    have heq : 1 / (x + 3) - 1 / x + qr * (1 / (x + 1) - 1 / (x + 2))
        = N x / (x * (x + 1) * (x + 2) * (x + 3)) := by
      rw [hN]; field_simp; ring
    rw [heq] at hd
    exact hd
  -- N is strictly increasing on [0, ∞).
  have hNmono : StrictMonoOn N (Set.Ici 0) := by
    intro a ha b hb hab
    simp only [Set.mem_Ici] at ha hb
    simp only [hN]
    nlinarith [mul_pos (mul_pos (show (0:ℝ) < qr - 3 by linarith)
      (show (0:ℝ) < b - a by linarith)) (show (0:ℝ) < b + a + 3 by linarith)]
  -- x₁ : the unique positive root of N in (0,3).
  have hNcont : Continuous N := by rw [hN]; fun_prop
  have hN0 : N 0 = -6 := by rw [hN]; ring
  have hN3 : 0 < N 3 := by simp only [hN]; nlinarith [hqr4]
  obtain ⟨x₁, hx₁mem, hx₁0⟩ :
      ∃ x ∈ Set.Icc (0:ℝ) 3, N x = 0 := by
    have hmem : (0:ℝ) ∈ Set.Icc (N 0) (N 3) := by
      rw [Set.mem_Icc, hN0]; exact ⟨by norm_num, hN3.le⟩
    obtain ⟨x, hx, hxeq⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 3)
      hNcont.continuousOn hmem
    exact ⟨x, hx, hxeq⟩
  have hx₁pos : 0 < x₁ := by
    rcases lt_or_eq_of_le hx₁mem.1 with h | h
    · exact h
    · exfalso; rw [← h] at hx₁0; rw [hN0] at hx₁0; norm_num at hx₁0
  -- Sign of N relative to x₁.
  have hNneg : ∀ x : ℝ, 0 < x → x < x₁ → N x < 0 := by
    intro x hx hxx₁
    have := hNmono (Set.mem_Ici.mpr hx.le) (Set.mem_Ici.mpr hx₁pos.le) hxx₁
    rw [hx₁0] at this; exact this
  have hNpos : ∀ x : ℝ, x₁ < x → 0 < N x := by
    intro x hxx₁
    have := hNmono (Set.mem_Ici.mpr hx₁pos.le) (Set.mem_Ici.mpr (by linarith : (0:ℝ) ≤ x)) hxx₁
    rw [hx₁0] at this; exact this
  -- helper: positive denominator
  have hden : ∀ x : ℝ, 0 < x → 0 < x * (x + 1) * (x + 2) * (x + 3) := by
    intro x hx; have := hx; positivity
  -- L is strictly decreasing on (0, x₁).
  have hLcont1 : ContinuousOn L (Set.Ioo 0 x₁) :=
    fun x hx => (hLderiv x hx.1).continuousAt.continuousWithinAt
  have hLanti : StrictAntiOn L (Set.Ioo 0 x₁) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo 0 x₁) hLcont1
    rw [interior_Ioo]
    intro x hx
    rw [(hLderiv x hx.1).deriv]
    exact div_neg_of_neg_of_pos (hNneg x hx.1 hx.2) (hden x hx.1)
  -- L is strictly increasing on [x₁, ∞).
  have hLcont2 : ContinuousOn L (Set.Ici x₁) :=
    fun x hx => (hLderiv x (lt_of_lt_of_le hx₁pos hx)).continuousAt.continuousWithinAt
  have hLmono : StrictMonoOn L (Set.Ici x₁) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici x₁) hLcont2
    rw [interior_Ici]
    intro x hx
    rw [(hLderiv x (lt_trans hx₁pos hx)).deriv]
    exact div_pos (hNpos x hx) (hden x (lt_trans hx₁pos hx))
  -- L → 0 at +∞.
  have hLtend0 : Tendsto L atTop (𝓝 0) := by
    have key : ∀ a b : ℝ,
        Tendsto (fun x : ℝ => Real.log (x + a) - Real.log (x + b)) atTop (𝓝 0) := by
      intro a b
      have hr : Tendsto (fun x : ℝ => (x + a) / (x + b)) atTop (𝓝 1) := by
        have h0 : Tendsto (fun x : ℝ => (a - b) / (x + b)) atTop (𝓝 0) :=
          Tendsto.div_atTop tendsto_const_nhds
            (tendsto_atTop_add_const_right atTop b tendsto_id)
        have h1 : Tendsto (fun x : ℝ => 1 + (a - b) / (x + b)) atTop (𝓝 1) := by
          simpa using h0.const_add 1
        refine h1.congr' ?_
        filter_upwards [eventually_gt_atTop (-b)] with x hx
        have hxb : x + b ≠ 0 := ne_of_gt (by linarith)
        field_simp
        ring
      have hc := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hr
      rw [Real.log_one] at hc
      refine hc.congr' ?_
      filter_upwards [eventually_gt_atTop (max (-a) (-b))] with x hx
      rw [max_lt_iff] at hx
      exact Real.log_div (ne_of_gt (by linarith [hx.1] : (0:ℝ) < x + a))
        (ne_of_gt (by linarith [hx.2] : (0:ℝ) < x + b))
    have hA : Tendsto (fun x : ℝ => Real.log (x + 3) - Real.log x) atTop (𝓝 0) := by
      refine (key 3 0).congr (fun x => ?_); rw [add_zero]
    have hB := ((key 1 2).const_mul qr)
    have := hA.add hB
    simp only [mul_zero, add_zero] at this
    exact this.congr (fun x => by simp only [hL])
  -- L < 0 on [x₁, ∞).
  have hLneg : ∀ x : ℝ, x₁ ≤ x → L x < 0 := by
    intro x hx
    have h1 : L x < L (x + 1) :=
      hLmono (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (by linarith)) (by linarith)
    have h2 : L (x + 1) ≤ 0 := by
      refine ge_of_tendsto hLtend0 ?_
      filter_upwards [eventually_ge_atTop (x + 1)] with y hy
      exact hLmono.monotoneOn (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) hy
    linarith
  -- L → +∞ at 0⁺.
  have hLtop : Tendsto L (𝓝[>] (0:ℝ)) atTop := by
    have tc : ∀ c : ℝ, Tendsto (fun x : ℝ => x + c) (𝓝[>] (0:ℝ)) (𝓝 c) := by
      intro c
      have h : Tendsto (fun x : ℝ => x + c) (𝓝 (0:ℝ)) (𝓝 (0 + c)) :=
        (by fun_prop : Continuous (fun x : ℝ => x + c)).tendsto 0
      rw [zero_add] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hbr : Tendsto (fun x : ℝ => Real.log (x + 3) + qr * Real.log (x + 1) - qr * Real.log (x + 2))
        (𝓝[>] (0:ℝ)) (𝓝 (Real.log 3 + qr * Real.log 1 - qr * Real.log 2)) := by
      have c3 : Tendsto (fun x : ℝ => Real.log (x + 3)) (𝓝[>] (0:ℝ)) (𝓝 (Real.log 3)) :=
        (Real.continuousAt_log (by norm_num)).tendsto.comp (tc 3)
      have c1 : Tendsto (fun x : ℝ => Real.log (x + 1)) (𝓝[>] (0:ℝ)) (𝓝 (Real.log 1)) :=
        (Real.continuousAt_log (by norm_num)).tendsto.comp (tc 1)
      have c2 : Tendsto (fun x : ℝ => Real.log (x + 2)) (𝓝[>] (0:ℝ)) (𝓝 (Real.log 2)) :=
        (Real.continuousAt_log (by norm_num)).tendsto.comp (tc 2)
      exact (c3.add (c1.const_mul qr)).sub (c2.const_mul qr)
    have hneg : Tendsto (fun x : ℝ => -Real.log x) (𝓝[>] (0:ℝ)) atTop :=
      tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
    have := hneg.atTop_add hbr
    exact this.congr (fun x => by simp only [hL]; ring)
  -- Existence via IVT.
  have hf1eval : f q 1 = 4 * (2 / 3 : ℝ) ^ q := by unfold f; norm_num
  have hf1lt1 : f q 1 < 1 := by
    rw [hf1eval]
    have hp : (2 / 3 : ℝ) ^ q ≤ (2 / 3 : ℝ) ^ 4 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
    nlinarith [hp, pow_nonneg (by norm_num : (0:ℝ) ≤ 2/3) q]
  have hL1 : L 1 < 0 := by
    rw [← hLlog 1 one_pos]; exact Real.log_neg (hfpos 1 one_pos) hf1lt1
  obtain ⟨a, haL, ha0, ha1⟩ : ∃ a, 0 < L a ∧ 0 < a ∧ a < 1 := by
    have hev : ∀ᶠ x in 𝓝[>] (0:ℝ), 0 < L x := hLtop.eventually (eventually_gt_atTop 0)
    have hmem : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) :=
      inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num)))
    obtain ⟨a, ha1, ha2⟩ := (hev.and (Filter.eventually_of_mem hmem (fun x hx => hx))).exists
    exact ⟨a, ha1, ha2.1, ha2.2⟩
  have hLconta1 : ContinuousOn L (Set.Icc a 1) :=
    fun x hx => (hLderiv x (lt_of_lt_of_le ha0 hx.1)).continuousAt.continuousWithinAt
  obtain ⟨c, hcmem, hLc⟩ : ∃ c ∈ Set.Icc a 1, L c = 0 := by
    have hmem0 : (0:ℝ) ∈ Set.Icc (L 1) (L a) := ⟨hL1.le, haL.le⟩
    obtain ⟨c, hc, hLc⟩ := intermediate_value_Icc' ha1.le hLconta1 hmem0
    exact ⟨c, hc, hLc⟩
  have hc0 : 0 < c := lt_of_lt_of_le ha0 hcmem.1
  -- Uniqueness.
  refine ⟨c, ⟨hc0, (hf1 c hc0).mpr hLc⟩, ?_⟩
  rintro y ⟨hy0, hfy⟩
  have hLy : L y = 0 := (hf1 y hy0).mp hfy
  have hyx₁ : y < x₁ := by
    by_contra h; push_neg at h; exact absurd hLy (ne_of_lt (hLneg y h))
  have hcx₁ : c < x₁ := by
    by_contra h; push_neg at h; exact absurd hLc (ne_of_lt (hLneg c h))
  exact hLanti.injOn ⟨hy0, hyx₁⟩ ⟨hc0, hcx₁⟩ (hLy.trans hLc.symm)


/-! ### Two-sided central-binomial bound (Wallis/Stirling)

A reusable constant-factor two-sided bound on `C(2m, m)`, derived from Mathlib's
`Stirling.stirlingSeq`.  This is the analytic input pitfall 4 flags as needed for
the termwise ratio `c/ĉ` (the paper's central-binomial expression, eq. (e10)). -/
section CentralBinom
open Real Stirling

/-- Mathlib's `stirlingSeq` (`√π ≤ stirlingSeq n ≤ e/√2` for `n ≥ 1`). -/
theorem centralBinom_two_sided (m : ℕ) (hm : 1 ≤ m) :
    2 * √π / exp 1 ^ 2 * (4 ^ m / √m) ≤ (Nat.centralBinom m : ℝ) ∧
    (Nat.centralBinom m : ℝ) ≤ exp 1 / (√2 * π) * (4 ^ m / √m) := by
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have he : (0:ℝ) < exp 1 := exp_pos 1
  have hsm : (0:ℝ) < √m := Real.sqrt_pos.mpr hmR
  set Dm : ℝ := √(2 * (m:ℝ)) * ((m:ℝ) / exp 1) ^ m with hDmdef
  set D2m : ℝ := √(2 * ((2 * m : ℕ) : ℝ)) * (((2 * m : ℕ) : ℝ) / exp 1) ^ (2 * m) with hD2mdef
  have hDm_pos : 0 < Dm := by rw [hDmdef]; positivity
  have hD2m_pos : 0 < D2m := by
    rw [hD2mdef]; apply mul_pos
    · apply Real.sqrt_pos.mpr; positivity
    · positivity
  -- factorial = stirlingSeq * D
  have hmfac : (m ! : ℝ) = stirlingSeq m * Dm := by
    rw [stirlingSeq, hDmdef]; field_simp
  have h2mfac : ((2 * m)! : ℝ) = stirlingSeq (2 * m) * D2m := by
    rw [stirlingSeq, hD2mdef]
    push_cast
    field_simp
  -- key: D2m = Dm^2 * (4^m / √m)
  have hs2 : (√(2 * (m:ℝ))) ^ 2 = 2 * (m:ℝ) := Real.sq_sqrt (by positivity)
  have hs4 : √(2 * ((2 * m : ℕ) : ℝ)) = 2 * √m := by
    have : (2 * ((2 * m : ℕ) : ℝ)) = 4 * (m:ℝ) := by push_cast; ring
    rw [this, Real.sqrt_mul (by norm_num) (m:ℝ),
      show √(4:ℝ) = 2 from by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hpow : (((2 * m : ℕ) : ℝ) / exp 1) ^ (2 * m)
      = 4 ^ m * ((m:ℝ) / exp 1) ^ (2 * m) := by
    have hb : ((2 * m : ℕ) : ℝ) / exp 1 = 2 * ((m:ℝ) / exp 1) := by push_cast; ring
    rw [hb, mul_pow, pow_mul, show (2:ℝ) ^ 2 = 4 by norm_num]
  have hDDaux : D2m * √m = Dm ^ 2 * 4 ^ m := by
    rw [hD2mdef, hDmdef, hs4, hpow, mul_pow, hs2]
    linear_combination (2 * 4 ^ m * ((m:ℝ) / exp 1) ^ (2 * m)) * Real.sq_sqrt hmR.le
  have hDD : D2m = Dm ^ 2 * (4 ^ m / √m) := by
    rw [← mul_div_assoc, eq_div_iff (ne_of_gt hsm)]; exact hDDaux
  -- two-sided bounds on the Stirling sequence at m and 2m
  have hpi : 0 < √π := Real.sqrt_pos.mpr pi_pos
  have hA_lo : √π ≤ stirlingSeq (2 * m) := sqrt_pi_le_stirlingSeq (by positivity)
  have hB_lo : √π ≤ stirlingSeq m := sqrt_pi_le_stirlingSeq (by omega)
  have hApos : 0 < stirlingSeq (2 * m) := lt_of_lt_of_le hpi hA_lo
  have hBpos : 0 < stirlingSeq m := lt_of_lt_of_le hpi hB_lo
  have hA_hi : stirlingSeq (2 * m) ≤ exp 1 / √2 := by
    have h := stirlingSeq'_antitone (Nat.zero_le (2 * m - 1))
    simp only [Function.comp, Nat.succ_eq_add_one, Nat.zero_add] at h
    rwa [show 2 * m - 1 + 1 = 2 * m by omega, stirlingSeq_one] at h
  have hB_hi : stirlingSeq m ≤ exp 1 / √2 := by
    have h := stirlingSeq'_antitone (Nat.zero_le (m - 1))
    simp only [Function.comp, Nat.succ_eq_add_one, Nat.zero_add] at h
    rwa [show m - 1 + 1 = m by omega, stirlingSeq_one] at h
  -- the exact profile identity
  have hident : (Nat.centralBinom m : ℝ)
      = stirlingSeq (2 * m) / stirlingSeq m ^ 2 * (4 ^ m / √m) := by
    have hcb : (Nat.centralBinom m : ℝ) * ((m ! : ℝ) * (m ! : ℝ)) = ((2 * m)! : ℝ) := by
      have h := Nat.choose_mul_factorial_mul_factorial
        (Nat.le_mul_of_pos_left m (by norm_num : 0 < 2))
      rw [show 2 * m - m = m by omega] at h
      rw [Nat.centralBinom_eq_two_mul_choose]
      have h2 : ((2 * m).choose m * m ! * m ! : ℕ) = ((2 * m)! : ℕ) := h
      push_cast [← h2]; ring
    rw [h2mfac, hDD, hmfac] at hcb
    -- hcb : centralBinom * ((B*Dm)*(B*Dm)) = A*(Dm^2*(4^m/√m))
    rw [div_mul_eq_mul_div, eq_div_iff (pow_pos hBpos 2).ne']
    apply mul_right_cancel₀ (pow_pos hDm_pos 2).ne'
    linear_combination hcb
  -- Derive the two-sided inequalities.
  have hKpos : 0 < (4:ℝ) ^ m / √m := by positivity
  have hBsq : stirlingSeq m ^ 2 ≤ exp 1 ^ 2 / 2 := by
    have he2 : (exp 1 / √2) ^ 2 = exp 1 ^ 2 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
    rw [← he2]; exact pow_le_pow_left₀ hBpos.le hB_hi 2
  have hBsq_lo : π ≤ stirlingSeq m ^ 2 := by
    have := pow_le_pow_left₀ hpi.le hB_lo 2
    rwa [Real.sq_sqrt pi_pos.le] at this
  have hA_hi' : stirlingSeq (2 * m) * √2 ≤ exp 1 := (le_div_iff₀ (by norm_num)).mp hA_hi
  refine ⟨?_, ?_⟩
  · rw [hident]
    apply mul_le_mul_of_nonneg_right _ hKpos.le
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hBsq (by positivity : (0:ℝ) ≤ 2 * √π),
      mul_le_mul_of_nonneg_right hA_lo (by positivity : (0:ℝ) ≤ exp 1 ^ 2)]
  · rw [hident]
    apply mul_le_mul_of_nonneg_right _ hKpos.le
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hA_hi' (by positivity : (0:ℝ) ≤ π),
      mul_le_mul_of_nonneg_left hBsq_lo (le_of_lt (exp_pos 1))]


end CentralBinom

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
