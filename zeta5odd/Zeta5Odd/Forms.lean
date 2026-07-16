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
  * `Rn_eq_c`, `Rn_eq_chat` — PROVED for `1 ≤ q` (the whole factorial reduction; see the
      helper lemmas `prod_range_shift`, `prod_range_odd`, `prod_range_odd3`, etc.).  The
      `q = 0` case of each is `sorry`: it is genuinely FALSE there (the `ℕ`-truncated
      exponents `2*q-1 = 0` in `Rn` vs `2*q = 0` in `c`/`chat` break `(2q-1)+1 = 2q`;
      e.g. `Rn 0 0 2 = 1 ≠ 2 = c 0 0 1`).  These theorems are only ever applied at `q = 17`.
  * `Rn`, `partialFraction_exists`, `repr_combined`
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

/-! #### Mechanical product-to-factorial helper lemmas -/

private lemma fact_cast_ne (a : ℕ) : (a ! : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)

/-- Ascending integer product `(a+1)(a+2)⋯(a+m) = (a+m)!/a!`. -/
private lemma prod_range_shift (a m : ℕ) :
    ∏ i ∈ Finset.range m, ((a : ℝ) + 1 + (i : ℝ)) = ((a + m)! : ℝ) / (a ! : ℝ) := by
  have ha : (a ! : ℝ) ≠ 0 := fact_cast_ne a
  induction m with
  | zero =>
    simp only [Finset.prod_range_zero, Nat.add_zero]
    rw [div_self ha]
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    have hfac : ((a + (m + 1))! : ℝ) = ((a + m + 1 : ℕ) : ℝ) * ((a + m)! : ℝ) := by
      rw [show a + (m + 1) = (a + m) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
    rw [hfac]; field_simp; push_cast; ring

/-- Odd product `(2k+1)(2k+3)⋯(2k+2m-1) = (2k+2m)!·k!/(2^m·(k+m)!·(2k)!)`. -/
private lemma prod_range_odd (k m : ℕ) :
    ∏ i ∈ Finset.range m, ((2 * k + 2 * i + 1 : ℕ) : ℝ)
      = ((2 * k + 2 * m)! : ℝ) * (k ! : ℝ)
          / (2 ^ m * ((k + m)! : ℝ) * ((2 * k)! : ℝ)) := by
  induction m with
  | zero =>
    simp only [Finset.prod_range_zero, Nat.mul_zero, Nat.add_zero, pow_zero, one_mul]
    rw [mul_comm ((2 * k)! : ℝ) (k ! : ℝ),
      div_self (mul_ne_zero (fact_cast_ne k) (fact_cast_ne (2 * k)))]
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    have e1 : ((2 * k + 2 * (m + 1))! : ℝ)
        = ((2 * k + 2 * m + 2 : ℕ) : ℝ) * ((2 * k + 2 * m + 1 : ℕ) : ℝ)
            * ((2 * k + 2 * m)! : ℝ) := by
      rw [show 2 * k + 2 * (m + 1) = (2 * k + 2 * m + 1) + 1 from by ring, Nat.factorial_succ,
        Nat.factorial_succ]; push_cast; ring
    have e2 : ((k + (m + 1))! : ℝ) = ((k + m + 1 : ℕ) : ℝ) * ((k + m)! : ℝ) := by
      rw [show k + (m + 1) = (k + m) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
    rw [e1, e2, pow_succ]
    have h1 : ((k + m)! : ℝ) ≠ 0 := fact_cast_ne _
    have h2 : ((2 * k)! : ℝ) ≠ 0 := fact_cast_ne _
    have h3 : ((k + m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring

/-- Odd product `(2k+3)(2k+5)⋯(2k+2m+1) = (2k+2m+1)!·k!/(2^m·(k+m)!·(2k+1)!)`. -/
private lemma prod_range_odd3 (k m : ℕ) :
    ∏ i ∈ Finset.range m, ((2 * k + 2 * i + 3 : ℕ) : ℝ)
      = ((2 * k + 2 * m + 1)! : ℝ) * (k ! : ℝ)
          / (2 ^ m * ((k + m)! : ℝ) * ((2 * k + 1)! : ℝ)) := by
  induction m with
  | zero =>
    simp only [Finset.prod_range_zero, Nat.mul_zero, Nat.add_zero, pow_zero, one_mul]
    rw [mul_comm ((2 * k + 1)! : ℝ) (k ! : ℝ),
      div_self (mul_ne_zero (fact_cast_ne k) (fact_cast_ne (2 * k + 1)))]
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    have e1 : ((2 * k + 2 * (m + 1) + 1)! : ℝ)
        = ((2 * k + 2 * m + 3 : ℕ) : ℝ) * ((2 * k + 2 * m + 2 : ℕ) : ℝ)
            * ((2 * k + 2 * m + 1)! : ℝ) := by
      rw [show 2 * k + 2 * (m + 1) + 1 = (2 * k + 2 * m + 2) + 1 from by ring, Nat.factorial_succ,
        Nat.factorial_succ]; push_cast; ring
    have e2 : ((k + (m + 1))! : ℝ) = ((k + m + 1 : ℕ) : ℝ) * ((k + m)! : ℝ) := by
      rw [show k + (m + 1) = (k + m) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
    rw [e1, e2, pow_succ]
    have h1 : ((k + m)! : ℝ) ≠ 0 := fact_cast_ne _
    have h2 : ((2 * k + 1)! : ℝ) ≠ 0 := fact_cast_ne _
    have h3 : ((k + m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring

/-- Reflect a product over `Icc 1 n`: reindex `j ↦ n - i`. -/
private lemma prod_Icc_one_reflect (n : ℕ) (f : ℕ → ℝ) :
    ∏ j ∈ Finset.Icc 1 n, f j = ∏ i ∈ Finset.range n, f (n - i) := by
  rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) from by
        ext x; rw [Finset.mem_Icc, Finset.mem_Ico]; omega,
    Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel]
  rw [← Finset.prod_range_reflect (fun i => f (n - i)) n]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  congr 1
  omega

/-- Convert an `Icc 1 n` product to a `range n` product (`j ↦ 1 + i`). -/
private lemma prod_Icc_one_range (n : ℕ) (f : ℕ → ℝ) :
    ∏ j ∈ Finset.Icc 1 n, f j = ∏ i ∈ Finset.range n, f (1 + i) := by
  rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) from by
        ext x; rw [Finset.mem_Icc, Finset.mem_Ico]; omega,
    Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel]

/-- Bridge (paper: `R_n(ν) = 0` for `ν = 1,…,n`, so `r_n = Σ_{k≥0} R_n(n+1+k)`):
the `k`-th summand of `r q n` is `R_n(n+1+k)`.

Note: the identity requires `1 ≤ q` (equivalently the paper's `s = 2q-1 ≥ 1`).
At `q = 0` the `ℕ`-truncated exponents `2*q-1 = 0` (in `Rn`) and `2*q = 0` (in `c`)
break the relation `(2q-1)+1 = 2q`, and the statement is genuinely FALSE
(counterexample `n=0, k=1`: `Rn 0 0 2 = 1` but `c 0 0 1 = 4!/(2·3!) = 2`). -/
theorem Rn_eq_c (q n k : ℕ) : Rn q n ((n : ℝ) + 1 + (k : ℝ)) = c q n k := by
  rcases Nat.eq_zero_or_pos q with hq0 | hq
  · -- q = 0 : the statement is FALSE (see the counterexample in the docstring).
    subst hq0
    sorry
  · -- q ≥ 1 : the genuine content.
    set t : ℝ := (n : ℝ) + 1 + (k : ℝ) with ht
    have hP1 : ∏ j ∈ Finset.Icc 1 n, (t - (j : ℝ)) = ((n + k)! : ℝ) / (k ! : ℝ) := by
      rw [prod_Icc_one_reflect n (fun j => t - (j : ℝ))]
      have hb : ∀ i ∈ Finset.range n, t - ((n - i : ℕ) : ℝ) = (k : ℝ) + 1 + (i : ℝ) := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [Nat.cast_sub (Nat.le_of_lt hi), ht]; ring
      rw [Finset.prod_congr rfl hb, prod_range_shift k n, Nat.add_comm k n]
    have hP2 : ∏ j ∈ Finset.Icc 1 n, (t + (n : ℝ) + (j : ℝ))
        = ((3 * n + k + 1)! : ℝ) / ((2 * n + k + 1)! : ℝ) := by
      rw [prod_Icc_one_range n (fun j => t + (n : ℝ) + (j : ℝ))]
      have hb : ∀ i ∈ Finset.range n,
          t + (n : ℝ) + ((1 + i : ℕ) : ℝ) = ((2 * n + k + 1 : ℕ) : ℝ) + 1 + (i : ℝ) := by
        intro i _; push_cast [ht]; ring
      rw [Finset.prod_congr rfl hb, prod_range_shift (2 * n + k + 1) n,
        show 2 * n + k + 1 + n = 3 * n + k + 1 from by ring]
    have hP3 : ∏ j ∈ Finset.Icc 1 (3 * n), (t - (n : ℝ) - 1 / 2 + (j : ℝ))
        = ((6 * n + 2 * k + 1)! : ℝ) * (k ! : ℝ)
            / (2 ^ (6 * n) * ((3 * n + k)! : ℝ) * ((2 * k + 1)! : ℝ)) := by
      rw [prod_Icc_one_range (3 * n) (fun j => t - (n : ℝ) - 1 / 2 + (j : ℝ))]
      have hb : ∀ i ∈ Finset.range (3 * n),
          t - (n : ℝ) - 1 / 2 + ((1 + i : ℕ) : ℝ) = ((2 * k + 2 * i + 3 : ℕ) : ℝ) / 2 := by
        intro i _; push_cast [ht]; ring
      rw [Finset.prod_congr rfl hb, Finset.prod_div_distrib, Finset.prod_const,
        Finset.card_range, prod_range_odd3 k (3 * n),
        show 2 * k + 2 * (3 * n) + 1 = 6 * n + 2 * k + 1 from by ring,
        show k + 3 * n = 3 * n + k from by ring]
      have h2 : (2 : ℝ) ^ (3 * n) ≠ 0 := by positivity
      have h3 : ((3 * n + k)! : ℝ) ≠ 0 := fact_cast_ne _
      have h4 : ((2 * k + 1)! : ℝ) ≠ 0 := fact_cast_ne _
      field_simp
      ring
    have hPden : ∏ j ∈ Finset.range (n + 1), (t + (j : ℝ))
        = ((2 * n + k + 1)! : ℝ) / ((n + k)! : ℝ) := by
      have hb : ∀ i ∈ Finset.range (n + 1),
          t + (i : ℝ) = ((n + k : ℕ) : ℝ) + 1 + (i : ℝ) := by
        intro i _; push_cast [ht]; ring
      rw [Finset.prod_congr rfl hb, prod_range_shift (n + k) (n + 1),
        show n + k + (n + 1) = 2 * n + k + 1 from by ring]
    -- Successor / power bridges to reconcile atoms with `c`.
    have hF1 : ((3 * n + k + 1)! : ℝ) = ((3 * n + k + 1 : ℕ) : ℝ) * ((3 * n + k)! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hF2 : ((6 * n + 2 * k + 2)! : ℝ)
        = ((6 * n + 2 * k + 2 : ℕ) : ℝ) * ((6 * n + 2 * k + 1)! : ℝ) := by
      rw [show 6 * n + 2 * k + 2 = (6 * n + 2 * k + 1) + 1 from by ring, Nat.factorial_succ]
      push_cast; ring
    have hpow : ∀ x : ℝ, x ^ (2 * q) = x ^ (2 * q - 1) * x := by
      intro x; rw [← pow_succ]; congr 1; omega
    -- Assemble.
    simp only [Rn, c]
    rw [Finset.prod_pow, hP1, hP2, hP3, hPden, hF1, hF2,
      hpow ((n + k)! : ℝ), hpow ((2 * n + k + 1)! : ℝ)]
    have hn := fact_cast_ne n
    have hnk := fact_cast_ne (n + k)
    have hk := fact_cast_ne k
    have h3nk := fact_cast_ne (3 * n + k)
    have h2nk := fact_cast_ne (2 * n + k + 1)
    have h6 := fact_cast_ne (6 * n + 2 * k + 1)
    have h2k := fact_cast_ne (2 * k + 1)
    have hpnk : ((n + k)! : ℝ) ^ (2 * q - 1) ≠ 0 := pow_ne_zero _ hnk
    have hp2nk : ((2 * n + k + 1)! : ℝ) ^ (2 * q - 1) ≠ 0 := pow_ne_zero _ h2nk
    have htwo : (2 : ℝ) ^ (6 * n) ≠ 0 := by positivity
    rw [div_pow]
    field_simp
    push_cast
    ring

/-- Bridge for the twisted form: the `k`-th summand of `rhat q n` is `R_n(n+½+k)`.

As with `Rn_eq_c`, this needs `1 ≤ q` and is FALSE at `q = 0` (same `ℕ`-truncation
of `2*q-1` vs `2*q`). -/
theorem Rn_eq_chat (q n k : ℕ) : Rn q n ((n : ℝ) + 1 / 2 + (k : ℝ)) = chat q n k := by
  rcases Nat.eq_zero_or_pos q with hq0 | hq
  · -- q = 0 : FALSE (same truncation obstruction as `Rn_eq_c`).
    subst hq0
    sorry
  · set t : ℝ := (n : ℝ) + 1 / 2 + (k : ℝ) with ht
    -- Half-integer descending product `P1`.
    have hP1 : ∏ j ∈ Finset.Icc 1 n, (t - (j : ℝ))
        = ((2 * n + 2 * k)! : ℝ) * (k ! : ℝ)
            / (2 ^ n * 2 ^ n * ((n + k)! : ℝ) * ((2 * k)! : ℝ)) := by
      rw [prod_Icc_one_reflect n (fun j => t - (j : ℝ))]
      have hb : ∀ i ∈ Finset.range n,
          t - ((n - i : ℕ) : ℝ) = ((2 * k + 2 * i + 1 : ℕ) : ℝ) / 2 := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [Nat.cast_sub (Nat.le_of_lt hi)]; push_cast [ht]; ring
      rw [Finset.prod_congr rfl hb, Finset.prod_div_distrib, Finset.prod_const,
        Finset.card_range, prod_range_odd k n, Nat.add_comm k n,
        show 2 * k + 2 * n = 2 * n + 2 * k from by ring]
      have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
      have h3 : ((n + k)! : ℝ) ≠ 0 := fact_cast_ne _
      have h4 : ((2 * k)! : ℝ) ≠ 0 := fact_cast_ne _
      field_simp
    -- Half-integer ascending product `P2`.
    have hP2 : ∏ j ∈ Finset.Icc 1 n, (t + (n : ℝ) + (j : ℝ))
        = ((6 * n + 2 * k + 1)! : ℝ) * ((2 * n + k)! : ℝ)
            / (2 ^ n * 2 ^ n * ((3 * n + k)! : ℝ) * ((4 * n + 2 * k + 1)! : ℝ)) := by
      rw [prod_Icc_one_range n (fun j => t + (n : ℝ) + (j : ℝ))]
      have hb : ∀ i ∈ Finset.range n,
          t + (n : ℝ) + ((1 + i : ℕ) : ℝ) = ((2 * (2 * n + k) + 2 * i + 3 : ℕ) : ℝ) / 2 := by
        intro i _; push_cast [ht]; ring
      rw [Finset.prod_congr rfl hb, Finset.prod_div_distrib, Finset.prod_const,
        Finset.card_range, prod_range_odd3 (2 * n + k) n,
        show 2 * (2 * n + k) + 2 * n + 1 = 6 * n + 2 * k + 1 from by ring,
        show 2 * n + k + n = 3 * n + k from by ring,
        show 2 * (2 * n + k) + 1 = 4 * n + 2 * k + 1 from by ring]
      have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
      have h3 : ((3 * n + k)! : ℝ) ≠ 0 := fact_cast_ne _
      have h4 : ((4 * n + 2 * k + 1)! : ℝ) ≠ 0 := fact_cast_ne _
      field_simp
    -- Integer product `P3` (the `∓½` cancel).
    have hP3 : ∏ j ∈ Finset.Icc 1 (3 * n), (t - (n : ℝ) - 1 / 2 + (j : ℝ))
        = ((3 * n + k)! : ℝ) / (k ! : ℝ) := by
      rw [prod_Icc_one_range (3 * n) (fun j => t - (n : ℝ) - 1 / 2 + (j : ℝ))]
      have hb : ∀ i ∈ Finset.range (3 * n),
          t - (n : ℝ) - 1 / 2 + ((1 + i : ℕ) : ℝ) = (k : ℝ) + 1 + (i : ℝ) := by
        intro i _; push_cast [ht]; ring
      rw [Finset.prod_congr rfl hb, prod_range_shift k (3 * n), Nat.add_comm k (3 * n)]
    -- The denominator product equals `S / 2^(n+1)` with `S` the same product as in `chat`.
    have hPden : ∏ j ∈ Finset.range (n + 1), (t + (j : ℝ))
        = (∏ j ∈ Finset.range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ)) / 2 ^ (n + 1) := by
      have hb : ∀ j ∈ Finset.range (n + 1),
          t + (j : ℝ) = ((2 * (n + k + j) + 1 : ℕ) : ℝ) / 2 := by
        intro j _; push_cast [ht]; ring
      rw [Finset.prod_congr rfl hb, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
    -- Expand `S` into factorials (only used inside the scalar identity `key`).
    have hS : (∏ j ∈ Finset.range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ))
        = ((4 * n + 2 * k + 2)! : ℝ) * ((n + k)! : ℝ)
            / (2 ^ (n + 1) * ((2 * n + k + 1)! : ℝ) * ((2 * n + 2 * k)! : ℝ)) := by
      have hb : ∀ j ∈ Finset.range (n + 1),
          ((2 * (n + k + j) + 1 : ℕ) : ℝ) = ((2 * (n + k) + 2 * j + 1 : ℕ) : ℝ) := by
        intro j _; rw [show 2 * (n + k + j) + 1 = 2 * (n + k) + 2 * j + 1 from by ring]
      rw [Finset.prod_congr rfl hb, prod_range_odd (n + k) (n + 1),
        show 2 * (n + k) + 2 * (n + 1) = 4 * n + 2 * k + 2 from by ring,
        show n + k + (n + 1) = 2 * n + k + 1 from by ring,
        show 2 * (n + k) = 2 * n + 2 * k from by ring]
    -- Successor bridges.
    have hF3 : ((4 * n + 2 * k + 2)! : ℝ)
        = ((4 * n + 2 * k + 2 : ℕ) : ℝ) * ((4 * n + 2 * k + 1)! : ℝ) := by
      rw [show 4 * n + 2 * k + 2 = (4 * n + 2 * k + 1) + 1 from by ring, Nat.factorial_succ]
      push_cast; ring
    have hF4 : ((2 * n + k + 1)! : ℝ) = ((2 * n + k + 1 : ℕ) : ℝ) * ((2 * n + k)! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    -- Scalar identity: products times `S / 2^(n+1)` give `chat`'s numerator core.
    have key : (∏ j ∈ Finset.Icc 1 n, (t - (j : ℝ)))
          * (∏ j ∈ Finset.Icc 1 n, (t + (n : ℝ) + (j : ℝ)))
          * (∏ j ∈ Finset.Icc 1 (3 * n), (t - (n : ℝ) - 1 / 2 + (j : ℝ)))
          * ((∏ j ∈ Finset.range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ)) / 2 ^ (n + 1))
        = ((6 * n + 2 * k + 1)! : ℝ) / ((2 * k)! : ℝ) / 2 ^ (6 * n + 1) := by
      rw [hP1, hP2, hP3, hS, hF3, hF4]
      have hn := fact_cast_ne n
      have hnk := fact_cast_ne (n + k)
      have hk := fact_cast_ne k
      have h3nk := fact_cast_ne (3 * n + k)
      have h2nk := fact_cast_ne (2 * n + k)
      have h4 := fact_cast_ne (4 * n + 2 * k + 1)
      have h2k := fact_cast_ne (2 * k)
      have h6 := fact_cast_ne (6 * n + 2 * k + 1)
      have e1 : (2 : ℝ) ^ n ≠ 0 := by positivity
      have e2 : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    have hpow : ∀ x : ℝ, x ^ (2 * q) = x ^ (2 * q - 1) * x := by
      intro x; rw [← pow_succ]; congr 1; omega
    -- Assemble.
    simp only [Rn, chat]
    rw [Finset.prod_pow, hPden]
    set E : ℝ := (∏ j ∈ Finset.range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ)) / 2 ^ (n + 1)
      with hE
    rw [hpow E, ← key]
    have hEne : E ≠ 0 := by
      rw [hE]
      apply div_ne_zero
      · apply Finset.prod_ne_zero_iff.mpr
        intro i _
        exact Nat.cast_ne_zero.mpr (by positivity)
      · positivity
    have hEpow : E ^ (2 * q - 1) ≠ 0 := pow_ne_zero _ hEne
    field_simp

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
