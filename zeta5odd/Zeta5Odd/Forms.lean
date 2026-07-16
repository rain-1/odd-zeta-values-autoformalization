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
  * `Rn_wellPoised` — PROVED: the well-poised functional equation `R_n(-t-n) = -R_n(t)`
      (paper Lemma 2 proof, tex 166), directly from the product definition by reindexing.
  * `partialFraction_exists` — PROVED modulo two clearly-named helper `sorry`s:
      - `pf_decomp` (e04 decomposition + Lemma 1 integrality — the analytic heart), and
      - `pf_unique` (uniqueness of the partial-fraction coefficients).
      The Lemma 2 SYMMETRY conjunct is fully DERIVED here from `Rn_wellPoised` + `pf_unique`
      (paper tex 165–176); only decomposition/integrality remain as `pf_decomp`.
  * `Rn`, `repr_combined` — STATED, `repr_combined` proof still `sorry` (Lemma 3 assembly).
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

/-- Pull a per-factor negation out of a finite product: `∏ (-f j) = (-1)^|s| ∏ f j`. -/
private lemma prod_neg_pow (s : Finset ℕ) (f : ℕ → ℝ) :
    ∏ j ∈ s, (-(f j)) = (-1) ^ s.card * ∏ j ∈ s, f j := by
  rw [Finset.prod_congr rfl (fun j _ => neg_eq_neg_one_mul (f j)),
    Finset.prod_mul_distrib, Finset.prod_const]

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
theorem Rn_eq_c (q n k : ℕ) (hq1 : 1 ≤ q) : Rn q n ((n : ℝ) + 1 + (k : ℝ)) = c q n k := by
  rcases Nat.eq_zero_or_pos q with hq0 | hq
  · -- q = 0 excluded by hypothesis (the statement is genuinely false there).
    subst hq0
    exact absurd hq1 (by norm_num)
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
theorem Rn_eq_chat (q n k : ℕ) (hq1 : 1 ≤ q) : Rn q n ((n : ℝ) + 1 / 2 + (k : ℝ)) = chat q n k := by
  rcases Nat.eq_zero_or_pos q with hq0 | hq
  · -- q = 0 excluded by hypothesis (same truncation obstruction).
    subst hq0
    exact absurd hq1 (by norm_num)
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

/-! ### Well-poised functional equation (paper tex 166, used for Lemma 2) -/

/-- **Well-poised symmetry of `R_n`** (paper Lemma 2 proof, tex 166): since `s = 33` is odd,
`R_n(-t-n) = -R_n(t)`.  Proved directly from the product definition by reindexing:
the two `Icc 1 n` products swap (each contributing `(-1)^n`, net invariant), the middle
`3n`-product reflects to `(-1)^{3n}` times itself, and the denominator base reflects to
`(-1)^{n+1}` times itself; the net sign is `-1` because `33` is odd. -/
theorem Rn_wellPoised (n : ℕ) (t : ℝ) :
    Rn 17 n (-t - (n : ℝ)) = - Rn 17 n t := by
  -- Reindexing identities for the four products at the reflected argument `-t-n`.
  have hA : ∏ j ∈ Finset.Icc 1 n, (-t - (n : ℝ) - (j : ℝ))
      = (-1) ^ n * ∏ j ∈ Finset.Icc 1 n, (t + (n : ℝ) + (j : ℝ)) := by
    have hpt : ∀ j ∈ Finset.Icc 1 n,
        -t - (n : ℝ) - (j : ℝ) = -(t + (n : ℝ) + (j : ℝ)) := fun j _ => by ring
    rw [Finset.prod_congr rfl hpt, prod_neg_pow, Nat.card_Icc, Nat.add_sub_cancel]
  have hB : ∏ j ∈ Finset.Icc 1 n, (-t - (n : ℝ) + (n : ℝ) + (j : ℝ))
      = (-1) ^ n * ∏ j ∈ Finset.Icc 1 n, (t - (j : ℝ)) := by
    have hpt : ∀ j ∈ Finset.Icc 1 n,
        -t - (n : ℝ) + (n : ℝ) + (j : ℝ) = -(t - (j : ℝ)) := fun j _ => by ring
    rw [Finset.prod_congr rfl hpt, prod_neg_pow, Nat.card_Icc, Nat.add_sub_cancel]
  have hC : ∏ j ∈ Finset.Icc 1 (3 * n), (-t - (n : ℝ) - (n : ℝ) - 1 / 2 + (j : ℝ))
      = (-1) ^ (3 * n) * ∏ j ∈ Finset.Icc 1 (3 * n), (t - (n : ℝ) - 1 / 2 + (j : ℝ)) := by
    -- Factor out a sign, reflecting the index `j ↦ 3n+1-j`.
    have hpt : ∀ j ∈ Finset.Icc 1 (3 * n),
        -t - (n : ℝ) - (n : ℝ) - 1 / 2 + (j : ℝ)
          = -(t - (n : ℝ) - 1 / 2 + ((3 * n + 1 - j : ℕ) : ℝ)) := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Nat.cast_sub (by omega : j ≤ 3 * n + 1)]
      push_cast; ring
    rw [Finset.prod_congr rfl hpt, prod_neg_pow, Nat.card_Icc, Nat.add_sub_cancel]
    congr 1
    -- reflect `∏ (t-n-1/2+↑(3n+1-j)) = ∏ (t-n-1/2+↑j)` over `Icc 1 (3n)`
    rw [prod_Icc_one_range (3 * n) (fun j => t - (n : ℝ) - 1 / 2 + ((3 * n + 1 - j : ℕ) : ℝ)),
        prod_Icc_one_range (3 * n) (fun j => t - (n : ℝ) - 1 / 2 + (j : ℝ)),
        ← Finset.prod_range_reflect
          (fun i => t - (n : ℝ) - 1 / 2 + ((1 + i : ℕ) : ℝ)) (3 * n)]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    show t - (n : ℝ) - 1 / 2 + ((3 * n + 1 - (1 + i) : ℕ) : ℝ)
        = t - (n : ℝ) - 1 / 2 + ((1 + (3 * n - 1 - i) : ℕ) : ℝ)
    congr 2
    omega
  have hD : ∏ j ∈ Finset.range (n + 1), (-t - (n : ℝ) + (j : ℝ))
      = (-1) ^ (n + 1) * ∏ j ∈ Finset.range (n + 1), (t + (j : ℝ)) := by
    have hpt : ∀ j ∈ Finset.range (n + 1),
        -t - (n : ℝ) + (j : ℝ) = -(t + ((n - j : ℕ) : ℝ)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Nat.cast_sub (by omega : j ≤ n)]
      ring
    rw [Finset.prod_congr rfl hpt, prod_neg_pow, Finset.card_range]
    congr 1
    -- reflect `∏ (t+↑(n-j)) = ∏ (t+↑j)` over `range (n+1)`
    rw [← Finset.prod_range_reflect (fun j => t + (j : ℝ)) (n + 1)]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    show t + ((n - j : ℕ) : ℝ) = t + ((n + 1 - 1 - j : ℕ) : ℝ)
    rw [show n + 1 - 1 - j = n - j from by omega]
  -- Assemble: expand `Rn`, normalise the concrete exponents, and rewrite the four products.
  simp only [Rn]
  rw [show (2 * 17 - 1 : ℕ) = 33 from by norm_num,
      show (2 * 17 - 6 : ℕ) = 28 from by norm_num]
  simp only [Finset.prod_pow]
  rw [hA, hB, hC, hD]
  rcases Nat.even_or_odd n with hpar | hpar
  · -- `n` even: signs are `1, 1, -1`.
    simp only [hpar.neg_one_pow, (hpar.mul_left 3).neg_one_pow, hpar.add_one.neg_one_pow]
    ring
  · -- `n` odd: signs are `-1, -1, 1`.
    simp only [hpar.neg_one_pow, ((by norm_num : Odd 3).mul hpar).neg_one_pow,
      hpar.add_one.neg_one_pow]
    ring

/-! ### Partial fractions with the coefficients `a_{i,k}` (paper e04 + Lemmas 1, 2) -/

/-- **Decomposition (e04) + integrality (Lemma 1)** for `R_n` at `s = 33`.
[ANALYTIC HEART — proof is `sorry`.]  `a i k` is the coefficient of `(t+k)^{-i}` in the
Laurent expansion of `R_n` at its order-`33` pole `t = -k`.  Existence of the decomposition
is the partial-fraction theorem; `d_n^{33-i}·a_{i,k} ∈ ℤ` (Lemma 1) follows from the paper's
differentiation formula (tex 138–153) applied to `R_n` as a product of the six
`simpler` integer-coefficient functions of tex 96–114 together with `d_n/(k_j-k_1) ∈ ℤ`
(available as `dvd_lcmUpto`).  These two conjuncts are exactly what `repr_combined` still needs. -/
private theorem pf_decomp (n : ℕ) :
    ∃ a : ℕ → ℕ → ℝ,
      (∀ t : ℝ, (∀ k ∈ Finset.range (n + 1), t + (k : ℝ) ≠ 0) →
          Rn 17 n t = ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1),
              a i k / (t + (k : ℝ)) ^ i)
      ∧ (∀ i ∈ Finset.Icc 1 33, ∀ k ∈ Finset.range (n + 1),
          ∃ z : ℤ, (Nat.lcmUpto n : ℝ) ^ (33 - i) * a i k = z) := by
  sorry

/-- **Uniqueness of the (e04) partial-fraction coefficients.**  [Proof is `sorry`.]
Two coefficient arrays inducing the same value off the `n+1` poles agree on the grid
`1 ≤ i ≤ 33`, `0 ≤ k ≤ n`.  (Clear denominators: the difference is a polynomial of degree
`< 33(n+1)` vanishing at infinitely many `t`, hence identically zero, forcing all
coefficients equal.)  Used only to transport the well-poised symmetry through the
decomposition; the symmetry reduction itself (below) is fully proved. -/
private theorem pf_unique (n : ℕ) (a b : ℕ → ℕ → ℝ)
    (h : ∀ t : ℝ, (∀ k ∈ Finset.range (n + 1), t + (k : ℝ) ≠ 0) →
        ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1), a i k / (t + (k : ℝ)) ^ i
          = ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1), b i k / (t + (k : ℝ)) ^ i) :
    ∀ i ∈ Finset.Icc 1 33, ∀ k ∈ Finset.range (n + 1), a i k = b i k := by
  sorry

/-- **Partial-fraction data (paper e04 + Lemmas 1–2).**
There is a coefficient array `a : (i,k) ↦ a_{i,k}` (`1 ≤ i ≤ s = 33`, `0 ≤ k ≤ n`) with:
  * (e04) the decomposition `R_n(t) = Σ_i Σ_k a_{i,k}/(t+k)^i` off the poles;
  * (Lemma 1) integrality `d_n^{s−i} · a_{i,k} ∈ ℤ`;
  * (Lemma 2) well-poised symmetry `a_{i,k} = (−1)^{i−1} a_{i,n−k}`.

The decomposition and integrality come from `pf_decomp` (the analytic heart, `sorry`); the
symmetry (Lemma 2) is DERIVED here from the well-poised functional equation `Rn_wellPoised`
(fully proved above) and the uniqueness of the decomposition (`pf_unique`, `sorry`), exactly
following the paper's Lemma 2 proof (tex 165–176). -/
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
  obtain ⟨a, hdec, hint⟩ := pf_decomp n
  refine ⟨a, hdec, hint, ?_⟩
  -- Lemma 2 (well-poised symmetry) from `Rn_wellPoised` + uniqueness of the decomposition.
  -- Substituting `Rn(-t-n) = -Rn(t)` into (e04) gives a second decomposition whose
  -- coefficients are `(-1)^{i-1} a_{i,n-k}`; uniqueness then forces the symmetry.
  have hsum : ∀ t : ℝ, (∀ k ∈ Finset.range (n + 1), t + (k : ℝ) ≠ 0) →
      ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1), a i k / (t + (k : ℝ)) ^ i
        = ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1),
            ((-1) ^ (i - 1) * a i (n - k)) / (t + (k : ℝ)) ^ i := by
    intro t ht
    -- The pole condition transports to the reflected argument `-t-n`.
    have ht' : ∀ k ∈ Finset.range (n + 1), (-t - (n : ℝ)) + (k : ℝ) ≠ 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hne := ht (n - k) (Finset.mem_range.mpr (by omega))
      rw [Nat.cast_sub (by omega : k ≤ n)] at hne
      intro hcontra
      exact hne (by linarith)
    calc ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1), a i k / (t + (k : ℝ)) ^ i
        = Rn 17 n t := (hdec t ht).symm
      _ = - Rn 17 n (-t - (n : ℝ)) := by rw [Rn_wellPoised n t, neg_neg]
      _ = - ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1),
              a i k / ((-t - (n : ℝ)) + (k : ℝ)) ^ i := by rw [hdec (-t - (n : ℝ)) ht']
      _ = ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1),
              ((-1) ^ (i - 1) * a i (n - k)) / (t + (k : ℝ)) ^ i := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mem_Icc] at hi
          rw [← Finset.sum_neg_distrib,
            ← Finset.sum_range_reflect
              (fun k => ((-1) ^ (i - 1) * a i (n - k)) / (t + (k : ℝ)) ^ i) (n + 1)]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_range] at hk
          have hne := ht (n - k) (Finset.mem_range.mpr (by omega))
          have hY : (-t - (n : ℝ)) + (k : ℝ) = -(t + ((n - k : ℕ) : ℝ)) := by
            rw [Nat.cast_sub (by omega : k ≤ n)]; ring
          have hsgn : (-1 : ℝ) ^ i = -((-1) ^ (i - 1)) := by
            conv_lhs => rw [show i = (i - 1) + 1 from by omega]
            rw [pow_succ]; ring
          have hinvI : ((-1 : ℝ) ^ i)⁻¹ = (-1) ^ i := by rw [← inv_pow]; norm_num
          simp only [show n + 1 - 1 - k = n - k from by omega,
            show n - (n - k) = k from by omega]
          rw [hY, neg_pow, mul_comm ((-1 : ℝ) ^ i) ((t + ((n - k : ℕ) : ℝ)) ^ i), ← div_div,
            div_eq_mul_inv (a i k / (t + ((n - k : ℕ) : ℝ)) ^ i) ((-1 : ℝ) ^ i), hinvI, hsgn]
          ring
  have hb := pf_unique n a (fun i k => (-1) ^ (i - 1) * a i (n - k)) hsum
  intro i hi k hk
  exact hb i hi k hk

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
