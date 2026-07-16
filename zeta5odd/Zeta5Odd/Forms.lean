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

open Filter Topology in
/-- **Uniqueness of the (e04) partial-fraction coefficients.**  [PROVED.]
Two coefficient arrays inducing the same value off the `n+1` poles agree on the grid
`1 ≤ i ≤ 33`, `0 ≤ k ≤ n`.  Proof by residue peeling: near each pole `-k₀` the difference
`Σ (a-b)_{i,k}/(t+k)^i` vanishes, so scaling by `(t+k₀)^P` and taking the punctured limit
`t → -k₀` extracts the top coefficient `(a-b)_{P,k₀}` (downward induction `P = 33,…,1`),
forcing it to `0`.  Used to transport the well-poised symmetry through the decomposition. -/
private theorem pf_unique (n : ℕ) (a b : ℕ → ℕ → ℝ)
    (h : ∀ t : ℝ, (∀ k ∈ Finset.range (n + 1), t + (k : ℝ) ≠ 0) →
        ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1), a i k / (t + (k : ℝ)) ^ i
          = ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1), b i k / (t + (k : ℝ)) ^ i) :
    ∀ i ∈ Finset.Icc 1 33, ∀ k ∈ Finset.range (n + 1), a i k = b i k := by
  classical
  set d : ℕ → ℕ → ℝ := fun i k => a i k - b i k with hd
  -- The difference of coefficient arrays vanishes off the poles.
  have hS : ∀ t : ℝ, (∀ k ∈ Finset.range (n + 1), t + (k : ℝ) ≠ 0) →
      ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1), d i k / (t + (k : ℝ)) ^ i = 0 := by
    intro t ht
    have hh := h t ht
    have hrw : ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1), d i k / (t + (k:ℝ))^i
        = (∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1), a i k / (t + (k:ℝ))^i)
          - (∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1), b i k / (t + (k:ℝ))^i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k _
      show (a i k - b i k) / (t + (k:ℝ))^i = a i k/(t+(k:ℝ))^i - b i k/(t+(k:ℝ))^i
      rw [sub_div]
    rw [hrw, hh, sub_self]
  -- Reduce the goal to `d i k = 0` on the grid.
  suffices hgoal : ∀ k₀ ∈ Finset.range (n+1), ∀ i ∈ Finset.Icc 1 33, d i k₀ = 0 by
    intro i hi k hk
    have h0 : a i k - b i k = 0 := hgoal k hk i hi
    linarith
  intro k₀ hk₀
  haveI : (𝓝[≠] (-(k₀:ℝ))).NeBot := inferInstance
  -- Near `-k₀`, all the poles `-k'` are eventually avoided.
  have hpole : ∀ᶠ t in 𝓝[≠] (-(k₀:ℝ)), ∀ k' ∈ Finset.range (n+1), t + (k':ℝ) ≠ 0 := by
    rw [Finset.eventually_all]
    intro k' _
    by_cases hcase : k' = k₀
    · subst hcase
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
      intro hc; apply ht; linarith
    · have hne : (-(k₀:ℝ)) + (k':ℝ) ≠ 0 := by
        have hcast : (k':ℝ) ≠ (k₀:ℝ) := by exact_mod_cast hcase
        intro hc; apply hcast; linarith
      have hcont : ContinuousAt (fun t : ℝ => t + (k':ℝ)) (-(k₀:ℝ)) := by fun_prop
      have hev := hcont.eventually_ne
        (show (fun t : ℝ => t + (k':ℝ)) (-(k₀:ℝ)) ≠ 0 by simpa using hne)
      exact nhdsWithin_le_nhds hev
  -- Peeling step: extract the leading coefficient `a_{P,k₀}` once the higher ones vanish.
  have leading : ∀ P : ℕ, 1 ≤ P → P ≤ 33 →
      (∀ j, P < j → j ≤ 33 → d j k₀ = 0) → d P k₀ = 0 := by
    intro P hP1 hP33 hyp
    set lim : ℕ → ℕ → ℝ := fun i k => if i = P ∧ k = k₀ then d P k₀ else 0 with hlim
    -- (A) The scaled sum `(t+k₀)^P · S(t)` is eventually zero near `-k₀`.
    have factA : Tendsto (fun t : ℝ => ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n+1),
          d i k * (t+(k₀:ℝ))^P/(t+(k:ℝ))^i) (𝓝[≠] (-(k₀:ℝ))) (𝓝 0) := by
      have hgz : (fun t : ℝ => ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n+1),
            d i k * (t+(k₀:ℝ))^P/(t+(k:ℝ))^i) =ᶠ[𝓝[≠] (-(k₀:ℝ))] (fun _ => 0) := by
        filter_upwards [hpole] with t htp
        have hmul : ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n+1),
              d i k * (t+(k₀:ℝ))^P/(t+(k:ℝ))^i
            = (t+(k₀:ℝ))^P * ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n+1),
              d i k/(t+(k:ℝ))^i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _
          ring
        rw [hmul, hS t htp, mul_zero]
      exact Filter.Tendsto.congr' hgz.symm tendsto_const_nhds
    -- (B) Termwise, the same scaled sum tends to `d_{P,k₀}`.
    have hlimsum : (∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n+1), lim i k) = d P k₀ := by
      rw [Finset.sum_eq_single_of_mem P (Finset.mem_Icc.mpr ⟨hP1, hP33⟩)
        (fun i _ hine => Finset.sum_eq_zero (fun k _ => by
          simp only [hlim, if_neg (show ¬(i = P ∧ k = k₀) from fun hc => hine hc.1)]))]
      rw [Finset.sum_eq_single_of_mem k₀ hk₀
        (fun k _ hkne => by
          simp only [hlim, if_neg (show ¬(P = P ∧ k = k₀) from fun hc => hkne hc.2)])]
      simp only [hlim, if_pos (show P = P ∧ k₀ = k₀ from ⟨rfl, rfl⟩)]
    have factB : Tendsto (fun t : ℝ => ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n+1),
          d i k * (t+(k₀:ℝ))^P/(t+(k:ℝ))^i) (𝓝[≠] (-(k₀:ℝ))) (𝓝 (d P k₀)) := by
      rw [← hlimsum]
      apply tendsto_finsetSum
      intro i hi
      apply tendsto_finsetSum
      intro k _
      by_cases hkk : k = k₀
      · subst k
        by_cases hiP : i ≤ P
        · -- power collapses to `(t+k₀)^(P-i)`
          have heq : (fun t : ℝ => d i k₀ * (t+(k₀:ℝ))^P/(t+(k₀:ℝ))^i)
                   =ᶠ[𝓝[≠] (-(k₀:ℝ))] (fun t : ℝ => d i k₀ * (t+(k₀:ℝ))^(P-i)) := by
            filter_upwards [self_mem_nhdsWithin] with t ht
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
            have htk : t + (k₀:ℝ) ≠ 0 := by intro hc; apply ht; linarith
            rw [mul_div_assoc, div_eq_mul_inv, ← pow_sub₀ _ htk hiP]
          have hlimval : lim i k₀ = d i k₀ * (0:ℝ)^(P-i) := by
            rcases eq_or_lt_of_le hiP with hEq | hLt
            · rw [hEq]
              simp only [hlim, if_pos (show P = P ∧ k₀ = k₀ from ⟨rfl, rfl⟩),
                Nat.sub_self, pow_zero, mul_one]
            · simp only [hlim,
                if_neg (show ¬(i = P ∧ k₀ = k₀) from fun hc => absurd hc.1 (by omega)),
                zero_pow (show P - i ≠ 0 by omega), mul_zero]
          rw [hlimval]
          refine Filter.Tendsto.congr' heq.symm ?_
          apply Tendsto.mono_left _ nhdsWithin_le_nhds
          have hc : ContinuousAt (fun t : ℝ => d i k₀ * (t+(k₀:ℝ))^(P-i)) (-(k₀:ℝ)) := by fun_prop
          simpa only [show (-(k₀:ℝ)) + (k₀:ℝ) = 0 from by ring] using hc.tendsto
        · -- `i > P`: the coefficient already vanishes by the inductive hypothesis
          push_neg at hiP
          have hd0 : d i k₀ = 0 := hyp i hiP (Finset.mem_Icc.mp hi).2
          have hlimval : lim i k₀ = 0 := by
            simp only [hlim,
              if_neg (show ¬(i = P ∧ k₀ = k₀) from fun hc => absurd hc.1 (by omega))]
          have hfun : (fun t : ℝ => d i k₀ * (t+(k₀:ℝ))^P/(t+(k₀:ℝ))^i) = (fun _ => (0:ℝ)) := by
            funext t; rw [hd0]; ring
          rw [hlimval, hfun]
          exact tendsto_const_nhds
      · -- `k ≠ k₀`: the summand is continuous at `-k₀` with value `0`
        have hlimval : lim i k = 0 := by
          simp only [hlim, if_neg (show ¬(i = P ∧ k = k₀) from fun hc => hkk hc.2)]
        rw [hlimval]
        apply Tendsto.mono_left _ nhdsWithin_le_nhds
        have hval0 : (-(k₀:ℝ)) + (k:ℝ) ≠ 0 := by
          have hcast : (k:ℝ) ≠ (k₀:ℝ) := by exact_mod_cast hkk
          intro hc; apply hcast; linarith
        have hcont : ContinuousAt (fun t : ℝ => d i k * (t+(k₀:ℝ))^P/(t+(k:ℝ))^i) (-(k₀:ℝ)) :=
          ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using pow_ne_zero i hval0)
        simpa only [show (-(k₀:ℝ)) + (k₀:ℝ) = 0 from by ring,
          zero_pow (show P ≠ 0 by omega), mul_zero, zero_div] using hcont.tendsto
    have huniq := tendsto_nhds_unique factA factB
    exact huniq.symm
  -- Downward induction: peel coefficients `i = 33, 32, …, 1`.
  have peel : ∀ m : ℕ, ∀ i : ℕ, 1 ≤ i → 33 - m ≤ i → i ≤ 33 → d i k₀ = 0 := by
    intro m
    induction m with
    | zero =>
      intro i h1 hle h33
      have hi33 : i = 33 := by omega
      subst hi33
      exact leading 33 (by norm_num) (le_refl 33) (fun j hj hj33 => absurd hj33 (by omega))
    | succ m ih =>
      intro i h1 hle h33
      rcases Nat.lt_or_ge i (33 - m) with hcase | hcase
      · have hiP : i = 33 - (m+1) := by omega
        subst hiP
        exact leading (33 - (m+1)) h1 (by omega)
          (fun j hj hj33 => ih j (by omega) (by omega) hj33)
      · exact ih i h1 hcase h33
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact peel 32 i hi.1 (by omega) hi.2

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

/-! ### Analytic helpers for Lemma 3 (e07/e08 assembly) -/

/-- **Even column totals vanish** (paper Lemma 3, the `Σ_k a_{i,k} = 0` for even `i`):
from the well-poised symmetry `a_{i,k} = (−1)^{i−1} a_{i,n−k}`, reflecting the `k`-sum
gives `Σ_k a_{i,k} = (−1)^{i−1} Σ_k a_{i,k}`, so for even `i` the total is its own
negative, hence `0`. -/
private lemma column_even_zero (n i : ℕ) (a : ℕ → ℕ → ℝ)
    (hsym : ∀ i ∈ Finset.Icc 1 33, ∀ k ∈ Finset.range (n + 1),
        a i k = (-1) ^ (i - 1) * a i (n - k))
    (hi : i ∈ Finset.Icc 1 33) (hev : Even i) :
    ∑ k ∈ Finset.range (n + 1), a i k = 0 := by
  have hrefl : ∑ k ∈ Finset.range (n + 1), a i (n - k)
      = ∑ k ∈ Finset.range (n + 1), a i k :=
    Finset.sum_range_reflect (fun k => a i k) (n + 1)
  have hsign : ((-1 : ℝ)) ^ (i - 1) = -1 := by
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hodd : Odd (i - 1) := Nat.Even.sub_odd hi1 hev (by norm_num)
    exact hodd.neg_one_pow
  have hkey : ∑ k ∈ Finset.range (n + 1), a i k
      = (-1) ^ (i - 1) * ∑ k ∈ Finset.range (n + 1), a i (n - k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact hsym i hi k hk
  rw [hrefl, hsign, neg_one_mul] at hkey
  linarith [hkey]

/-- Summability of the base ζ-series `g m = 1/(m+1)^i` for `i ≥ 2`. -/
private lemma summable_zeta_base (i : ℕ) (hi : 2 ≤ i) :
    Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ i) := by
  have h0 : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ i) :=
    Real.summable_one_div_nat_pow.mpr hi
  refine ((summable_nat_add_iff 1).mpr h0).congr (fun k => ?_)
  push_cast; ring

/-- **Tail-to-ζ identity** (paper e07): for `i ≥ 2` and `c ≥ 1`, the shifted tail
`Σ'_{m} 1/(m+c)^i` equals `ζ(i)` minus its first `c−1` terms. -/
private lemma tsum_shift_zeta (c i : ℕ) (hc : 1 ≤ c) (hi : 2 ≤ i) :
    ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + (c : ℝ)) ^ i
      = zetaVal i - ∑ ℓ ∈ Finset.Icc 1 (c - 1), (1 : ℝ) / (ℓ : ℝ) ^ i := by
  have hg := summable_zeta_base i hi
  -- Split `ζ(i)` into its first `c−1` terms and the shifted tail.
  have hsplit := hg.sum_add_tsum_nat_add (c - 1)
  -- Identify the shifted tail with our target series.
  have htail : (∑' m : ℕ, (1 : ℝ) / (((m + (c - 1) : ℕ) : ℝ) + 1) ^ i)
      = ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + (c : ℝ)) ^ i := by
    apply tsum_congr
    intro m
    have : ((m + (c - 1) : ℕ) : ℝ) + 1 = (m : ℝ) + (c : ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub hc]; push_cast; ring
    rw [this]
  -- Reindex the finite head from `range (c-1)` to `Icc 1 (c-1)`.
  have hfin : (∑ ℓ ∈ Finset.Icc 1 (c - 1), (1 : ℝ) / (ℓ : ℝ) ^ i)
      = ∑ j ∈ Finset.range (c - 1), (1 : ℝ) / ((j : ℝ) + 1) ^ i := by
    rw [show Finset.Icc 1 (c - 1) = Finset.Ico 1 c from by
          ext x; rw [Finset.mem_Icc, Finset.mem_Ico]; omega,
      Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  -- Assemble.  `hsplit : head + tail = ∑' g = zetaVal i`.
  have hz : (∑ j ∈ Finset.range (c - 1), (1 : ℝ) / ((j : ℝ) + 1) ^ i)
      + (∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + (c : ℝ)) ^ i) = zetaVal i := by
    rw [zetaVal, ← htail]; exact hsplit
  rw [hfin]
  linarith [hz]

/-- Antitonicity and decay of `m ↦ 1/(m+a)` for `a > 0`. -/
private lemma antitone_tendsto_one_div (a : ℝ) (ha : 0 < a) :
    Antitone (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + a)) ∧
      Filter.Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + a)) Filter.atTop (nhds 0) := by
  refine ⟨?_, ?_⟩
  · intro p q hpq
    have hpq' : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
    have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  · have hd : Filter.Tendsto (fun m : ℕ => (m : ℝ) + a) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ a tendsto_natCast_atTop_atTop
    have h0 : Filter.Tendsto (fun m : ℕ => ((m : ℝ) + a)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hd
    simpa only [one_div] using h0

/-- **Telescoping tsum**: for antitone `w → 0`, `Σ'_m (w m − w (m+1)) = w 0`. -/
private lemma tsum_telescope_nonneg (w : ℕ → ℝ)
    (hanti : Antitone w) (hw : Filter.Tendsto w Filter.atTop (nhds 0)) :
    Summable (fun m => w m - w (m + 1)) ∧ ∑' m, (w m - w (m + 1)) = w 0 := by
  have hwnn : ∀ n, 0 ≤ w n := hanti.le_of_tendsto hw
  have hnn : ∀ m, 0 ≤ w m - w (m + 1) := fun m => sub_nonneg.mpr (hanti (Nat.le_succ m))
  have hpart : ∀ M, ∑ m ∈ Finset.range M, (w m - w (m + 1)) = w 0 - w M :=
    fun M => Finset.sum_range_sub' w M
  have hsum : Summable (fun m => w m - w (m + 1)) := by
    apply summable_of_sum_range_le hnn
    intro M; rw [hpart]; linarith [hwnn M]
  refine ⟨hsum, ?_⟩
  have h1 := hsum.hasSum.tendsto_sum_nat
  have h2 : Filter.Tendsto (fun M => ∑ m ∈ Finset.range M, (w m - w (m + 1)))
      Filter.atTop (nhds (w 0)) := by
    simp_rw [hpart]
    simpa using hw.const_sub (w 0)
  exact tendsto_nhds_unique h1 h2

/-- **Harmonic telescoping** (paper e07, `i = 1` column): the divergent tails cancel to a
finite harmonic number.  Used with `Σ_k a_{1,k} = 0` for the `i = 1` residue. -/
private lemma tsum_harmonic (k : ℕ) :
    ∑' m : ℕ, ((1 : ℝ) / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1))
      = -∑ ℓ ∈ Finset.Icc 1 k, (1 : ℝ) / (ℓ : ℝ) := by
  -- Per-column telescoping pieces `e j m = wj (m+1) − wj m`, `wj m = 1/(m + (j+1))`.
  have hej : ∀ j : ℕ,
      Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + ((j : ℝ) + 2)) - 1 / ((m : ℝ) + ((j : ℝ) + 1)))
      ∧ (∑' m : ℕ, ((1 : ℝ) / ((m : ℝ) + ((j : ℝ) + 2)) - 1 / ((m : ℝ) + ((j : ℝ) + 1))))
          = -(1 / ((j : ℝ) + 1)) := by
    intro j
    obtain ⟨hanti, htend⟩ := antitone_tendsto_one_div ((j : ℝ) + 1) (by positivity)
    obtain ⟨hs, hval⟩ := tsum_telescope_nonneg (fun m => (1 : ℝ) / ((m : ℝ) + ((j : ℝ) + 1)))
      hanti htend
    -- `wj (m+1) - wj m = (1/(m+(j+2)) - 1/(m+(j+1)))`.
    have hcongr : ∀ m : ℕ,
        (1 : ℝ) / ((m : ℝ) + ((j : ℝ) + 2)) - 1 / ((m : ℝ) + ((j : ℝ) + 1))
          = -((1 : ℝ) / ((m : ℝ) + ((j : ℝ) + 1)) - 1 / (((m + 1 : ℕ) : ℝ) + ((j : ℝ) + 1))) := by
      intro m; push_cast; ring
    constructor
    · exact (hs.neg).congr (fun m => (hcongr m).symm)
    · rw [tsum_congr hcongr, tsum_neg, hval]; simp
  -- Assemble via a finite telescoping over `j ∈ range k`.
  have hpt : ∀ m : ℕ,
      (1 : ℝ) / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1)
        = ∑ j ∈ Finset.range k,
            ((1 : ℝ) / ((m : ℝ) + ((j : ℝ) + 2)) - 1 / ((m : ℝ) + ((j : ℝ) + 1))) := by
    intro m
    have hstep : ∀ K : ℕ,
        (∑ j ∈ Finset.range K,
            ((1 : ℝ) / ((m : ℝ) + ((j : ℝ) + 2)) - 1 / ((m : ℝ) + ((j : ℝ) + 1))))
          = (1 : ℝ) / ((m : ℝ) + ((K : ℝ) + 1)) - 1 / ((m : ℝ) + 1) := by
      intro K
      induction K with
      | zero => simp
      | succ K ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
    rw [hstep k]; ring
  rw [tsum_congr hpt]
  rw [Summable.tsum_finsetSum (fun j _ => (hej j).1)]
  have hval2 : ∀ j ∈ Finset.range k,
      (∑' m : ℕ, ((1 : ℝ) / ((m : ℝ) + ((j : ℝ) + 2)) - 1 / ((m : ℝ) + ((j : ℝ) + 1))))
        = -(1 / ((j : ℝ) + 1)) := fun j _ => (hej j).2
  rw [Finset.sum_congr rfl hval2]
  rw [Finset.sum_neg_distrib]
  congr 1
  -- `∑_{j<k} 1/(j+1) = ∑_{ℓ∈Icc 1 k} 1/ℓ`.
  rw [show Finset.Icc 1 k = Finset.Ico 1 (k + 1) from by
        ext x; rw [Finset.mem_Icc, Finset.mem_Ico]; omega,
    Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  push_cast; ring

/-- Summability of a finite sum of summable series. -/
private lemma summable_finset_sum (s : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ i ∈ s, Summable (fun m => f i m)) :
    Summable (fun m => ∑ i ∈ s, f i m) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert a s ha ih =>
    intro hf
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Summability of the shifted power series `1/(m+c)^i` for `i ≥ 2`, `c ≥ 1`. -/
private lemma summable_shift_pow (c i : ℕ) (hc : 1 ≤ c) (hi : 2 ≤ i) :
    Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + (c : ℝ)) ^ i) := by
  have h := (summable_nat_add_iff (c - 1)).2 (summable_zeta_base i hi)
  refine h.congr (fun m => ?_)
  rw [show (((m + (c - 1) : ℕ) : ℝ) + 1) = (m : ℝ) + (c : ℝ) from by
    rw [Nat.cast_add, Nat.cast_sub hc]; push_cast; ring]

/-- Summability of the telescoping column difference. -/
private lemma summable_telescope_col (j : ℕ) :
    Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + ((j : ℝ) + 2)) - 1 / ((m : ℝ) + ((j : ℝ) + 1))) := by
  obtain ⟨hanti, htend⟩ := antitone_tendsto_one_div ((j : ℝ) + 1) (by positivity)
  obtain ⟨hs, _⟩ := tsum_telescope_nonneg (fun m => (1 : ℝ) / ((m : ℝ) + ((j : ℝ) + 1)))
    hanti htend
  refine (hs.neg).congr (fun m => ?_)
  push_cast; ring

/-- Summability of the `i = 1` harmonic difference `1/(m+1+k) − 1/(m+1)`. -/
private lemma summable_harmonic_diff (k : ℕ) :
    Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1)) := by
  have hpt : (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1))
      = (fun m : ℕ => ∑ j ∈ Finset.range k,
          ((1 : ℝ) / ((m : ℝ) + ((j : ℝ) + 2)) - 1 / ((m : ℝ) + ((j : ℝ) + 1)))) := by
    funext m
    have hstep : ∀ K : ℕ,
        (∑ j ∈ Finset.range K,
            ((1 : ℝ) / ((m : ℝ) + ((j : ℝ) + 2)) - 1 / ((m : ℝ) + ((j : ℝ) + 1))))
          = (1 : ℝ) / ((m : ℝ) + ((K : ℝ) + 1)) - 1 / ((m : ℝ) + 1) := by
      intro K
      induction K with
      | zero => simp
      | succ K ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
    rw [hstep k]; ring
  rw [hpt]
  exact summable_finset_sum (Finset.range k) _ (fun j _ => summable_telescope_col j)

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
  classical
  -- Partial-fraction data (e04 decomposition, Lemma-1 integrality, Lemma-2 symmetry).
  obtain ⟨a, _hdec, hint, _hsym⟩ := partialFraction_exists n
  -- Column totals `S i = Σ_k a_{i,k}` (paper's `a_i`, `â_i` — they coincide across the two forms).
  set S : ℕ → ℝ := fun i => ∑ k ∈ Finset.range (n + 1), a i k with hSdef
  -- Integrality of the totals: `d_n^{33-i} · S i ∈ ℤ` (sum Lemma 1 over `k`).
  have hSint : ∀ i, ∃ z : ℤ, i ∈ Finset.Icc 1 33 →
      (Nat.lcmUpto n : ℝ) ^ (33 - i) * S i = z := by
    intro i
    by_cases hi : i ∈ Finset.Icc 1 33
    · have hzk : ∀ k, ∃ z : ℤ, k ∈ Finset.range (n + 1) →
          (Nat.lcmUpto n : ℝ) ^ (33 - i) * a i k = z := by
        intro k
        by_cases hk : k ∈ Finset.range (n + 1)
        · obtain ⟨z, hz⟩ := hint i hi k hk; exact ⟨z, fun _ => hz⟩
        · exact ⟨0, fun h => absurd h hk⟩
      choose zc hzc using hzk
      refine ⟨∑ k ∈ Finset.range (n + 1), zc k, fun _ => ?_⟩
      simp only [hSdef, Finset.mul_sum, Int.cast_sum]
      exact Finset.sum_congr rfl (fun k hk => hzc k hk)
    · exact ⟨0, fun h => absurd h hi⟩
  -- The integer coefficients `B i` with `d_n^{33} · S i = d_n^i · B i` for `i ≤ 33`.
  choose B hB using hSint
  have hBrel : ∀ i ∈ oddIdx3, (Nat.lcmUpto n : ℝ) ^ i * (B i : ℝ)
      = (Nat.lcmUpto n : ℝ) ^ 33 * S i := by
    intro i hi
    have hi' : i ∈ Finset.Icc 1 33 := by
      have hi3 : i ∈ Finset.Icc 3 33 := by
        have := hi; rw [oddIdx3, Finset.mem_filter] at this; exact this.1
      rw [Finset.mem_Icc] at hi3 ⊢; omega
    have h1 := hB i hi'
    have hpow : (Nat.lcmUpto n : ℝ) ^ 33
        = (Nat.lcmUpto n : ℝ) ^ i * (Nat.lcmUpto n : ℝ) ^ (33 - i) := by
      rw [← pow_add]; congr 1; rw [Finset.mem_Icc] at hi'; omega
    rw [hpow, mul_assoc, h1]
  -- Fold the integer coefficients back into the two ζ-sums.
  have hsum_r : (∑ i ∈ oddIdx3, (Nat.lcmUpto n : ℝ) ^ i * (B i : ℝ) * zetaVal i)
      = ∑ i ∈ oddIdx3, (Nat.lcmUpto n : ℝ) ^ 33 * S i * zetaVal i :=
    Finset.sum_congr rfl (fun i hi => by rw [hBrel i hi])
  have hsum_rhat :
      (∑ i ∈ oddIdx3, (Nat.lcmUpto n : ℝ) ^ i * (B i : ℝ) * ((2 : ℝ) ^ i - 1) * zetaVal i)
      = ∑ i ∈ oddIdx3, (Nat.lcmUpto n : ℝ) ^ 33 * S i * ((2 : ℝ) ^ i - 1) * zetaVal i :=
    Finset.sum_congr rfl (fun i hi => by rw [hBrel i hi])
  -- ANALYTIC HEART (paper Lemma 3, e07/e08): the two series representations in terms of the
  -- column totals `S i`.  Proving this is the remaining `sorry`; see report for the exact gap.
  have hraw : ∃ B0 Bhat0 : ℤ,
      (Nat.lcmUpto n : ℝ) ^ 33 * r 17 n
        = (∑ i ∈ oddIdx3, (Nat.lcmUpto n : ℝ) ^ 33 * S i * zetaVal i) + (B0 : ℝ)
      ∧ (Nat.lcmUpto n : ℝ) ^ 33 * rhat 17 n
        = (∑ i ∈ oddIdx3, (Nat.lcmUpto n : ℝ) ^ 33 * S i * ((2 : ℝ) ^ i - 1) * zetaVal i)
            + (Bhat0 : ℝ) := by
    sorry
  obtain ⟨B0, Bhat0, hr, hrh⟩ := hraw
  exact ⟨B, B0, Bhat0, by rw [hsum_r]; exact hr, by rw [hsum_rhat]; exact hrh⟩

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
