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
  * `Rn`, `repr_combined` — the `r_n` (e07) representation is PROVED (Lemma 3 assembly:
      reindexing, `S 1 = 0` via harmonic divergence, even-column vanishing, tail-to-ζ,
      interchange, integer constant).  The `r̂_n` (e08) representation `repr_rhat_e08` is now
      also PROVED sorry-free.  Its analytic ingredients are the summation shift
      `rhat = Σ'_j R_n(j−m−½)` (`rhat_shift`), the shifted half-integer tail evaluations
      `tail_val_pos`/`tail_val_neg` (each `= (2^i−1)ζ(i) + small head`), the odd ζ-sum
      `tsum_odd_eq`, and the head integralities `odd_harmonic_integrality` (`i ≥ 2`) and
      `signed_harmonic_integrality` (`i = 1`).  The final assembly mirrors the e07 half:
      it decomposes each `R_n(j−m−½)` via `hdec`, interchanges `Σ'_j` with the finite `i,k`
      sums, splits `k ≤ m` / `k ≥ m+1`, collects the `(2^i−1)ζ(i)` coefficients onto `oddIdx3`
      (even columns drop by `column_even_zero`, `i=1` by `column1_sum_zero`), and evaluates the
      `i=1` block by the negative-base telescoping `tsum_neg_harmonic`; the `n = 0` base case is
      handled directly.  All finite heads times `d^33` are integers, collected into `Bhat0`.
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

/-! ### Elementary two-pole partial fraction (engine for Lemma 1 integrality) -/

/-- **Two-pole partial fraction.**  For `u ≠ 0`, `δ ≠ 0`, `u+δ ≠ 0`:
`1/(uⁱ·(u+δ)) = Σ_{r<i} (-1)ʳ/δ^{r+1}/u^{i-r} + (-1)ⁱ/δⁱ/(u+δ)`.
With `u = t+k`, `δ = m-k` (so `u+δ = t+m`), this expands `1/[(t+k)ⁱ(t+m)]` into
partial fractions at the poles `-k` (orders `1..i`) and `-m` (order `1`), with the
coefficients being `±1/(m-k)^p`; multiplying by `d_n^p` clears them (Lemma 1). -/
private lemma pf_two_pole (i : ℕ) (u δ : ℝ) (hu : u ≠ 0) (hδ : δ ≠ 0) (huδ : u + δ ≠ 0) :
    1 / (u ^ i * (u + δ))
      = (∑ r ∈ Finset.range i, (-1 : ℝ) ^ r / δ ^ (r + 1) / u ^ (i - r))
        + (-1 : ℝ) ^ i / δ ^ i / (u + δ) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hSrec : (∑ r ∈ Finset.range (i + 1), (-1 : ℝ) ^ r / δ ^ (r + 1) / u ^ (i + 1 - r))
        = (1 / u) * (∑ r ∈ Finset.range i, (-1 : ℝ) ^ r / δ ^ (r + 1) / u ^ (i - r))
          + (-1 : ℝ) ^ i / δ ^ (i + 1) / u := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mem_range] at hr
        rw [show i + 1 - r = (i - r) + 1 from by omega, pow_succ]
        field_simp; ring
      · rw [show i + 1 - i = 1 from by omega, pow_one]
    have hkey : (1 : ℝ) / (u ^ (i + 1) * (u + δ)) = (1 / u) * (1 / (u ^ i * (u + δ))) := by
      rw [pow_succ]; field_simp
    have hsgn : (-1 : ℝ) ^ (i + 1) = -((-1) ^ i) := by rw [pow_succ]; ring
    rw [hkey, ih, hSrec, mul_add, hsgn]
    field_simp
    ring

/-! ### Product of `simple` integer functions: decomposition + integrality (paper Lemma 1) -/

/-- A `simple` rational function `Σ_{k=0}^n c_k/(t+k)` with integer coefficients `c`
(the building blocks of tex 96–114). -/
private noncomputable def simpleFn (n : ℕ) (c : ℕ → ℤ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (c k : ℝ) / (t + (k : ℝ))

/-- Product of the `simple` functions in the list `cs`. -/
private noncomputable def simpleProd (n : ℕ) (cs : List (ℕ → ℤ)) (t : ℝ) : ℝ :=
  (cs.map (fun c => simpleFn n c t)).prod

/-- **Multiply a decomposition by one `simple` integer function** (the inductive step of
paper Lemma 1, tex 138–153).  If `G` decomposes as `Σ_{i≤L} Σ_k a_{i,k}/(t+k)^i` with
`d_n^{L-i} a_{i,k} ∈ ℤ`, then `simpleFn c · G` decomposes to order `L+1` with
`d_n^{L+1-i} a'_{i,k} ∈ ℤ`.  The new coefficients arise from `pf_two_pole` applied to each
cross term `1/[(t+m)(t+k)^i]`; the extra `d_n` powers are absorbed by `d_n/(m-k) ∈ ℤ`
(`dvd_lcmUpto`, since `|m-k| ≤ n`).  [PROOF: `sorry` — the coefficient-collection algebra.] -/
private theorem pf_mul_simple (n L : ℕ) (hL : 1 ≤ L) (c : ℕ → ℤ) (G : ℝ → ℝ)
    (a : ℕ → ℕ → ℝ)
    (hdec : ∀ t : ℝ, (∀ k ∈ Finset.range (n + 1), t + (k : ℝ) ≠ 0) →
        G t = ∑ i ∈ Finset.Icc 1 L, ∑ k ∈ Finset.range (n + 1), a i k / (t + (k : ℝ)) ^ i)
    (hint : ∀ i ∈ Finset.Icc 1 L, ∀ k ∈ Finset.range (n + 1),
        ∃ z : ℤ, (Nat.lcmUpto n : ℝ) ^ (L - i) * a i k = z) :
    ∃ a' : ℕ → ℕ → ℝ,
      (∀ t : ℝ, (∀ k ∈ Finset.range (n + 1), t + (k : ℝ) ≠ 0) →
          simpleFn n c t * G t
            = ∑ i ∈ Finset.Icc 1 (L + 1), ∑ k ∈ Finset.range (n + 1), a' i k / (t + (k : ℝ)) ^ i)
      ∧ (∀ i ∈ Finset.Icc 1 (L + 1), ∀ k ∈ Finset.range (n + 1),
          ∃ z : ℤ, (Nat.lcmUpto n : ℝ) ^ (L + 1 - i) * a' i k = z) := by
  sorry

/-- **Product of `simple` integer functions decomposes with integrality** (paper Lemma 1).
By induction on the list `cs`, base case a singleton, inductive step `pf_mul_simple`. -/
private theorem pf_prod (n : ℕ) (cs : List (ℕ → ℤ)) (hcs : cs ≠ []) :
    ∃ a : ℕ → ℕ → ℝ,
      (∀ t : ℝ, (∀ k ∈ Finset.range (n + 1), t + (k : ℝ) ≠ 0) →
          simpleProd n cs t
            = ∑ i ∈ Finset.Icc 1 cs.length, ∑ k ∈ Finset.range (n + 1), a i k / (t + (k : ℝ)) ^ i)
      ∧ (∀ i ∈ Finset.Icc 1 cs.length, ∀ k ∈ Finset.range (n + 1),
          ∃ z : ℤ, (Nat.lcmUpto n : ℝ) ^ (cs.length - i) * a i k = z) := by
  induction cs with
  | nil => exact absurd rfl hcs
  | cons c rest ih =>
    rcases eq_or_ne rest [] with hrest | hrest
    · -- singleton base: `cs = [c]`, length 1, `a 1 k = c k`.
      subst hrest
      refine ⟨fun i k => if i = 1 then (c k : ℝ) else 0, ?_, ?_⟩
      · intro t ht
        simp only [simpleProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, List.length_cons, List.length_nil, Nat.zero_add, Finset.Icc_self,
          Finset.sum_singleton, if_pos, pow_one]
        rfl
      · intro i hi k hk
        rw [Finset.mem_Icc] at hi
        have hi1 : i = 1 := by
          have : (([c]).length) = 1 := rfl
          omega
        subst hi1
        exact ⟨c k, by simp⟩
    · -- inductive step: peel `c`, apply `pf_mul_simple`.
      obtain ⟨a, hdec, hint⟩ := ih hrest
      have hL : 1 ≤ rest.length := by
        cases rest with
        | nil => exact absurd rfl hrest
        | cons _ _ => simp
      obtain ⟨a', hdec', hint'⟩ :=
        pf_mul_simple n rest.length hL c (simpleProd n rest) a hdec hint
      have hlen : (c :: rest).length = rest.length + 1 := by simp
      refine ⟨a', ?_, ?_⟩
      · intro t ht
        have hfac : simpleProd n (c :: rest) t = simpleFn n c t * simpleProd n rest t := by
          simp [simpleProd, List.map_cons, List.prod_cons]
        rw [hfac, hdec' t ht, hlen]
      · intro i hi k hk
        rw [hlen] at hi ⊢
        exact hint' i hi k hk

/-! ### The six explicit integer coefficient arrays (tex 96–114) -/

/-- `f1 = n!/∏(t+j)`: coefficient `(-1)^k C(n,k)` (tex 98). -/
private def pfC1 (n : ℕ) : ℕ → ℤ := fun k => (-1 : ℤ) ^ k * (n.choose k : ℤ)
/-- `f2 = ∏(t-j)/∏(t+j)`: coefficient `(-1)^{n+k} C(n+k,n) C(n,k)` (tex 101). -/
private def pfC2 (n : ℕ) : ℕ → ℤ := fun k => (-1 : ℤ) ^ (n + k) * ((n + k).choose n : ℤ) * (n.choose k : ℤ)
/-- `f3 = ∏(t+n+j)/∏(t+j)`: coefficient `(-1)^k C(2n-k,n) C(n,k)` (tex 104). -/
private def pfC3 (n : ℕ) : ℕ → ℤ := fun k => (-1 : ℤ) ^ k * ((2 * n - k).choose n : ℤ) * (n.choose k : ℤ)
/-- `f4 = 2^{2n}∏(t+½-j)/∏(t+j)`: coefficient `(-1)^{n+k} C(2n+2k,2n) C(2n,n+k)` (tex 107). -/
private def pfC4 (n : ℕ) : ℕ → ℤ :=
  fun k => (-1 : ℤ) ^ (n + k) * ((2 * n + 2 * k).choose (2 * n) : ℤ) * ((2 * n).choose (n + k) : ℤ)
/-- `f5 = 2^{2n}∏(t-½+j)/∏(t+j)`: coefficient `C(2k,k) C(2n-2k,n-k)` (tex 110). -/
private def pfC5 (n : ℕ) : ℕ → ℤ :=
  fun k => ((2 * k).choose k : ℤ) * ((2 * n - 2 * k).choose (n - k) : ℤ)
/-- `f6 = 2^{2n}∏(t+n-½+j)/∏(t+j)`: coefficient `(-1)^k C(4n-2k,2n) C(2n,k)` (tex 113). -/
private def pfC6 (n : ℕ) : ℕ → ℤ :=
  fun k => (-1 : ℤ) ^ k * ((4 * n - 2 * k).choose (2 * n) : ℤ) * ((2 * n).choose k : ℤ)

/-- The list of `33` `simple`-function coefficient arrays whose product is `R_n(t)`:
`28` copies of `f1` (from the `n!^{28}` prefactor `= (n!/∏(t+j))^{28}·∏(t+j)^{28}` absorbed
into the denominator power), followed by `f2, f3, f4, f5, f6`.  See `Rn_as_simpleProd`. -/
private def pfList (n : ℕ) : List (ℕ → ℤ) :=
  List.replicate 28 (pfC1 n) ++ [pfC2 n, pfC3 n, pfC4 n, pfC5 n, pfC6 n]

/-- **`R_n` as a product of the six `simple` integer functions** (tex 115–119):
`R_n(t) = f1(t)^{28}·f2(t)·f3(t)·f4(t)·f5(t)·f6(t)`, i.e. `simpleProd n (pfList n) t`, using the
six partial-fraction identities of tex 96–114.  [PROOF: `sorry` — the six single-power
identities (each provable by clearing denominators at the `n+1` points `t=-k`) plus the
product-of-factorials bookkeeping that matches `n!^{28}`, `2^{6n}` and the `33` denominator
power, analogous to `Rn_eq_c`.] -/
private theorem Rn_as_simpleProd (n : ℕ) (t : ℝ)
    (ht : ∀ k ∈ Finset.range (n + 1), t + (k : ℝ) ≠ 0) :
    Rn 17 n t = simpleProd n (pfList n) t := by
  sorry

/-! ### Partial fractions with the coefficients `a_{i,k}` (paper e04 + Lemmas 1, 2) -/

/-- **Decomposition (e04) + integrality (Lemma 1)** for `R_n` at `s = 33`.
ASSEMBLED from `pf_prod` (the abstract decomposition-with-integrality of a product of `simple`
integer functions, whose analytic engine `pf_two_pole` and inductive step `pf_mul_simple` sit
above) applied to `pfList n`, together with `Rn_as_simpleProd` (the algebraic identity
`R_n = simpleProd (pfList n)`).  `pfList n` has length `33`, giving `Icc 1 33` and the exponent
`33 - i`.  These two conjuncts are exactly what `repr_combined` still needs. -/
private theorem pf_decomp (n : ℕ) :
    ∃ a : ℕ → ℕ → ℝ,
      (∀ t : ℝ, (∀ k ∈ Finset.range (n + 1), t + (k : ℝ) ≠ 0) →
          Rn 17 n t = ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1),
              a i k / (t + (k : ℝ)) ^ i)
      ∧ (∀ i ∈ Finset.Icc 1 33, ∀ k ∈ Finset.range (n + 1),
          ∃ z : ℤ, (Nat.lcmUpto n : ℝ) ^ (33 - i) * a i k = z) := by
  have hlen : (pfList n).length = 33 := by
    simp [pfList, List.length_append, List.length_replicate]
  have hne : pfList n ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen
  obtain ⟨a, hdec, hint⟩ := pf_prod n (pfList n) hne
  rw [hlen] at hdec hint
  refine ⟨a, ?_, hint⟩
  intro t ht
  rw [Rn_as_simpleProd n t ht, hdec t ht]

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

/-! ### Half-integer harmonic machinery for the `r̂_n` form (paper e08) -/

/-- **Odd half-integer harmonic integrality** (paper Lemma 3, e08 inclusions, tex 236–237):
`d_n^i · 2^i · Σ_{ℓ<L} 1/(2ℓ+1)^i ∈ ℤ` whenever the largest odd denominator `2L−1 ≤ n`
(equivalently `2L ≤ n+1`), so every `2ℓ+1 ≤ n` is cleared by `d_n` via `dvd_lcmUpto`; the
`2^i` from `(ℓ+½) = (2ℓ+1)/2` is an integer factor. -/
theorem odd_harmonic_integrality (n i L : ℕ) (hL : 2 * L ≤ n + 1) :
    ∃ z : ℤ, (Nat.lcmUpto n : ℝ) ^ i
        * ((2 : ℝ) ^ i * ∑ ℓ ∈ Finset.range L, (1 : ℝ) / ((2 * ℓ + 1 : ℕ) : ℝ) ^ i) = z := by
  refine ⟨∑ ℓ ∈ Finset.range L, ((2 * (Nat.lcmUpto n / (2 * ℓ + 1)) : ℕ) : ℤ) ^ i, ?_⟩
  rw [Finset.mul_sum, Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  rw [Finset.mem_range] at hℓ
  have hodd : (2 * ℓ + 1) ∣ Nat.lcmUpto n := dvd_lcmUpto (by omega) (by omega)
  have hne : ((2 * ℓ + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Int.cast_pow, Int.cast_natCast, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_div hodd hne,
    mul_pow, div_pow, mul_one_div]
  ring

/-- Summability of the odd-denominator ζ-series `1/(2r+1)^i` for `i ≥ 2`. -/
private lemma summable_odd_base (i : ℕ) (hi : 2 ≤ i) :
    Summable (fun r : ℕ => (1 : ℝ) / ((2 * r + 1 : ℕ) : ℝ) ^ i) := by
  apply Summable.of_nonneg_of_le (f := fun r : ℕ => (1 : ℝ) / ((r : ℝ) + 1) ^ i)
  · intro r; positivity
  · intro r
    have hb : ((r : ℝ) + 1) ≤ ((2 * r + 1 : ℕ) : ℝ) := by
      have h : ((2 * r + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + 1 := by push_cast; ring
      rw [h]; linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ (r : ℝ))]
    have hpow : ((r : ℝ) + 1) ^ i ≤ ((2 * r + 1 : ℕ) : ℝ) ^ i :=
      pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (r : ℝ) + 1) hb i
    exact one_div_le_one_div_of_le (by positivity) hpow
  · exact summable_zeta_base i hi

/-- **Odd ζ-sum** (paper e08): for `i ≥ 2`, `2^i · Σ'_r 1/(2r+1)^i = (2^i − 1)·ζ(i)`.
Proved by splitting `ζ(i) = Σ' 1/(n+1)^i` into its even/odd index parts. -/
private lemma tsum_odd_eq (i : ℕ) (hi : 2 ≤ i) :
    (2 : ℝ) ^ i * ∑' r : ℕ, (1 : ℝ) / ((2 * r + 1 : ℕ) : ℝ) ^ i
      = ((2 : ℝ) ^ i - 1) * zetaVal i := by
  have hgf : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ i) := summable_zeta_base i hi
  have hinj2 : Function.Injective (fun r : ℕ => 2 * r) := by intro a b h; simpa using h
  have hinj2' : Function.Injective (fun r : ℕ => 2 * r + 1) := by intro a b h; simpa using h
  have he : Summable (fun k => (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ i) (2 * k)) :=
    hgf.comp_injective hinj2
  have ho : Summable (fun k => (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ i) (2 * k + 1)) :=
    hgf.comp_injective hinj2'
  have hsplit := tsum_even_add_odd (f := fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ i) he ho
  have hOdd : (∑' k, (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ i) (2 * k))
      = ∑' r : ℕ, (1 : ℝ) / ((2 * r + 1 : ℕ) : ℝ) ^ i := by
    apply tsum_congr; intro k; show (1 : ℝ) / (((2 * k : ℕ) : ℝ) + 1) ^ i = _
    push_cast; ring_nf
  have hEven : (2 : ℝ) ^ i * (∑' k, (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ i) (2 * k + 1))
      = zetaVal i := by
    rw [← tsum_mul_left, zetaVal]
    apply tsum_congr; intro k
    show (2 : ℝ) ^ i * ((1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ i) = (1 : ℝ) / ((k : ℝ) + 1) ^ i
    have h2 : ((2 * k + 1 : ℕ) : ℝ) + 1 = 2 * ((k : ℝ) + 1) := by push_cast; ring
    rw [h2, mul_pow]; field_simp
  have hzeta : (∑' k, (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ i) k) = zetaVal i := by rw [zetaVal]
  rw [hOdd, hzeta] at hsplit
  linear_combination (2 : ℝ) ^ i * hsplit - hEven

/-- Summability of the shifted half-integer series with positive base `1/(j+c−½)^i`. -/
private lemma summable_half_pos (c i : ℕ) (hc : 1 ≤ c) (hi : 2 ≤ i) :
    Summable (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + (c : ℝ) - 1 / 2) ^ i) := by
  have hc' : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  apply Summable.of_nonneg_of_le (f := fun j : ℕ => (2 : ℝ) ^ i * ((1 : ℝ) / ((j : ℝ) + 1) ^ i))
  · intro j
    have hbpos : (0 : ℝ) < (j : ℝ) + (c : ℝ) - 1 / 2 := by
      have := Nat.cast_nonneg (α := ℝ) j; linarith
    exact div_nonneg zero_le_one (pow_pos hbpos i).le
  · intro j
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hbase : ((j : ℝ) + 1) / 2 ≤ (j : ℝ) + (c : ℝ) - 1 / 2 := by linarith
    have hbpos : (0 : ℝ) < ((j : ℝ) + 1) / 2 := by positivity
    have hpow : (((j : ℝ) + 1) / 2) ^ i ≤ ((j : ℝ) + (c : ℝ) - 1 / 2) ^ i :=
      pow_le_pow_left₀ hbpos.le hbase i
    have h1 : (1 : ℝ) / ((j : ℝ) + (c : ℝ) - 1 / 2) ^ i ≤ 1 / (((j : ℝ) + 1) / 2) ^ i :=
      one_div_le_one_div_of_le (by positivity) hpow
    have h2 : (1 : ℝ) / (((j : ℝ) + 1) / 2) ^ i = (2 : ℝ) ^ i * (1 / ((j : ℝ) + 1) ^ i) := by
      rw [div_pow, one_div_div]; ring
    rw [h2] at h1; exact h1
  · exact (summable_zeta_base i hi).mul_left ((2 : ℝ) ^ i)

/-- Summability of the shifted half-integer series with negative base `1/(j−p−½)^i`. -/
private lemma summable_half_neg (p i : ℕ) (hi : 2 ≤ i) :
    Summable (fun j : ℕ => (1 : ℝ) / ((j : ℝ) - (p : ℝ) - 1 / 2) ^ i) := by
  have hg := summable_odd_base i hi
  have hshift : Summable (fun r : ℕ =>
      (fun j : ℕ => (1 : ℝ) / ((j : ℝ) - (p : ℝ) - 1 / 2) ^ i) (r + (p + 1))) := by
    refine (hg.mul_left ((2 : ℝ) ^ i)).congr (fun r => ?_)
    show (2 : ℝ) ^ i * ((1 : ℝ) / ((2 * r + 1 : ℕ) : ℝ) ^ i)
        = (1 : ℝ) / (((r + (p + 1) : ℕ) : ℝ) - (p : ℝ) - 1 / 2) ^ i
    have hbase : (((r + (p + 1) : ℕ) : ℝ) - (p : ℝ) - 1 / 2) = ((2 * r + 1 : ℕ) : ℝ) / 2 := by
      push_cast; ring
    rw [hbase, div_pow, one_div_div, mul_one_div]
  exact (summable_nat_add_iff (p + 1)).1 hshift

/-- **Positive-base half-integer tail** (paper e08, `k ≥ m+1` columns): for `i ≥ 2`, `c ≥ 1`,
`Σ'_j 1/(j+c−½)^i = (2^i−1)ζ(i) − 2^i·Σ_{ℓ<c−1} 1/(2ℓ+1)^i`.  The harmonic head has odd
denominators `≤ 2c−3`, small enough to be cleared by `d_n`. -/
private lemma tail_val_pos (c i : ℕ) (hc : 1 ≤ c) (hi : 2 ≤ i) :
    ∑' j : ℕ, (1 : ℝ) / ((j : ℝ) + (c : ℝ) - 1 / 2) ^ i
      = ((2 : ℝ) ^ i - 1) * zetaVal i
        - (2 : ℝ) ^ i * ∑ ℓ ∈ Finset.range (c - 1), (1 : ℝ) / ((2 * ℓ + 1 : ℕ) : ℝ) ^ i := by
  have hg := summable_odd_base i hi
  have hrw : (∑' j : ℕ, (1 : ℝ) / ((j : ℝ) + (c : ℝ) - 1 / 2) ^ i)
      = (2 : ℝ) ^ i * ∑' j : ℕ, (1 : ℝ) / ((2 * (j + (c - 1)) + 1 : ℕ) : ℝ) ^ i := by
    rw [← tsum_mul_left]
    apply tsum_congr; intro j
    show (1 : ℝ) / ((j : ℝ) + (c : ℝ) - 1 / 2) ^ i
        = (2 : ℝ) ^ i * ((1 : ℝ) / ((2 * (j + (c - 1)) + 1 : ℕ) : ℝ) ^ i)
    have hbase : ((j : ℝ) + (c : ℝ) - 1 / 2) = ((2 * (j + (c - 1)) + 1 : ℕ) : ℝ) / 2 := by
      have hnat : (2 * (j + (c - 1)) + 1 : ℕ) = 2 * j + 2 * c - 1 := by omega
      rw [hnat, Nat.cast_sub (by omega : 1 ≤ 2 * j + 2 * c)]; push_cast; ring
    rw [hbase, div_pow, one_div_div, mul_one_div]
  rw [hrw]
  have hsplit := hg.sum_add_tsum_nat_add (c - 1)
  have key : (2 : ℝ) ^ i * (∑' j : ℕ, (1 : ℝ) / ((2 * (j + (c - 1)) + 1 : ℕ) : ℝ) ^ i)
      = (2 : ℝ) ^ i * ((∑' r : ℕ, (1 : ℝ) / ((2 * r + 1 : ℕ) : ℝ) ^ i)
          - ∑ r ∈ Finset.range (c - 1), (1 : ℝ) / ((2 * r + 1 : ℕ) : ℝ) ^ i) := by
    congr 1
    have hbeta : (∑' j : ℕ, (1 : ℝ) / ((2 * (j + (c - 1)) + 1 : ℕ) : ℝ) ^ i)
        = ∑' j : ℕ, (fun r : ℕ => (1 : ℝ) / ((2 * r + 1 : ℕ) : ℝ) ^ i) (j + (c - 1)) := by
      apply tsum_congr; intro j; rfl
    rw [hbeta]; linarith [hsplit]
  rw [key, mul_sub, tsum_odd_eq i hi]

/-- **Negative-base half-integer tail** (paper e08, `k ≤ m` columns): for `i ≥ 2`, `p : ℕ`,
`Σ'_j 1/(j−p−½)^i = (2^i−1)ζ(i) + (−1)^i·2^i·Σ_{ℓ<p+1} 1/(2ℓ+1)^i`.  The finite head, from the
`p+1` negative-denominator terms, has odd denominators `≤ 2p+1`, cleared by `d_n`. -/
private lemma tail_val_neg (p i : ℕ) (hi : 2 ≤ i) :
    ∑' j : ℕ, (1 : ℝ) / ((j : ℝ) - (p : ℝ) - 1 / 2) ^ i
      = ((2 : ℝ) ^ i - 1) * zetaVal i
        + (-1) ^ i * (2 : ℝ) ^ i
            * ∑ ℓ ∈ Finset.range (p + 1), (1 : ℝ) / ((2 * ℓ + 1 : ℕ) : ℝ) ^ i := by
  have hfsum := summable_half_neg p i hi
  have hsplit := hfsum.sum_add_tsum_nat_add (p + 1)
  -- The infinite tail (`j ≥ p+1`) reindexes to the odd ζ-sum.
  have htailval : (∑' r : ℕ, (1 : ℝ) / (((r + (p + 1) : ℕ) : ℝ) - (p : ℝ) - 1 / 2) ^ i)
      = ((2 : ℝ) ^ i - 1) * zetaVal i := by
    have hcong : ∀ r : ℕ, (1 : ℝ) / (((r + (p + 1) : ℕ) : ℝ) - (p : ℝ) - 1 / 2) ^ i
        = (2 : ℝ) ^ i * ((1 : ℝ) / ((2 * r + 1 : ℕ) : ℝ) ^ i) := by
      intro r
      have hbase : (((r + (p + 1) : ℕ) : ℝ) - (p : ℝ) - 1 / 2) = ((2 * r + 1 : ℕ) : ℝ) / 2 := by
        push_cast; ring
      rw [hbase, div_pow, one_div_div, mul_one_div]
    rw [tsum_congr hcong, tsum_mul_left, tsum_odd_eq i hi]
  -- The finite head (`j = 0,…,p`) reflects to the `(−1)^i 2^i` odd head.
  have hheadval : (∑ j ∈ Finset.range (p + 1), (1 : ℝ) / ((j : ℝ) - (p : ℝ) - 1 / 2) ^ i)
      = (-1) ^ i * (2 : ℝ) ^ i
          * ∑ ℓ ∈ Finset.range (p + 1), (1 : ℝ) / ((2 * ℓ + 1 : ℕ) : ℝ) ^ i := by
    rw [Finset.mul_sum,
      ← Finset.sum_range_reflect (fun j => (1 : ℝ) / ((j : ℝ) - (p : ℝ) - 1 / 2) ^ i) (p + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    show (1 : ℝ) / (((p + 1 - 1 - j : ℕ) : ℝ) - (p : ℝ) - 1 / 2) ^ i
        = (-1) ^ i * (2 : ℝ) ^ i * (1 / ((2 * j + 1 : ℕ) : ℝ) ^ i)
    have hbase : (((p + 1 - 1 - j : ℕ) : ℝ) - (p : ℝ) - 1 / 2) = -(((2 * j + 1 : ℕ) : ℝ) / 2) := by
      rw [show (p + 1 - 1 - j : ℕ) = p - j from by omega, Nat.cast_sub (by omega : j ≤ p)]
      push_cast; ring
    rw [hbase]
    rcases Nat.even_or_odd i with hev | hodd
    · rw [hev.neg_one_pow, hev.neg_pow, div_pow, one_div_div]; ring
    · rw [hodd.neg_one_pow, hodd.neg_pow, div_neg, div_pow, one_div_div]; ring
  calc ∑' j : ℕ, (1 : ℝ) / ((j : ℝ) - (p : ℝ) - 1 / 2) ^ i
      = (∑ j ∈ Finset.range (p + 1), (1 : ℝ) / ((j : ℝ) - (p : ℝ) - 1 / 2) ^ i)
        + (∑' r : ℕ, (1 : ℝ) / (((r + (p + 1) : ℕ) : ℝ) - (p : ℝ) - 1 / 2) ^ i) := hsplit.symm
    _ = ((2 : ℝ) ^ i - 1) * zetaVal i
        + (-1) ^ i * (2 : ℝ) ^ i
            * ∑ ℓ ∈ Finset.range (p + 1), (1 : ℝ) / ((2 * ℓ + 1 : ℕ) : ℝ) ^ i := by
        rw [hheadval, htailval]; ring

/-- **Summation shift for `r̂_n`** (paper tex 220).  Since `R_n` vanishes at the half-integer
nodes `t = −½,−3/2,…,−(n−½)` (zeros of the `∏_{j=1}^{3n}(t−n−½+j)` factor), for `n ≥ 1` and
`m = ⌊(n−1)/2⌋` the twisted sum `r̂_n = Σ'_k R_n(n+½+k)` can be re-started at `t = −m−½`:
`r̂_n = Σ'_j R_n(j − m − ½)`.  The prepended `n+m+1` terms (`j = 0,…,n+m`) all vanish. -/
theorem rhat_shift (n : ℕ) (hn1 : 1 ≤ n) :
    ∑' j : ℕ, Rn 17 n ((j : ℝ) - (((n - 1) / 2 : ℕ) : ℝ) - 1 / 2) = rhat 17 n := by
  set m : ℕ := (n - 1) / 2 with hm_def
  -- `R_n` vanishes at `t = j − m − ½` for `j ≤ n + m` (a zero of the middle `3n`-product).
  have hvanish_half : ∀ j : ℕ, j ≤ n + m → Rn 17 n ((j : ℝ) - (m : ℝ) - 1 / 2) = 0 := by
    intro j hj
    have hP3 : ∏ j' ∈ Finset.Icc 1 (3 * n),
        ((j : ℝ) - (m : ℝ) - 1 / 2 - (n : ℝ) - 1 / 2 + (j' : ℝ)) = 0 := by
      apply Finset.prod_eq_zero (i := n + m + 1 - j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [Nat.cast_sub (by omega : j ≤ n + m + 1)]; push_cast; ring
    simp only [Rn]
    rw [hP3]; ring
  -- Summability of the shifted series (it is the `chat` series after dropping `n+m+1` zeros).
  have hRnhalf_sum : Summable (fun j : ℕ => Rn 17 n ((j : ℝ) - (m : ℝ) - 1 / 2)) := by
    apply (summable_nat_add_iff (n + m + 1)).1
    refine (summable_chat 17 n (by norm_num)).congr (fun k => ?_)
    rw [← Rn_eq_chat 17 n k (by norm_num)]; congr 1; push_cast; ring
  -- Prepended terms vanish; the tail reindexes to `r̂_n`.
  have hhead : (∑ j ∈ Finset.range (n + m + 1), Rn 17 n ((j : ℝ) - (m : ℝ) - 1 / 2)) = 0 :=
    Finset.sum_eq_zero (fun j hj => hvanish_half j (by rw [Finset.mem_range] at hj; omega))
  have htail : (∑' k : ℕ, Rn 17 n (((k + (n + m + 1) : ℕ) : ℝ) - (m : ℝ) - 1 / 2)) = rhat 17 n := by
    show _ = ∑' k, chat 17 n k
    refine tsum_congr (fun k => ?_)
    rw [← Rn_eq_chat 17 n k (by norm_num)]; congr 1; push_cast; ring
  have key := hRnhalf_sum.sum_add_tsum_nat_add (n + m + 1)
  rw [hhead, zero_add] at key
  rw [← key]; exact htail

/-! ### Extra helpers for the `r̂_n` (e08) assembly -/

/-- **General telescoping value**: for a sequence `w → 0` whose consecutive differences are
summable, `Σ'_M (w (M+1) − w M) = −w 0`.  (No sign/antitone hypothesis, unlike
`tsum_telescope_nonneg`.) -/
private lemma tsum_telescope_value (w : ℕ → ℝ)
    (hsum : Summable (fun M : ℕ => w (M + 1) - w M))
    (hlim : Filter.Tendsto w Filter.atTop (nhds 0)) :
    ∑' M : ℕ, (w (M + 1) - w M) = - w 0 := by
  have h1 := hsum.hasSum.tendsto_sum_nat
  have hpart : ∀ N : ℕ, ∑ M ∈ Finset.range N, (w (M + 1) - w M) = w N - w 0 :=
    fun N => Finset.sum_range_sub w N
  have h2 : Filter.Tendsto (fun N : ℕ => ∑ M ∈ Finset.range N, (w (M + 1) - w M))
      Filter.atTop (nhds (0 - w 0)) := by
    simp_rw [hpart]; exact hlim.sub_const (w 0)
  have huniq := tendsto_nhds_unique h1 h2
  rw [huniq]; ring

/-- Summability of the negative-base telescoping column
`1/(M + (ℓ−m−½) + 1) − 1/(M + (ℓ−m−½))` (shift by `m+1` to a positive base). -/
private lemma summable_neg_telescope (m ℓ : ℕ) :
    Summable (fun M : ℕ =>
      (1 : ℝ) / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2) + 1)
        - 1 / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2))) := by
  obtain ⟨hanti, htend⟩ := antitone_tendsto_one_div ((ℓ : ℝ) + 1 / 2) (by positivity)
  obtain ⟨hs, _⟩ := tsum_telescope_nonneg (fun M => (1 : ℝ) / ((M : ℝ) + ((ℓ : ℝ) + 1 / 2)))
    hanti htend
  have hshift : Summable (fun M : ℕ =>
      (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2) + 1)
        - 1 / ((j : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2))) (M + (m + 1))) := by
    refine (hs.neg).congr (fun M => ?_)
    push_cast; ring
  exact (summable_nat_add_iff (m + 1)).1 hshift

/-- **Negative-base harmonic telescoping** (paper e08, `i = 1` column): the divergent tails
cancel to a finite signed-half-integer harmonic number. -/
private lemma tsum_neg_harmonic (m k : ℕ) :
    ∑' M : ℕ, ((1 : ℝ) / ((M : ℝ) - (m : ℝ) - 1 / 2 + (k : ℝ)) - 1 / ((M : ℝ) - (m : ℝ) - 1 / 2))
      = -∑ ℓ ∈ Finset.range k, (1 : ℝ) / ((ℓ : ℝ) - (m : ℝ) - 1 / 2) := by
  -- Per-column summability and value `−1/(ℓ−m−½)`.
  have hej : ∀ ℓ : ℕ,
      Summable (fun M : ℕ => (1 : ℝ) / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2) + 1)
          - 1 / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2)))
      ∧ (∑' M : ℕ, ((1 : ℝ) / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2) + 1)
          - 1 / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2))))
          = -((1 : ℝ) / ((ℓ : ℝ) - (m : ℝ) - 1 / 2)) := by
    intro ℓ
    refine ⟨summable_neg_telescope m ℓ, ?_⟩
    set w : ℕ → ℝ := fun M => (1 : ℝ) / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2)) with hw
    have hCw : ∀ M : ℕ,
        (1 : ℝ) / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2) + 1)
            - 1 / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2)) = w (M + 1) - w M := by
      intro M; simp only [hw]; push_cast; ring
    have hlim : Filter.Tendsto w Filter.atTop (nhds 0) := by
      have hd : Filter.Tendsto (fun M : ℕ => (M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2))
          Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      have h0 : Filter.Tendsto (fun M : ℕ => ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2))⁻¹)
          Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp hd
      simpa only [hw, one_div] using h0
    have hsw : Summable (fun M => w (M + 1) - w M) := (summable_neg_telescope m ℓ).congr hCw
    rw [tsum_congr hCw, tsum_telescope_value w hsw hlim]
    simp only [hw, Nat.cast_zero, zero_add]
  -- Finite telescoping identity over `ℓ ∈ range k`.
  have hpt : ∀ M : ℕ,
      (1 : ℝ) / ((M : ℝ) - (m : ℝ) - 1 / 2 + (k : ℝ)) - 1 / ((M : ℝ) - (m : ℝ) - 1 / 2)
        = ∑ ℓ ∈ Finset.range k,
            ((1 : ℝ) / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2) + 1)
              - 1 / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2))) := by
    intro M
    have hstep : ∀ K : ℕ,
        (∑ ℓ ∈ Finset.range K,
          ((1 : ℝ) / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2) + 1)
            - 1 / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2))))
          = (1 : ℝ) / ((M : ℝ) + ((K : ℝ) - (m : ℝ) - 1 / 2)) - 1 / ((M : ℝ) - (m : ℝ) - 1 / 2) := by
      intro K
      induction K with
      | zero => simp only [Finset.sum_range_zero, Nat.cast_zero]; ring
      | succ K ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
    rw [hstep k]; push_cast; ring
  rw [tsum_congr hpt, Summable.tsum_finsetSum (fun ℓ _ => (hej ℓ).1),
    Finset.sum_congr rfl (fun ℓ _ => (hej ℓ).2), Finset.sum_neg_distrib]

/-- Summability of the `i = 1` negative-base harmonic difference `1/(M−m−½+k) − 1/(M−m−½)`. -/
private lemma summable_neg_harmonic_diff (m k : ℕ) :
    Summable (fun M : ℕ =>
      (1 : ℝ) / ((M : ℝ) - (m : ℝ) - 1 / 2 + (k : ℝ)) - 1 / ((M : ℝ) - (m : ℝ) - 1 / 2)) := by
  have hpt : (fun M : ℕ =>
        (1 : ℝ) / ((M : ℝ) - (m : ℝ) - 1 / 2 + (k : ℝ)) - 1 / ((M : ℝ) - (m : ℝ) - 1 / 2))
      = (fun M : ℕ => ∑ ℓ ∈ Finset.range k,
          ((1 : ℝ) / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2) + 1)
            - 1 / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2)))) := by
    funext M
    have hstep : ∀ K : ℕ,
        (∑ ℓ ∈ Finset.range K,
          ((1 : ℝ) / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2) + 1)
            - 1 / ((M : ℝ) + ((ℓ : ℝ) - (m : ℝ) - 1 / 2))))
          = (1 : ℝ) / ((M : ℝ) + ((K : ℝ) - (m : ℝ) - 1 / 2)) - 1 / ((M : ℝ) - (m : ℝ) - 1 / 2) := by
      intro K
      induction K with
      | zero => simp only [Finset.sum_range_zero, Nat.cast_zero]; ring
      | succ K ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
    rw [hstep k]; push_cast; ring
  rw [hpt]
  exact summable_finset_sum (Finset.range k) _ (fun ℓ _ => summable_neg_telescope m ℓ)

/-- Summability of the shifted half-integer power series `1/(j−m−½+k)^i` (`i ≥ 2`), for either
sign of `k−m`. -/
private lemma summable_half_shift (m k i : ℕ) (hi : 2 ≤ i) :
    Summable (fun j : ℕ => (1 : ℝ) / ((j : ℝ) - (m : ℝ) - 1 / 2 + (k : ℝ)) ^ i) := by
  by_cases hkm : k ≤ m
  · refine (summable_half_neg (m - k) i hi).congr (fun j => ?_)
    have hb : (j : ℝ) - ((m - k : ℕ) : ℝ) - 1 / 2 = (j : ℝ) - (m : ℝ) - 1 / 2 + (k : ℝ) := by
      rw [Nat.cast_sub hkm]; ring
    rw [hb]
  · refine (summable_half_pos (k - m) i (by omega) hi).congr (fun j => ?_)
    have hb : (j : ℝ) + ((k - m : ℕ) : ℝ) - 1 / 2 = (j : ℝ) - (m : ℝ) - 1 / 2 + (k : ℝ) := by
      rw [Nat.cast_sub (le_of_lt (not_le.mp hkm))]; ring
    rw [hb]

/-- **Signed-denominator harmonic integrality** (paper e08, `i = 1` head): the finite head
`Σ_{ℓ<k} 1/(ℓ−m−½)` has denominators `|2ℓ−2m−1| ≤ n` (since `m = ⌊(n−1)/2⌋`), so `d_n` clears
it: `d_n · Σ_{ℓ<k} 1/(ℓ−m−½) ∈ ℤ`. -/
private lemma signed_harmonic_integrality (n m k : ℕ) (hn : 1 ≤ n) (hm : m = (n - 1) / 2)
    (hk : k ≤ n) :
    ∃ z : ℤ, (Nat.lcmUpto n : ℝ)
        * (∑ ℓ ∈ Finset.range k, (1 : ℝ) / ((ℓ : ℝ) - (m : ℝ) - 1 / 2)) = z := by
  refine ⟨∑ ℓ ∈ Finset.range k,
      (if m < ℓ then ((2 * (Nat.lcmUpto n / (2 * ℓ - 2 * m - 1)) : ℕ) : ℤ)
       else -((2 * (Nat.lcmUpto n / (2 * m + 1 - 2 * ℓ)) : ℕ) : ℤ)), ?_⟩
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  rw [Finset.mem_range] at hℓ
  by_cases hcase : m < ℓ
  · rw [if_pos hcase]
    set w : ℕ := 2 * ℓ - 2 * m - 1 with hwdef
    have hw1 : 1 ≤ w := by omega
    have hwn : w ≤ n := by omega
    have hdvd : w ∣ Nat.lcmUpto n := dvd_lcmUpto hw1 hwn
    have hwne : (w : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hwval : w + (2 * m + 1) = 2 * ℓ := by omega
    have hwcast : (w : ℝ) = 2 * (ℓ : ℝ) - 2 * (m : ℝ) - 1 := by
      have := congrArg (Nat.cast : ℕ → ℝ) hwval; push_cast at this; linarith
    have hbase : (ℓ : ℝ) - (m : ℝ) - 1 / 2 = (w : ℝ) / 2 := by rw [hwcast]; ring
    rw [hbase, Int.cast_natCast, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_div hdvd hwne]
    field_simp
  · rw [if_neg hcase]
    set w : ℕ := 2 * m + 1 - 2 * ℓ with hwdef
    have hw1 : 1 ≤ w := by omega
    have hwn : w ≤ n := by omega
    have hdvd : w ∣ Nat.lcmUpto n := dvd_lcmUpto hw1 hwn
    have hwne : (w : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hwval : w + 2 * ℓ = 2 * m + 1 := by omega
    have hwcast : (w : ℝ) = 2 * (m : ℝ) + 1 - 2 * (ℓ : ℝ) := by
      have := congrArg (Nat.cast : ℕ → ℝ) hwval; push_cast at this; linarith
    have hbase : (ℓ : ℝ) - (m : ℝ) - 1 / 2 = -((w : ℝ) / 2) := by rw [hwcast]; ring
    rw [hbase, Int.cast_neg, Int.cast_natCast, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_div hdvd hwne]
    field_simp

/-- **`Σ_k a_{1,k} = 0`** (paper e07/e08, `i = 1` column): from the decomposition alone, the
`i = 1` column total vanishes (otherwise `Σ 1/(m+1)` would be summable).  Extracted from the
`r_n` half so it can be reused in the `r̂_n` assembly. -/
private lemma column1_sum_zero (n : ℕ) (a : ℕ → ℕ → ℝ)
    (hdec : ∀ t : ℝ, (∀ k ∈ Finset.range (n + 1), t + (k : ℝ) ≠ 0) →
        Rn 17 n t = ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1),
            a i k / (t + (k : ℝ)) ^ i) :
    ∑ k ∈ Finset.range (n + 1), a 1 k = 0 := by
  have hpole : ∀ m : ℕ, ∀ k ∈ Finset.range (n + 1), ((m : ℝ) + 1) + (k : ℝ) ≠ 0 :=
    fun m k _ => by positivity
  have hRn_dec : ∀ m : ℕ, Rn 17 n ((m : ℝ) + 1)
      = ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1),
          a i k / (((m : ℝ) + 1) + (k : ℝ)) ^ i :=
    fun m => hdec ((m : ℝ) + 1) (hpole m)
  have hRnsum : Summable (fun m : ℕ => Rn 17 n ((m : ℝ) + 1)) := by
    apply (summable_nat_add_iff n).1
    refine (summable_c 17 n (by norm_num)).congr (fun m => ?_)
    rw [← Rn_eq_c 17 n m (by norm_num)]; congr 1; push_cast; ring
  have hcol2_sum : ∀ i, 2 ≤ i → ∀ k : ℕ,
      Summable (fun m : ℕ => a i k / ((m : ℝ) + 1 + (k : ℝ)) ^ i) := by
    intro i hi k
    refine ((summable_shift_pow (k + 1) i (by omega) hi).mul_left (a i k)).congr (fun m => ?_)
    rw [mul_one_div, show ((m : ℝ) + ((k + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 + (k : ℝ) from by
      push_cast; ring]
  have hcol1_sum : ∀ k : ℕ,
      Summable (fun m : ℕ => a 1 k * (1 / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1))) :=
    fun k => (summable_harmonic_diff k).mul_left (a 1 k)
  have hQsum : Summable (fun m : ℕ =>
      ∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1),
        a i k / ((m : ℝ) + 1 + (k : ℝ)) ^ i) := by
    apply summable_finset_sum; intro i hi; apply summable_finset_sum; intro k _
    exact hcol2_sum i (Finset.mem_Icc.mp hi).1 k
  have hRn_split : ∀ m : ℕ, Rn 17 n ((m : ℝ) + 1)
      = (∑ k ∈ Finset.range (n + 1), a 1 k / ((m : ℝ) + 1 + (k : ℝ)))
        + (∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1),
            a i k / ((m : ℝ) + 1 + (k : ℝ)) ^ i) := by
    intro m
    rw [hRn_dec m, show Finset.Icc 1 33 = insert 1 (Finset.Icc 2 33) from by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega,
      Finset.sum_insert (by simp)]
    congr 1
    apply Finset.sum_congr rfl
    intro k _; rw [pow_one]
  have hPsum : Summable (fun m : ℕ =>
      ∑ k ∈ Finset.range (n + 1), a 1 k / ((m : ℝ) + 1 + (k : ℝ))) := by
    refine (hRnsum.sub hQsum).congr (fun m => ?_)
    rw [hRn_split m]; ring
  have hcorrsum : Summable (fun m : ℕ =>
      ∑ k ∈ Finset.range (n + 1),
        a 1 k * (1 / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1))) :=
    summable_finset_sum _ _ (fun k _ => hcol1_sum k)
  have hSsum : Summable (fun m : ℕ =>
      (∑ k ∈ Finset.range (n + 1), a 1 k) * (1 / ((m : ℝ) + 1))) := by
    refine (hPsum.sub hcorrsum).congr (fun m => ?_)
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  by_contra hne
  have hdiv : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) := by
    refine (hSsum.mul_left (∑ k ∈ Finset.range (n + 1), a 1 k)⁻¹).congr (fun m => ?_)
    field_simp
  have hnot : ¬ Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) := by
    intro hc
    apply Real.not_summable_one_div_natCast
    refine ((summable_nat_add_iff (f := fun m : ℕ => (1 : ℝ) / (m : ℝ)) 1).1 ?_)
    refine hc.congr (fun m => ?_)
    push_cast; ring
  exact hnot hdiv

/-- The finite half-integer head attached to column `(i,k)` in the e08 tail evaluation:
`−2^i Σ_{ℓ<k−m−1} 1/(2ℓ+1)^i` when `k > m` (positive base, `tail_val_pos`), and
`(−1)^i 2^i Σ_{ℓ<m−k+1} 1/(2ℓ+1)^i` when `k ≤ m` (negative base, `tail_val_neg`). -/
private noncomputable def e08Head (m i k : ℕ) : ℝ :=
  if m < k then
    -((2 : ℝ) ^ i * ∑ ℓ ∈ Finset.range (k - m - 1), (1 : ℝ) / ((2 * ℓ + 1 : ℕ) : ℝ) ^ i)
  else
    (-1) ^ i * (2 : ℝ) ^ i * ∑ ℓ ∈ Finset.range (m - k + 1), (1 : ℝ) / ((2 * ℓ + 1 : ℕ) : ℝ) ^ i

/-- **The `r̂_n` (e08) ζ-representation** (paper tex 220–239).  Given the partial-fraction data
for `R_n` (decomposition `hdec`, Lemma-1 integrality `hint`, Lemma-2 symmetry `hsym`) and the
column totals `S i = Σ_k a_{i,k}`, there is an integer constant `Bhat0` with
`d_n^{33}·r̂_n = Σ_{i∈oddIdx3} d_n^{33}·S_i·(2^i−1)·ζ(i) + Bhat0`.

The proof shifts the start of summation to `t = −m−½` (`m = ⌊(n−1)/2⌋`), using that `R_n`
vanishes at `t = −½,…,−(n−½)`, so that `r̂_n = Σ'_j R_n(j−m−½)`.  Each column tail is then
evaluated by `tail_val_pos` (`k ≥ m+1`) / `tail_val_neg` (`k ≤ m`); the `(2^i−1)ζ(i)` parts
collect (even `i` and `i=1` drop by `column_even_zero` / `S 1 = 0`), while the finite heads
have odd denominators `≤ n`, cleared by `d_n` via `odd_harmonic_integrality`. -/
theorem repr_rhat_e08 (n : ℕ) (a : ℕ → ℕ → ℝ)
    (hdec : ∀ t : ℝ, (∀ k ∈ Finset.range (n + 1), t + (k : ℝ) ≠ 0) →
        Rn 17 n t = ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1), a i k / (t + (k : ℝ)) ^ i)
    (hint : ∀ i ∈ Finset.Icc 1 33, ∀ k ∈ Finset.range (n + 1),
        ∃ z : ℤ, (Nat.lcmUpto n : ℝ) ^ (33 - i) * a i k = z)
    (hsym : ∀ i ∈ Finset.Icc 1 33, ∀ k ∈ Finset.range (n + 1),
        a i k = (-1) ^ (i - 1) * a i (n - k))
    (S : ℕ → ℝ) (hSdef : S = fun i => ∑ k ∈ Finset.range (n + 1), a i k) :
    ∃ Bhat0 : ℤ,
      (Nat.lcmUpto n : ℝ) ^ 33 * rhat 17 n
        = (∑ i ∈ oddIdx3, (Nat.lcmUpto n : ℝ) ^ 33 * S i * ((2 : ℝ) ^ i - 1) * zetaVal i)
            + (Bhat0 : ℝ) := by
  classical
  subst hSdef
  set d : ℝ := (Nat.lcmUpto n : ℝ) with hd_def
  have hS1 : (∑ k ∈ Finset.range (n + 1), a 1 k) = 0 := column1_sum_zero n a hdec
  -- The ζ-part collapses from `Icc 2 33` to `oddIdx3` (even columns vanish).
  have hoddsub : oddIdx3 ⊆ Finset.Icc 2 33 := by
    intro i hi
    rw [oddIdx3, Finset.mem_filter, Finset.mem_Icc] at hi
    rw [Finset.mem_Icc]; omega
  have hSeven : ∀ i ∈ Finset.Icc 2 33, i ∉ oddIdx3 →
      (∑ k ∈ Finset.range (n + 1), a i k) = 0 := by
    intro i hi hni
    have hi' : i ∈ Finset.Icc 1 33 := by rw [Finset.mem_Icc] at hi ⊢; omega
    have hev : Even i := by
      rcases Nat.even_or_odd i with he | ho
      · exact he
      · exfalso; apply hni
        rw [oddIdx3, Finset.mem_filter, Finset.mem_Icc]
        rw [Finset.mem_Icc] at hi
        refine ⟨⟨?_, hi.2⟩, ho⟩
        rcases ho with ⟨t, ht⟩; omega
    exact column_even_zero n i a hsym hi' hev
  suffices hmain : ∃ Bhat0 : ℤ,
      d ^ 33 * rhat 17 n
        = (∑ i ∈ Finset.Icc 2 33,
            d ^ 33 * (∑ k ∈ Finset.range (n + 1), a i k) * ((2 : ℝ) ^ i - 1) * zetaVal i)
          + (Bhat0 : ℝ) by
    obtain ⟨B, hB⟩ := hmain
    refine ⟨B, ?_⟩
    have hcollapse : (∑ i ∈ oddIdx3,
          d ^ 33 * (∑ k ∈ Finset.range (n + 1), a i k) * ((2 : ℝ) ^ i - 1) * zetaVal i)
        = ∑ i ∈ Finset.Icc 2 33,
            d ^ 33 * (∑ k ∈ Finset.range (n + 1), a i k) * ((2 : ℝ) ^ i - 1) * zetaVal i :=
      Finset.sum_subset hoddsub (fun i hi hni => by rw [hSeven i hi hni]; ring)
    rw [hB, hcollapse]
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · -- `n = 0`: only the `k = 0` column, all heads empty, `Bhat0 = 0`.
    subst hn0
    refine ⟨0, ?_⟩
    rw [Int.cast_zero, add_zero]
    have ha10 : a 1 0 = 0 := by have h := hS1; rwa [Finset.sum_range_one] at h
    have hdec0 : ∀ k : ℕ, Rn 17 0 ((0 : ℝ) + 1 / 2 + (k : ℝ))
        = ∑ i ∈ Finset.Icc 2 33, a i 0 / ((0 : ℝ) + 1 / 2 + (k : ℝ)) ^ i := by
      intro k
      have hpole0 : ∀ k' ∈ Finset.range (0 + 1), ((0 : ℝ) + 1 / 2 + (k : ℝ)) + (k' : ℝ) ≠ 0 := by
        intro k' _; positivity
      rw [hdec _ hpole0, show (0 : ℕ) + 1 = 1 from rfl]
      simp only [Finset.sum_range_one, Nat.cast_zero, add_zero]
      rw [show Finset.Icc 1 33 = insert 1 (Finset.Icc 2 33) from by
        ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega, Finset.sum_insert (by simp),
        pow_one, ha10, zero_div, zero_add]
    have hchat : ∀ k : ℕ, chat 17 0 k = Rn 17 0 ((0 : ℝ) + 1 / 2 + (k : ℝ)) := by
      intro k
      rw [← Rn_eq_chat 17 0 k (by norm_num)]; congr 1; norm_num
    have hcolsum0 : ∀ i, 2 ≤ i → Summable (fun k : ℕ => a i 0 / ((0 : ℝ) + 1 / 2 + (k : ℝ)) ^ i) := by
      intro i hi
      refine ((summable_half_pos 1 i (by norm_num) hi).mul_left (a i 0)).congr (fun k => ?_)
      have hb : (k : ℝ) + ((1 : ℕ) : ℝ) - 1 / 2 = (0 : ℝ) + 1 / 2 + (k : ℝ) := by push_cast; ring
      rw [mul_one_div, hb]
    have hrhat0 : rhat 17 0 = ∑ i ∈ Finset.Icc 2 33, a i 0 * ((2 : ℝ) ^ i - 1) * zetaVal i := by
      simp only [rhat]
      rw [tsum_congr hchat, tsum_congr hdec0,
        Summable.tsum_finsetSum (fun i hi => hcolsum0 i (Finset.mem_Icc.mp hi).1)]
      apply Finset.sum_congr rfl
      intro i hi
      have hi2 := (Finset.mem_Icc.mp hi).1
      rw [show (fun k : ℕ => a i 0 / ((0 : ℝ) + 1 / 2 + (k : ℝ)) ^ i)
            = (fun k : ℕ => a i 0 * (1 / ((0 : ℝ) + 1 / 2 + (k : ℝ)) ^ i)) from
          funext (fun k => (mul_one_div _ _).symm), tsum_mul_left,
        show (∑' k : ℕ, (1 : ℝ) / ((0 : ℝ) + 1 / 2 + (k : ℝ)) ^ i)
            = ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + ((1 : ℕ) : ℝ) - 1 / 2) ^ i from
          tsum_congr (fun k => by rw [show (0 : ℝ) + 1 / 2 + (k : ℝ) = (k : ℝ) + ((1 : ℕ) : ℝ) - 1 / 2
            from by push_cast; ring]),
        tail_val_pos 1 i (by norm_num) hi2]
      simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero]
      ring
    rw [hrhat0, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_range_one]; ring
  · -- `n ≥ 1`: the shifted half-integer assembly.
    set m : ℕ := (n - 1) / 2 with hm
    have hshift : ∑' j : ℕ, Rn 17 n ((j : ℝ) - (m : ℝ) - 1 / 2) = rhat 17 n := by
      have h := rhat_shift n hn1
      rwa [← hm] at h
    have hpole : ∀ j : ℕ, ∀ k ∈ Finset.range (n + 1),
        ((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ) ≠ 0 := by
      intro j k _ h
      have h2 : (2 * (j + k) : ℕ) = (2 * m + 1 : ℕ) := by
        have hcast : ((2 * (j + k) : ℕ) : ℝ) = ((2 * m + 1 : ℕ) : ℝ) := by
          push_cast; push_cast at h; linarith
        exact_mod_cast hcast
      omega
    have hdecj : ∀ j : ℕ, Rn 17 n ((j : ℝ) - (m : ℝ) - 1 / 2)
        = ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1),
            a i k / (((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ)) ^ i :=
      fun j => hdec _ (hpole j)
    -- `i = 1` telescoped by `S 1 = 0`.
    have hGj : ∀ j : ℕ, Rn 17 n ((j : ℝ) - (m : ℝ) - 1 / 2)
        = (∑ k ∈ Finset.range (n + 1),
              a 1 k * (1 / (((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ)) - 1 / ((j : ℝ) - (m : ℝ) - 1 / 2)))
          + (∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1),
              a i k / (((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ)) ^ i) := by
      intro j
      rw [hdecj j, show Finset.Icc 1 33 = insert 1 (Finset.Icc 2 33) from by
        ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega, Finset.sum_insert (by simp)]
      congr 1
      rw [Finset.sum_congr rfl (fun k _ => by
        show a 1 k / (((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ)) ^ 1
            = a 1 k * (1 / (((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ)) - 1 / ((j : ℝ) - (m : ℝ) - 1 / 2))
              + a 1 k * (1 / ((j : ℝ) - (m : ℝ) - 1 / 2))
        rw [pow_one]; ring)]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hS1, zero_mul, add_zero]
    -- Column summabilities.
    have hQcol_sum : ∀ i, 2 ≤ i → ∀ k : ℕ,
        Summable (fun j : ℕ => a i k / (((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ)) ^ i) := by
      intro i hi k
      refine ((summable_half_shift m k i hi).mul_left (a i k)).congr (fun j => ?_)
      rw [mul_one_div]
    have hPcol_sum : ∀ k : ℕ,
        Summable (fun j : ℕ =>
          a 1 k * (1 / (((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ)) - 1 / ((j : ℝ) - (m : ℝ) - 1 / 2))) :=
      fun k => (summable_neg_harmonic_diff m k).mul_left (a 1 k)
    have hPsum_j : Summable (fun j : ℕ =>
        ∑ k ∈ Finset.range (n + 1),
          a 1 k * (1 / (((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ)) - 1 / ((j : ℝ) - (m : ℝ) - 1 / 2))) :=
      summable_finset_sum _ _ (fun k _ => hPcol_sum k)
    have hQsum_j : Summable (fun j : ℕ =>
        ∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1),
          a i k / (((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ)) ^ i) := by
      apply summable_finset_sum; intro i hi; apply summable_finset_sum; intro k _
      exact hQcol_sum i (Finset.mem_Icc.mp hi).1 k
    -- Column tail values `Σ'_j 1/(j−m−½+k)^i = (2^i−1)ζ(i) + head`.
    have hval_col : ∀ i, 2 ≤ i → ∀ k : ℕ,
        (∑' j : ℕ, (1 : ℝ) / (((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ)) ^ i)
          = ((2 : ℝ) ^ i - 1) * zetaVal i + e08Head m i k := by
      intro i hi k
      by_cases hkm : m < k
      · rw [show (∑' j : ℕ, (1 : ℝ) / (((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ)) ^ i)
              = ∑' j : ℕ, (1 : ℝ) / ((j : ℝ) + ((k - m : ℕ) : ℝ) - 1 / 2) ^ i from
            tsum_congr (fun j => by
              rw [show ((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ) = (j : ℝ) + ((k - m : ℕ) : ℝ) - 1 / 2
                from by rw [Nat.cast_sub (le_of_lt hkm)]; ring]),
          tail_val_pos (k - m) i (by omega) hi]
        simp only [e08Head, if_pos hkm]
        ring
      · have hkm' : k ≤ m := not_lt.mp hkm
        rw [show (∑' j : ℕ, (1 : ℝ) / (((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ)) ^ i)
              = ∑' j : ℕ, (1 : ℝ) / ((j : ℝ) - ((m - k : ℕ) : ℝ) - 1 / 2) ^ i from
            tsum_congr (fun j => by
              rw [show ((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ) = (j : ℝ) - ((m - k : ℕ) : ℝ) - 1 / 2
                from by rw [Nat.cast_sub hkm']; ring]),
          tail_val_neg (m - k) i hi]
        simp only [e08Head, if_neg hkm]
    -- Value of `r̂_n`.
    have hRV : rhat 17 n
        = (∑ k ∈ Finset.range (n + 1),
            a 1 k * (-∑ ℓ ∈ Finset.range k, (1 : ℝ) / ((ℓ : ℝ) - (m : ℝ) - 1 / 2)))
          + (∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1),
              a i k * (((2 : ℝ) ^ i - 1) * zetaVal i + e08Head m i k)) := by
      rw [← hshift, tsum_congr hGj, hPsum_j.tsum_add hQsum_j]
      congr 1
      · rw [Summable.tsum_finsetSum (fun k _ => hPcol_sum k)]
        apply Finset.sum_congr rfl; intro k _
        rw [tsum_mul_left, tsum_neg_harmonic]
      · rw [Summable.tsum_finsetSum (fun i hi =>
          summable_finset_sum _ _ (fun k _ => hQcol_sum i (Finset.mem_Icc.mp hi).1 k))]
        apply Finset.sum_congr rfl; intro i hi
        rw [Summable.tsum_finsetSum (fun k _ => hQcol_sum i (Finset.mem_Icc.mp hi).1 k)]
        apply Finset.sum_congr rfl; intro k _
        rw [show (fun j : ℕ => a i k / (((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ)) ^ i)
              = (fun j : ℕ => a i k * (1 / (((j : ℝ) - (m : ℝ) - 1 / 2) + (k : ℝ)) ^ i)) from
            funext (fun j => (mul_one_div _ _).symm),
          tsum_mul_left, hval_col i (Finset.mem_Icc.mp hi).1 k]
    -- Integer certificates for the finite heads.
    have hInt1 : ∀ k : ℕ, ∃ z : ℤ, k ∈ Finset.range (n + 1) →
        (z : ℝ) = d ^ 33 * a 1 k
            * (-∑ ℓ ∈ Finset.range k, (1 : ℝ) / ((ℓ : ℝ) - (m : ℝ) - 1 / 2)) := by
      intro k
      by_cases hk : k ∈ Finset.range (n + 1)
      · obtain ⟨z1, hz1⟩ := hint 1 (Finset.mem_Icc.mpr (by omega)) k hk
        obtain ⟨z2, hz2⟩ :=
          signed_harmonic_integrality n m k hn1 hm (by rw [Finset.mem_range] at hk; omega)
        rw [← hd_def] at hz2
        refine ⟨-(z1 * z2), fun _ => ?_⟩
        have hpow : d ^ 33 = d ^ (33 - 1) * d ^ 1 := by rw [← pow_add]
        push_cast
        rw [← hz1, ← hz2, hpow]; ring
      · exact ⟨0, fun h => absurd h hk⟩
    have hIntCol : ∀ i k : ℕ, ∃ z : ℤ, i ∈ Finset.Icc 2 33 → k ∈ Finset.range (n + 1) →
        (z : ℝ) = d ^ 33 * a i k * e08Head m i k := by
      intro i k
      by_cases hi : i ∈ Finset.Icc 2 33
      · by_cases hk : k ∈ Finset.range (n + 1)
        · have hi1 : i ∈ Finset.Icc 1 33 := by rw [Finset.mem_Icc] at hi ⊢; omega
          obtain ⟨z1, hz1⟩ := hint i hi1 k hk
          have hpow : d ^ 33 = d ^ (33 - i) * d ^ i := by
            rw [← pow_add]; congr 1; rw [Finset.mem_Icc] at hi; omega
          by_cases hkm : m < k
          · obtain ⟨z2, hz2⟩ :=
              odd_harmonic_integrality n i (k - m - 1) (by rw [Finset.mem_range] at hk; omega)
            rw [← hd_def] at hz2
            refine ⟨-(z1 * z2), fun _ _ => ?_⟩
            simp only [e08Head, if_pos hkm]
            push_cast at hz2 ⊢
            rw [← hz1, ← hz2, hpow]; ring
          · have hkm' : k ≤ m := not_lt.mp hkm
            obtain ⟨z2, hz2⟩ := odd_harmonic_integrality n i (m - k + 1) (by omega)
            rw [← hd_def] at hz2
            refine ⟨(-1) ^ i * (z1 * z2), fun _ _ => ?_⟩
            simp only [e08Head, if_neg hkm]
            push_cast at hz2 ⊢
            rw [← hz1, ← hz2, hpow]; ring
        · exact ⟨0, fun _ h => absurd h hk⟩
      · exact ⟨0, fun h _ => absurd h hi⟩
    choose z1f hz1f using hInt1
    choose z2f hz2f using hIntCol
    refine ⟨(∑ k ∈ Finset.range (n + 1), z1f k)
        + (∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1), z2f i k), ?_⟩
    -- Multiply through by `d^33` and collect.
    have hBcast : (((∑ k ∈ Finset.range (n + 1), z1f k)
          + (∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1), z2f i k) : ℤ) : ℝ)
        = (∑ k ∈ Finset.range (n + 1),
            d ^ 33 * a 1 k * (-∑ ℓ ∈ Finset.range k, (1 : ℝ) / ((ℓ : ℝ) - (m : ℝ) - 1 / 2)))
          + (∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1),
              d ^ 33 * a i k * e08Head m i k) := by
      push_cast
      congr 1
      · apply Finset.sum_congr rfl; intro k hk; exact hz1f k hk
      · apply Finset.sum_congr rfl; intro i hi
        apply Finset.sum_congr rfl; intro k hk
        exact hz2f i k hi hk
    have hAeq : d ^ 33 * (∑ k ∈ Finset.range (n + 1),
          a 1 k * (-∑ ℓ ∈ Finset.range k, (1 : ℝ) / ((ℓ : ℝ) - (m : ℝ) - 1 / 2)))
        = ∑ k ∈ Finset.range (n + 1),
            d ^ 33 * a 1 k * (-∑ ℓ ∈ Finset.range k, (1 : ℝ) / ((ℓ : ℝ) - (m : ℝ) - 1 / 2)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    have hBeq : d ^ 33 * (∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1),
          a i k * (((2 : ℝ) ^ i - 1) * zetaVal i + e08Head m i k))
        = (∑ i ∈ Finset.Icc 2 33,
            d ^ 33 * (∑ k ∈ Finset.range (n + 1), a i k) * ((2 : ℝ) ^ i - 1) * zetaVal i)
          + (∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1),
              d ^ 33 * a i k * e08Head m i k) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum,
        show d ^ 33 * (∑ k ∈ Finset.range (n + 1), a i k) * ((2 : ℝ) ^ i - 1) * zetaVal i
            = ∑ k ∈ Finset.range (n + 1), d ^ 33 * a i k * (((2 : ℝ) ^ i - 1) * zetaVal i) from by
          rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro k _; ring,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hRV, hBcast, mul_add, hAeq, hBeq]
    ring

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
  -- column totals `S i`.  The `r_n` form (e07) is PROVED below (reindex `r = Σ_{ν≥1} R_n(ν)`,
  -- so all harmonic heads stay `≤ n`; even columns drop by `column_even_zero`, the `i = 1`
  -- residue vanishes by `S 1 = 0` via harmonic divergence, and the constant is an integer by
  -- `hint` + `harmonic_integrality`).  The `r̂_n` form (e08) is the residual `sorry`: its
  -- half-integer heads run past `n`, so integrality of its constant needs the Lemma-2 symmetry
  -- cancellation of paper e08, which is not yet formalized.
  have hraw : ∃ B0 Bhat0 : ℤ,
      (Nat.lcmUpto n : ℝ) ^ 33 * r 17 n
        = (∑ i ∈ oddIdx3, (Nat.lcmUpto n : ℝ) ^ 33 * S i * zetaVal i) + (B0 : ℝ)
      ∧ (Nat.lcmUpto n : ℝ) ^ 33 * rhat 17 n
        = (∑ i ∈ oddIdx3, (Nat.lcmUpto n : ℝ) ^ 33 * S i * ((2 : ℝ) ^ i - 1) * zetaVal i)
            + (Bhat0 : ℝ) := by
    set d : ℝ := (Nat.lcmUpto n : ℝ) with hd_def
    -- Abbreviation for the harmonic head `Hh i k = Σ_{ℓ=1}^k 1/ℓ^i`.
    set Hh : ℕ → ℕ → ℝ := fun i k => ∑ ℓ ∈ Finset.Icc 1 k, (1 : ℝ) / (ℓ : ℝ) ^ i with hHh_def
    -- Poles are avoided at every `t = m + 1` (`t + k = m + 1 + k ≥ 1 > 0`).
    have hpole : ∀ m : ℕ, ∀ k ∈ Finset.range (n + 1), ((m : ℝ) + 1) + (k : ℝ) ≠ 0 :=
      fun m k _ => by positivity
    have hRn_dec : ∀ m : ℕ, Rn 17 n ((m : ℝ) + 1)
        = ∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1),
            a i k / (((m : ℝ) + 1) + (k : ℝ)) ^ i :=
      fun m => _hdec ((m : ℝ) + 1) (hpole m)
    -- `R_n` vanishes at `t = m+1` for `m < n` (the `∏(t-j)` factor).
    have hvanish : ∀ m : ℕ, m < n → Rn 17 n ((m : ℝ) + 1) = 0 := by
      intro m hm
      have hP1 : ∏ j ∈ Finset.Icc 1 n, (((m : ℝ) + 1) - (j : ℝ)) = 0 := by
        apply Finset.prod_eq_zero (i := m + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        push_cast; ring
      simp only [Rn]
      rw [hP1]; ring
    -- Summability of the reindexed series and the tail identification.
    have hRnsum : Summable (fun m : ℕ => Rn 17 n ((m : ℝ) + 1)) := by
      apply (summable_nat_add_iff n).1
      refine (summable_c 17 n (by norm_num)).congr (fun m => ?_)
      rw [← Rn_eq_c 17 n m (by norm_num)]; congr 1; push_cast; ring
    have htail : (∑' m : ℕ, Rn 17 n (((m + n : ℕ) : ℝ) + 1)) = r 17 n := by
      show (∑' m : ℕ, Rn 17 n (((m + n : ℕ) : ℝ) + 1)) = ∑' k, c 17 n k
      refine tsum_congr (fun m => ?_)
      rw [← Rn_eq_c 17 n m (by norm_num)]; congr 1; push_cast; ring
    have hhead : (∑ m ∈ Finset.range n, Rn 17 n ((m : ℝ) + 1)) = 0 :=
      Finset.sum_eq_zero (fun m hm => hvanish m (Finset.mem_range.mp hm))
    have hr_reindex : (∑' m : ℕ, Rn 17 n ((m : ℝ) + 1)) = r 17 n := by
      have key : (∑ m ∈ Finset.range n, Rn 17 n ((m : ℝ) + 1))
          + (∑' m : ℕ, Rn 17 n (((m + n : ℕ) : ℝ) + 1))
          = ∑' m : ℕ, Rn 17 n ((m : ℝ) + 1) := hRnsum.sum_add_tsum_nat_add n
      rw [hhead, zero_add] at key
      rw [← key]; exact htail
    -- Per-column tsum values.
    have hcol2_val : ∀ i, 2 ≤ i → ∀ k : ℕ,
        (∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 1 + (k : ℝ)) ^ i) = zetaVal i - Hh i k := by
      intro i hi k
      rw [show (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1 + (k : ℝ)) ^ i)
            = (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + ((k + 1 : ℕ) : ℝ)) ^ i) from by
        funext m; rw [show ((m : ℝ) + ((k + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 + (k : ℝ) from by
          push_cast; ring]]
      rw [tsum_shift_zeta (k + 1) i (by omega) hi, hHh_def]
      simp
    have hcol2_sum : ∀ i, 2 ≤ i → ∀ k : ℕ,
        Summable (fun m : ℕ => a i k / ((m : ℝ) + 1 + (k : ℝ)) ^ i) := by
      intro i hi k
      refine ((summable_shift_pow (k + 1) i (by omega) hi).mul_left (a i k)).congr (fun m => ?_)
      rw [mul_one_div, show ((m : ℝ) + ((k + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 + (k : ℝ) from by
        push_cast; ring]
    have hcol1_sum : ∀ k : ℕ,
        Summable (fun m : ℕ => a 1 k * (1 / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1))) :=
      fun k => (summable_harmonic_diff k).mul_left (a 1 k)
    -- The `i ≥ 2` block, as a function of `m`.
    have hQsum : Summable (fun m : ℕ =>
        ∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1),
          a i k / ((m : ℝ) + 1 + (k : ℝ)) ^ i) := by
      apply summable_finset_sum
      intro i hi
      apply summable_finset_sum
      intro k _
      exact hcol2_sum i (Finset.mem_Icc.mp hi).1 k
    -- `S 1 = 0` by the harmonic-divergence argument.
    have hS1 : (∑ k ∈ Finset.range (n + 1), a 1 k) = 0 := by
      -- The `i = 1` block `P m = Σ_k a_{1,k}/(m+1+k)` is summable (`= R_n(m+1) − Q m`).
      have hRn_split : ∀ m : ℕ, Rn 17 n ((m : ℝ) + 1)
          = (∑ k ∈ Finset.range (n + 1), a 1 k / ((m : ℝ) + 1 + (k : ℝ)))
            + (∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1),
                a i k / ((m : ℝ) + 1 + (k : ℝ)) ^ i) := by
        intro m
        rw [hRn_dec m, show Finset.Icc 1 33 = insert 1 (Finset.Icc 2 33) from by
          ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega,
          Finset.sum_insert (by simp)]
        congr 1
        apply Finset.sum_congr rfl
        intro k _; rw [pow_one]
      have hPsum : Summable (fun m : ℕ =>
          ∑ k ∈ Finset.range (n + 1), a 1 k / ((m : ℝ) + 1 + (k : ℝ))) := by
        refine (hRnsum.sub hQsum).congr (fun m => ?_)
        rw [hRn_split m]; ring
      -- Correction term `corr m = Σ_k a_{1,k}(1/(m+1+k) − 1/(m+1))` is summable.
      have hcorrsum : Summable (fun m : ℕ =>
          ∑ k ∈ Finset.range (n + 1),
            a 1 k * (1 / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1))) :=
        summable_finset_sum _ _ (fun k _ => hcol1_sum k)
      -- Hence `S1 · (1/(m+1))` is summable.
      have hSsum : Summable (fun m : ℕ =>
          (∑ k ∈ Finset.range (n + 1), a 1 k) * (1 / ((m : ℝ) + 1))) := by
        refine (hPsum.sub hcorrsum).congr (fun m => ?_)
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _; ring
      by_contra hne
      have hdiv : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) := by
        refine (hSsum.mul_left (∑ k ∈ Finset.range (n + 1), a 1 k)⁻¹).congr (fun m => ?_)
        field_simp
      have hnot : ¬ Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) := by
        intro hc
        apply Real.not_summable_one_div_natCast
        refine ((summable_nat_add_iff (f := fun m : ℕ => (1 : ℝ) / (m : ℝ)) 1).1 ?_)
        refine hc.congr (fun m => ?_)
        push_cast; ring
      exact hnot hdiv
    -- Rewrite `R_n(m+1)` with the `i = 1` column in harmonic-difference form (uses `S1 = 0`).
    have hGm : ∀ m : ℕ, Rn 17 n ((m : ℝ) + 1)
        = (∑ k ∈ Finset.range (n + 1),
              a 1 k * (1 / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1)))
          + (∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1),
              a i k / ((m : ℝ) + 1 + (k : ℝ)) ^ i) := by
      intro m
      rw [hRn_dec m, show Finset.Icc 1 33 = insert 1 (Finset.Icc 2 33) from by
        ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega,
        Finset.sum_insert (by simp)]
      congr 1
      -- `i = 1` column: `Σ_k a_{1,k}/(m+1+k) = Σ_k a_{1,k}(1/(m+1+k) − 1/(m+1))` since `S1 = 0`.
      rw [Finset.sum_congr rfl (fun k _ => by
        show a 1 k / ((m : ℝ) + 1 + (k : ℝ)) ^ 1
          = a 1 k * (1 / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1))
            + a 1 k * (1 / ((m : ℝ) + 1))
        rw [pow_one]; ring)]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hS1, zero_mul, add_zero]
    -- Summability of the two blocks in `G`.
    have hPform_sum : Summable (fun m : ℕ =>
        ∑ k ∈ Finset.range (n + 1),
          a 1 k * (1 / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1))) :=
      summable_finset_sum _ _ (fun k _ => hcol1_sum k)
    -- Interchange to get the value of `Σ'_m R_n(m+1) = r`.
    have hPval : (∑' m : ℕ, ∑ k ∈ Finset.range (n + 1),
          a 1 k * (1 / ((m : ℝ) + 1 + (k : ℝ)) - 1 / ((m : ℝ) + 1)))
        = ∑ k ∈ Finset.range (n + 1), a 1 k * (- Hh 1 k) := by
      rw [Summable.tsum_finsetSum (fun k _ => hcol1_sum k)]
      apply Finset.sum_congr rfl
      intro k _
      rw [tsum_mul_left, tsum_harmonic, hHh_def]
      simp
    have hQval : (∑' m : ℕ, ∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1),
          a i k / ((m : ℝ) + 1 + (k : ℝ)) ^ i)
        = ∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1),
            a i k * (zetaVal i - Hh i k) := by
      rw [Summable.tsum_finsetSum (fun i hi =>
        summable_finset_sum _ _ (fun k _ => hcol2_sum i (Finset.mem_Icc.mp hi).1 k))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Summable.tsum_finsetSum (fun k _ => hcol2_sum i (Finset.mem_Icc.mp hi).1 k)]
      apply Finset.sum_congr rfl
      intro k _
      rw [show (fun m : ℕ => a i k / ((m : ℝ) + 1 + (k : ℝ)) ^ i)
            = (fun m : ℕ => a i k * (1 / ((m : ℝ) + 1 + (k : ℝ)) ^ i)) from by
          funext m; rw [mul_one_div],
        tsum_mul_left, hcol2_val i (Finset.mem_Icc.mp hi).1 k]
    -- Value of `r`.
    have hRV : r 17 n
        = (∑ k ∈ Finset.range (n + 1), a 1 k * (- Hh 1 k))
          + (∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1), a i k * (zetaVal i - Hh i k)) := by
      rw [← hr_reindex, tsum_congr hGm,
        (hPform_sum.tsum_add hQsum), hPval, hQval]
    -- Multiply through by `d^33` and read off the ζ-sum and the integer constant.
    -- The ζ-part collapses to `oddIdx3` (even columns vanish by `column_even_zero`).
    have hSeven : ∀ i ∈ Finset.Icc 2 33, i ∉ oddIdx3 →
        (∑ k ∈ Finset.range (n + 1), a i k) = 0 := by
      intro i hi hni
      have hi' : i ∈ Finset.Icc 1 33 := by rw [Finset.mem_Icc] at hi ⊢; omega
      have hev : Even i := by
        rcases Nat.even_or_odd i with he | ho
        · exact he
        · exfalso; apply hni
          rw [oddIdx3, Finset.mem_filter, Finset.mem_Icc]
          rw [Finset.mem_Icc] at hi
          refine ⟨⟨?_, hi.2⟩, ho⟩
          rcases ho with ⟨t, ht⟩; omega
      exact column_even_zero n i a _hsym hi' hev
    have hoddsub : oddIdx3 ⊆ Finset.Icc 2 33 := by
      intro i hi
      rw [oddIdx3, Finset.mem_filter, Finset.mem_Icc] at hi
      rw [Finset.mem_Icc]; omega
    -- The ζ-coefficient sum over `Icc 2 33` equals the one over `oddIdx3`.
    have hZeta : (∑ i ∈ Finset.Icc 2 33, d ^ 33 * (∑ k ∈ Finset.range (n + 1), a i k) * zetaVal i)
        = ∑ i ∈ oddIdx3, d ^ 33 * S i * zetaVal i := by
      refine (Finset.sum_subset hoddsub (fun i hi hni => ?_)).symm
      rw [hSeven i hi hni]; ring
    -- Distribute `d^33` across the `r`-value.
    have hAeq : d ^ 33 * (∑ k ∈ Finset.range (n + 1), a 1 k * (- Hh 1 k))
        = -(∑ k ∈ Finset.range (n + 1), d ^ 33 * a 1 k * Hh 1 k) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _; ring
    have hBeq : d ^ 33 * (∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1),
          a i k * (zetaVal i - Hh i k))
        = (∑ i ∈ Finset.Icc 2 33, d ^ 33 * (∑ k ∈ Finset.range (n + 1), a i k) * zetaVal i)
          - (∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1), d ^ 33 * a i k * Hh i k) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum,
        show d ^ 33 * (∑ k ∈ Finset.range (n + 1), a i k) * zetaVal i
            = ∑ k ∈ Finset.range (n + 1), d ^ 33 * a i k * zetaVal i from by
          rw [Finset.mul_sum, Finset.sum_mul],
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _; ring
    -- Integrality of each constant term `d^33 · a_{i,k} · Hh_{i,k}`.
    have hIntTot : ∀ i k, ∃ z : ℤ, i ∈ Finset.Icc 1 33 → k ∈ Finset.range (n + 1) →
        (z : ℝ) = d ^ 33 * a i k * Hh i k := by
      intro i k
      by_cases hi : i ∈ Finset.Icc 1 33
      · by_cases hk : k ∈ Finset.range (n + 1)
        · obtain ⟨z1, hz1⟩ := hint i hi k hk
          obtain ⟨z2, hz2⟩ := harmonic_integrality n i k (by rw [Finset.mem_range] at hk; omega)
          rw [← hd_def] at hz2
          refine ⟨z1 * z2, fun _ _ => ?_⟩
          have hpow : d ^ 33 = d ^ (33 - i) * d ^ i := by
            rw [← pow_add]; congr 1; rw [Finset.mem_Icc] at hi; omega
          simp only [hHh_def]
          rw [hpow]
          push_cast
          rw [← hz1, ← hz2]; ring
        · exact ⟨0, fun _ h => absurd h hk⟩
      · exact ⟨0, fun h _ => absurd h hi⟩
    choose zf hzf using hIntTot
    have hB0eq : ((-(∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1), zf i k) : ℤ) : ℝ)
        = -(∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1), d ^ 33 * a i k * Hh i k) := by
      push_cast
      congr 1
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro k hk
      exact hzf i k hi hk
    -- The `r̂_n` (e08) constant is packaged as an existential integer; its identity is proved
    -- via the summation-shift `rhat = Σ'_j R_n(j−m−½)` and the tail lemmas `tail_val_pos/neg`.
    obtain ⟨Bhat0, hrhat_eq⟩ := repr_rhat_e08 n a _hdec hint _hsym S hSdef
    refine ⟨-(∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1), zf i k), Bhat0, ?_, hrhat_eq⟩
    -- r-form.
    rw [hB0eq, ← hZeta, hRV, mul_add, hAeq, hBeq,
      show (∑ i ∈ Finset.Icc 1 33, ∑ k ∈ Finset.range (n + 1), d ^ 33 * a i k * Hh i k)
          = (∑ k ∈ Finset.range (n + 1), d ^ 33 * a 1 k * Hh 1 k)
            + (∑ i ∈ Finset.Icc 2 33, ∑ k ∈ Finset.range (n + 1), d ^ 33 * a i k * Hh i k) from by
        rw [show Finset.Icc 1 33 = insert 1 (Finset.Icc 2 33) from by
          ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega,
          Finset.sum_insert (by simp)]]
    ring
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
