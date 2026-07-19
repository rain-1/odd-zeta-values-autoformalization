import Cbcert.PartialFraction

/-!
# Lemma A — the decay relations (Layer L1)

`E_M(a) = 0` for `1 ≤ M ≤ 4n+4`, and `E_M(ã) = 0` for `1 ≤ M ≤ 4n+2`.
These are the vanishing Laurent coefficients `[k^{-M}] R_n = 0` implied by
`R_n(k) = O(k^{-(4n+5)})`.

## Route (elementary power series over `ℚ⟦X⟧`, `x = 1/k`)
`E_M(a) = [X^M] S` where `S = Σ_{i,j} a_{i,j} X^i (1+jX)^{-i}`.  Clearing `S` by the
unit `D̃ = ∏_{m=0}^n (1+mX)^6` turns the negative-binomial factors into honest
polynomials, and the cleared identity `pf_cleared` (owner: `PartialFraction.lean`),
*reversed* via `x = 1/k`, shows `S·D̃ = X^{4n+5}·Ñ` with `Ñ = X^{2n+1}N_n(1/X)` a
polynomial.  Hence `S = X^{4n+5}·(unit)` and `[X^M] S = 0` for `M ≤ 4n+4`.

The reversal is transported from the pointwise identity `pf_cleared` to the honest
`Polynomial ℚ` identity `RHSpoly = X^{4n+5}·Ñ` by comparing evaluations at all
nonzero rationals (`Polynomial.eq_of_infinite_eval_eq`).

## Status
Both `decay_a` and `decay_at` are **proved** sorry-free (relying only on `pf_cleared`).
The companion `decay_at` runs the same reversal after the exact clearing identity
`atclear` (`Σ ã_{i,j}(k+j)^{6-i}∏ = -k(k+n)N_n`), which is derived from `pf_cleared`
together with the boundary vanishing `E_1(a) = E_2(a) = 0` (i.e. `decay_a` at `M=1,2`).
-/

open Cbcert PowerSeries

namespace Cbcert.Decay

open scoped Classical
open Cbcert.PartialFraction

/-! ## The negative-binomial series `geomPow i j = (1+jX)^{-i}` -/

/-- `geomPow i j = (1 + j·X)^{-i}` as a power series in `ℚ⟦X⟧`. -/
noncomputable def geomPow (i j : ℕ) : ℚ⟦X⟧ :=
  rescale (-(j : ℚ)) ((invOneSubPow ℚ i).val)

/-- The negative-binomial coefficient: `[X^r]((1+jX)^{-i}) = C(-i,r)·j^r`. -/
theorem coeff_geomPow (i j r : ℕ) (hi : 1 ≤ i) :
    (coeff r) (geomPow i j) = (Cneg i r : ℚ) * (j : ℚ) ^ r := by
  unfold geomPow Cneg
  rw [coeff_rescale, invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℚ i (by omega),
    coeff_mk]
  have hch : Nat.choose (i - 1 + r) (i - 1) = Nat.choose (i + r - 1) r := by
    rw [show i - 1 + r = i + r - 1 by omega, ← Nat.choose_symm (by omega)]
    congr 1; omega
  rw [hch]; push_cast; rw [neg_pow]; ring

/-- `geomPow i j` is the (two-sided) inverse of `(1 + j·X)^i`. -/
theorem geomPow_mul (i j : ℕ) :
    geomPow i j * (1 + C (j : ℚ) * X) ^ i = 1 := by
  unfold geomPow
  have hval : (invOneSubPow ℚ i).val * (1 - X : ℚ⟦X⟧) ^ i = 1 := by
    have := (invOneSubPow ℚ i).val_inv
    rwa [invOneSubPow_inv_eq_one_sub_pow] at this
  have h := congrArg (rescale (-(j : ℚ))) hval
  rw [map_mul, map_one, map_pow, map_sub, map_one, rescale_X] at h
  rwa [show (1 : ℚ⟦X⟧) - C (-(j : ℚ)) * X = 1 + C (j : ℚ) * X by rw [map_neg]; ring] at h

/-- `geomPow i j · (1+jX)^6 = (1+jX)^{6-i}` for `i ≤ 6`. -/
theorem geomPow_mul_pow6 (i j : ℕ) (hi : i ≤ 6) :
    geomPow i j * (1 + C (j : ℚ) * X) ^ 6 = (1 + C (j : ℚ) * X) ^ (6 - i) := by
  conv_lhs => rw [show (6 : ℕ) = i + (6 - i) from by omega, pow_add]
  rw [← mul_assoc, geomPow_mul, one_mul]

/-! ## `S`, its coefficients, and the `E_M` bridge -/

/-- The series `S_b = Σ_{i,j} b_{i,j}·X^i·(1+jX)^{-i}` for a coefficient array `b`. -/
noncomputable def Sgen (n : ℕ) (b : ℕ → ℕ → ℚ) : ℚ⟦X⟧ :=
  ∑ i ∈ Finset.Icc 1 6, ∑ j ∈ Finset.range (n + 1),
    C (b i j) * X ^ i * geomPow i j

/-- **Coefficient extraction:** `[X^M] S_b = E_M(b)`. -/
theorem coeff_Sgen (n M : ℕ) (b : ℕ → ℕ → ℚ) :
    (coeff M) (Sgen n b) = EM n M b := by
  unfold Sgen EM
  rw [map_sum,
    show Finset.Icc 1 (min 6 M) = (Finset.Icc 1 6).filter (· ≤ M) by
      ext i; simp only [Finset.mem_Icc, Finset.mem_filter, le_min_iff]; omega,
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  rw [map_sum]
  by_cases hiM : i ≤ M
  · rw [if_pos hiM, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos hiM, coeff_geomPow i j (M - i) hi1]
    ring
  · rw [if_neg hiM]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_neg hiM, mul_zero]

/-! ## Clearing by `D̃` -/

/-- `D̃ = ∏_{m=0}^n (1 + mX)^6`, a unit of `ℚ⟦X⟧` (constant coefficient `1`). -/
noncomputable def Dtil (n : ℕ) : ℚ⟦X⟧ :=
  ∏ m ∈ Finset.range (n + 1), (1 + C (m : ℚ) * X) ^ 6

/-- Explicit inverse of `D̃`. -/
noncomputable def Dinv (n : ℕ) : ℚ⟦X⟧ := ∏ m ∈ Finset.range (n + 1), (geomPow 1 m) ^ 6

theorem Dtil_mul_Dinv (n : ℕ) : Dtil n * Dinv n = 1 := by
  unfold Dtil Dinv
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro m hm
  rw [← mul_pow,
    show (1 + C (m : ℚ) * X) * geomPow 1 m = 1 from by
      have h := geomPow_mul 1 m; rw [pow_one] at h; rw [mul_comm]; exact h,
    one_pow]

/-- The cleared form `S_b·D̃`, native in `ℚ⟦X⟧` (positive powers only). -/
noncomputable def RHSserGen (n : ℕ) (b : ℕ → ℕ → ℚ) : ℚ⟦X⟧ :=
  ∑ i ∈ Finset.Icc 1 6, ∑ j ∈ Finset.range (n + 1),
    C (b i j) * X ^ i *
      ((1 + C (j : ℚ) * X) ^ (6 - i)
        * ∏ m ∈ (Finset.range (n + 1)).erase j, (1 + C (m : ℚ) * X) ^ 6)

theorem Sgen_mul_Dtil (n : ℕ) (b : ℕ → ℕ → ℚ) : Sgen n b * Dtil n = RHSserGen n b := by
  unfold Sgen RHSserGen
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hi6 : i ≤ 6 := (Finset.mem_Icc.mp hi).2
  have key : geomPow i j * Dtil n
      = (1 + C (j : ℚ) * X) ^ (6 - i)
        * ∏ m ∈ (Finset.range (n + 1)).erase j, (1 + C (m : ℚ) * X) ^ 6 := by
    unfold Dtil
    rw [← Finset.mul_prod_erase (Finset.range (n + 1)) (fun m => (1 + C (m : ℚ) * X) ^ 6) hj,
      ← mul_assoc, geomPow_mul_pow6 i j hi6]
  calc C (b i j) * X ^ i * geomPow i j * Dtil n
      = C (b i j) * X ^ i * (geomPow i j * Dtil n) := by ring
    _ = _ := by rw [key]

/-! ## The polynomial side -/

/-- `RHSpoly` — the cleared PF-identity RHS, as an honest polynomial. -/
noncomputable def RHSpolyGen (n : ℕ) (b : ℕ → ℕ → ℚ) : Polynomial ℚ :=
  ∑ i ∈ Finset.Icc 1 6, ∑ j ∈ Finset.range (n + 1),
    Polynomial.C (b i j) * Polynomial.X ^ i *
      ((1 + Polynomial.C (j : ℚ) * Polynomial.X) ^ (6 - i)
        * ∏ m ∈ (Finset.range (n + 1)).erase j, (1 + Polynomial.C (m : ℚ) * Polynomial.X) ^ 6)

theorem RHSserGen_eq_coe (n : ℕ) (b : ℕ → ℕ → ℚ) :
    RHSserGen n b = (RHSpolyGen n b : ℚ⟦X⟧) := by
  unfold RHSserGen RHSpolyGen
  rw [← Polynomial.coeToPowerSeries.ringHom_apply]
  simp only [map_sum, map_prod, map_mul, map_pow, map_add, map_one,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]

/-- Reversal of a finite product: `x^{|s|}·∏ f = ∏ g` when `x·f = g` pointwise. -/
theorem prod_rev (x : ℚ) (s : Finset ℕ) (f g : ℕ → ℚ) (h : ∀ m, x * f m = g m) :
    x ^ s.card * ∏ m ∈ s, f m = ∏ m ∈ s, g m := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun m _ => h m)

/-- Sixth-power product reversal. -/
theorem prod_six_rev (x : ℚ) (hx : x ≠ 0) (s : Finset ℕ) :
    x ^ (6 * s.card) * ∏ m ∈ s, (x⁻¹ + (m : ℚ)) ^ 6 = ∏ m ∈ s, (1 + (m : ℚ) * x) ^ 6 := by
  rw [pow_mul, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun m _ => ?_)
  rw [← mul_pow]; congr 1; field_simp

/-- `Ñ(x) = x^{2n+1}·N_n(1/x)`, the reversed numerator, as a polynomial. -/
noncomputable def NtilP (n : ℕ) : Polynomial ℚ :=
  Polynomial.C ((Nat.factorial n : ℚ) ^ 4) * (1 + Polynomial.C ((n : ℚ) / 2) * Polynomial.X)
    * (∏ m ∈ Finset.Icc 1 n, (1 - Polynomial.C (m : ℚ) * Polynomial.X))
    * (∏ m ∈ Finset.Icc 1 n, (1 + Polynomial.C ((n : ℚ) + (m : ℚ)) * Polynomial.X))

/-- **E1.** `Ñ(x) = x^{2n+1}·N_n(1/x)`. -/
theorem eval_NtilP (n : ℕ) (x : ℚ) (hx : x ≠ 0) :
    (NtilP n).eval x = x ^ (2 * n + 1) * Nnum n x⁻¹ := by
  have hc : (Finset.Icc 1 n).card = n := by rw [Nat.card_Icc]; omega
  unfold NtilP Nnum
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_prod]
  rw [← prod_rev x (Finset.Icc 1 n) (fun m => x⁻¹ - (m : ℚ)) (fun m => 1 - (m : ℚ) * x)
        (fun m => by field_simp),
     ← prod_rev x (Finset.Icc 1 n) (fun m => x⁻¹ + (n : ℚ) + (m : ℚ))
        (fun m => 1 + ((n : ℚ) + (m : ℚ)) * x) (fun m => by field_simp; ring),
     hc, show (1 : ℚ) + (n : ℚ) / 2 * x = x * (x⁻¹ + (n : ℚ) / 2) from by field_simp]
  ring

/-- **E2 (base).** The reversal of `pf_cleared`: `RHSpoly(x) = x^{6n+6}·N_n(1/x)`. -/
theorem eval_RHSpoly (n : ℕ) (x : ℚ) (hx : x ≠ 0) :
    (RHSpolyGen n (acoeff n)).eval x = x ^ (6 * n + 6) * Nnum n x⁻¹ := by
  unfold RHSpolyGen
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_prod]
  rw [pf_cleared n x⁻¹, Finset.sum_comm]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi6 : i ≤ 6 := (Finset.mem_Icc.mp hi).2
  have hcard : ((Finset.range (n + 1)).erase j).card = n := by
    rw [Finset.card_erase_of_mem hj, Finset.card_range]; omega
  have hA : (1 + (j : ℚ) * x) ^ (6 - i) = x ^ (6 - i) * (x⁻¹ + (j : ℚ)) ^ (6 - i) := by
    rw [← mul_pow]; congr 1; field_simp
  have hpw : x ^ i * x ^ (6 - i) * x ^ (6 * n) = x ^ (6 * n + 6) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [hA, ← prod_six_rev x hx ((Finset.range (n + 1)).erase j), hcard, ← hpw]
  ring

/-- The reversed factorization, as polynomials: `RHSpoly = X^{4n+5}·Ñ`. -/
theorem RHSpoly_factor (n : ℕ) :
    RHSpolyGen n (acoeff n) = Polynomial.X ^ (4 * n + 5) * NtilP n := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono _ ((Set.finite_singleton (0 : ℚ)).infinite_compl)
  intro x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp only [Set.mem_setOf_eq]
  rw [eval_RHSpoly n x hx0, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    eval_NtilP n x hx0, show 6 * n + 6 = (4 * n + 5) + (2 * n + 1) from by ring, pow_add]
  ring

/-- `S` (base) is `X^{4n+5}` times a power series. -/
theorem Sser_factor (n : ℕ) :
    Sgen n (acoeff n) = X ^ (4 * n + 5) * ((NtilP n : ℚ⟦X⟧) * Dinv n) := by
  have h1 : Sgen n (acoeff n) * Dtil n = X ^ (4 * n + 5) * (NtilP n : ℚ⟦X⟧) := by
    rw [Sgen_mul_Dtil, RHSserGen_eq_coe, RHSpoly_factor, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_X]
  calc Sgen n (acoeff n) = Sgen n (acoeff n) * (Dtil n * Dinv n) := by rw [Dtil_mul_Dinv, mul_one]
    _ = Sgen n (acoeff n) * Dtil n * Dinv n := by ring
    _ = X ^ (4 * n + 5) * (NtilP n : ℚ⟦X⟧) * Dinv n := by rw [h1]
    _ = X ^ (4 * n + 5) * ((NtilP n : ℚ⟦X⟧) * Dinv n) := by ring

/-- **Lemma A (base).** `E_M(a) = 0` for `1 ≤ M ≤ 4n+4`. -/
theorem decay_a (n M : ℕ) (hM1 : 1 ≤ M) (hM : M ≤ 4 * n + 4) :
    EM n M (acoeff n) = 0 := by
  rw [← coeff_Sgen, Sser_factor, coeff_X_pow_mul', if_neg (by omega : ¬ 4 * n + 5 ≤ M)]

/-! ## Lemma A (companion) — the `ã`-chain

`decay_at` follows the same route with `-k(k+n)R_n` in place of `R_n`; the order at
`∞` drops to `4n+3`, giving vanishing for `M ≤ 4n+2`.  The only new analytic input is
the companion clearing identity `atclear` (the exact analogue of `pf_cleared`).  All
the packaging around it is discharged below. -/

/-- **Companion clearing identity** (the `ã`-analogue of `pf_cleared`).
`Σ_{j,i} ã_{i,j}(k+j)^{6-i}∏_{m≠j}(k+m)^6 = -k(k+n)·N_n(k)`.
This is the numerator of `-k(k+n)R_n`, cleared over `∏(k+m)^6`; it is exact because
the `ã`-shift loses only the boundary terms `Σ a_{1,j}` and `Σ a_{2,j}-Σ j a_{1,j}`,
both of which vanish (`= E_1(a) = E_2(a) = 0`, i.e. `decay_a` at `M=1,2`). -/
theorem atclear (n : ℕ) (k : ℚ) :
    (∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.Icc 1 6,
        atcoeff n i j * (k + (j : ℚ)) ^ (6 - i)
          * ∏ m ∈ (Finset.range (n + 1)).erase j, (k + (m : ℚ)) ^ 6)
      = -k * (k + (n : ℚ)) * Nnum n k := by
  have hE1 : ∑ j ∈ Finset.range (n + 1), acoeff n 1 j = 0 := by
    have h := decay_a n 1 le_rfl (by omega)
    rw [EM, show Finset.Icc 1 (min 6 1) = ({1} : Finset ℕ) from by decide] at h
    simpa [Cneg] using h
  have hE2 : (∑ j ∈ Finset.range (n + 1), acoeff n 2 j)
      - ∑ j ∈ Finset.range (n + 1), (j : ℚ) * acoeff n 1 j = 0 := by
    have h := decay_a n 2 (by omega) (by omega)
    rw [EM, show Finset.Icc 1 (min 6 2) = ({1, 2} : Finset ℕ) from by decide,
      Finset.sum_insert (by decide), Finset.sum_singleton] at h
    norm_num [Cneg] at h
    linear_combination h
  have hj_id : ∀ j, (∑ i ∈ Finset.Icc 1 6, atcoeff n i j * (k + (j : ℚ)) ^ (6 - i))
      = -k * (k + n) * (∑ i ∈ Finset.Icc 1 6, acoeff n i j * (k + (j : ℚ)) ^ (6 - i))
        + (acoeff n 1 j * (k + (j : ℚ)) + acoeff n 2 j - (2 * (j : ℚ) - n) * acoeff n 1 j)
            * (k + (j : ℚ)) ^ 6 := by
    intro j
    have h7 : acoeff n 7 j = 0 := by unfold acoeff; norm_num
    have h8 : acoeff n 8 j = 0 := by unfold acoeff; norm_num
    simp only [atcoeff, show (Finset.Icc 1 6 : Finset ℕ) = {1, 2, 3, 4, 5, 6} from by decide,
      Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton]
    norm_num [h7, h8]; ring
  have hstep : ∀ j ∈ Finset.range (n + 1),
      (∑ i ∈ Finset.Icc 1 6, atcoeff n i j * (k + (j : ℚ)) ^ (6 - i)
          * ∏ m ∈ (Finset.range (n + 1)).erase j, (k + (m : ℚ)) ^ 6)
        = -k * (k + n) * (∑ i ∈ Finset.Icc 1 6, acoeff n i j * (k + (j : ℚ)) ^ (6 - i)
              * ∏ m ∈ (Finset.range (n + 1)).erase j, (k + (m : ℚ)) ^ 6)
          + (acoeff n 1 j * (k + (j : ℚ)) + acoeff n 2 j - (2 * (j : ℚ) - n) * acoeff n 1 j)
              * ∏ m ∈ Finset.range (n + 1), (k + (m : ℚ)) ^ 6 := by
    intro j hj
    rw [← Finset.sum_mul, hj_id j]
    conv_rhs =>
      rw [← Finset.sum_mul,
        ← Finset.mul_prod_erase (Finset.range (n + 1)) (fun m => (k + (m : ℚ)) ^ 6) hj]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum, ← pf_cleared n k,
    ← Finset.sum_mul]
  have hcorr : ∑ j ∈ Finset.range (n + 1),
      (acoeff n 1 j * (k + (j : ℚ)) + acoeff n 2 j - (2 * (j : ℚ) - n) * acoeff n 1 j) = 0 := by
    have expand : ∀ j, acoeff n 1 j * (k + (j : ℚ)) + acoeff n 2 j
          - (2 * (j : ℚ) - n) * acoeff n 1 j
        = (k + n) * acoeff n 1 j + (acoeff n 2 j - (j : ℚ) * acoeff n 1 j) := by intro j; ring
    simp only [expand]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hE1, mul_zero, zero_add,
      Finset.sum_sub_distrib, hE2]
  rw [hcorr, zero_mul, add_zero]

/-- Reversal of `atclear`: `RHSpoly(ã)(x) = -(1+nx)·x^{6n+4}·N_n(1/x)`, i.e.
`x^2·RHSpoly(ã)(x) = -(1+nx)·RHSpoly(a)(x)`. -/
theorem eval_RHSpoly_at (n : ℕ) (x : ℚ) (hx : x ≠ 0) :
    (RHSpolyGen n (atcoeff n)).eval x
      = -(1 + (n : ℚ) * x) * x ^ (6 * n + 4) * Nnum n x⁻¹ := by
  unfold RHSpolyGen
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_prod]
  rw [Finset.sum_comm]
  have key : (∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.Icc 1 6,
        atcoeff n i j * (x⁻¹ + (j : ℚ)) ^ (6 - i)
          * ∏ m ∈ (Finset.range (n + 1)).erase j, (x⁻¹ + (m : ℚ)) ^ 6)
      = -x⁻¹ * (x⁻¹ + (n : ℚ)) * Nnum n x⁻¹ := atclear n x⁻¹
  -- reverse each term by x^{6n+6}, exactly as in `eval_RHSpoly`
  have hrev : ∀ j ∈ Finset.range (n + 1), ∀ i ∈ Finset.Icc 1 6,
      atcoeff n i j * x ^ i * ((1 + (j : ℚ) * x) ^ (6 - i)
          * ∏ m ∈ (Finset.range (n + 1)).erase j, (1 + (m : ℚ) * x) ^ 6)
        = x ^ (6 * n + 6) * (atcoeff n i j * (x⁻¹ + (j : ℚ)) ^ (6 - i)
            * ∏ m ∈ (Finset.range (n + 1)).erase j, (x⁻¹ + (m : ℚ)) ^ 6) := by
    intro j hj i hi
    have hi6 : i ≤ 6 := (Finset.mem_Icc.mp hi).2
    have hcard : ((Finset.range (n + 1)).erase j).card = n := by
      rw [Finset.card_erase_of_mem hj, Finset.card_range]; omega
    have hA : (1 + (j : ℚ) * x) ^ (6 - i) = x ^ (6 - i) * (x⁻¹ + (j : ℚ)) ^ (6 - i) := by
      rw [← mul_pow]; congr 1; field_simp
    have hpw : x ^ i * x ^ (6 - i) * x ^ (6 * n) = x ^ (6 * n + 6) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [hA, ← prod_six_rev x hx ((Finset.range (n + 1)).erase j), hcard, ← hpw]; ring
  rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun i hi => hrev j hj i hi))]
  simp only [← Finset.mul_sum]
  rw [key, show x ^ (6 * n + 6) = x ^ 2 * x ^ (6 * n + 4) from by rw [← pow_add]; congr 1; omega]
  field_simp

/-- Companion polynomial factorization: `RHSpoly(ã) = X^{4n+3}·(-(1+nX)·Ñ)`. -/
theorem RHSpoly_at_factor (n : ℕ) :
    RHSpolyGen n (atcoeff n)
      = Polynomial.X ^ (4 * n + 3) * (-(1 + Polynomial.C (n : ℚ) * Polynomial.X) * NtilP n) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono _ ((Set.finite_singleton (0 : ℚ)).infinite_compl)
  intro x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp only [Set.mem_setOf_eq]
  rw [eval_RHSpoly_at n x hx0]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_neg,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_C, eval_NtilP n x hx0]
  rw [show 6 * n + 4 = (4 * n + 3) + (2 * n + 1) from by ring, pow_add]
  ring

/-- `S(ã)` is `X^{4n+3}` times a power series. -/
theorem Sser_at_factor (n : ℕ) :
    Sgen n (atcoeff n)
      = X ^ (4 * n + 3)
          * (((-(1 + Polynomial.C (n : ℚ) * Polynomial.X) * NtilP n : Polynomial ℚ) : ℚ⟦X⟧) * Dinv n) := by
  have h1 : Sgen n (atcoeff n) * Dtil n
      = X ^ (4 * n + 3) * ((-(1 + Polynomial.C (n : ℚ) * Polynomial.X) * NtilP n : Polynomial ℚ) : ℚ⟦X⟧) := by
    rw [Sgen_mul_Dtil, RHSserGen_eq_coe, RHSpoly_at_factor, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_X]
  calc Sgen n (atcoeff n) = Sgen n (atcoeff n) * (Dtil n * Dinv n) := by rw [Dtil_mul_Dinv, mul_one]
    _ = Sgen n (atcoeff n) * Dtil n * Dinv n := by ring
    _ = X ^ (4 * n + 3) * ((-(1 + Polynomial.C (n : ℚ) * Polynomial.X) * NtilP n : Polynomial ℚ) : ℚ⟦X⟧)
          * Dinv n := by rw [h1]
    _ = X ^ (4 * n + 3)
          * (((-(1 + Polynomial.C (n : ℚ) * Polynomial.X) * NtilP n : Polynomial ℚ) : ℚ⟦X⟧) * Dinv n) := by ring

/-- **Lemma A (companion).** `E_M(ã) = 0` for `1 ≤ M ≤ 4n+2`. -/
theorem decay_at (n M : ℕ) (hM1 : 1 ≤ M) (hM : M ≤ 4 * n + 2) :
    EM n M (atcoeff n) = 0 := by
  rw [← coeff_Sgen, Sser_at_factor, coeff_X_pow_mul', if_neg (by omega : ¬ 4 * n + 3 ≤ M)]

end Cbcert.Decay
