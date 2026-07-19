import Cbcert.Defs

/-!
# The cleared partial-fraction identity (Layer L1, load-bearing)

The concrete coefficients `acoeff n i j = [t^{6-i}] B_j` are, by construction, the
partial-fraction coefficients of `R_n`. Cleared of denominators, that is the
polynomial identity `pf_cleared` below.

## Proof architecture

A crucial simplification: the Lean `tsMul` (Defs.lean) is the *exact* Cauchy product
`fun r => ∑_{s≤r} a s * b (r-s)` (no truncation), so `Bseries n j r` equals the exact
power-series coefficient of the product of the factor series, for *every* `r`.

* `mk_tsMul` : `PowerSeries.mk (tsMul a b) = mk a * mk b`.
* `tsInv6_inv` : `(C c + X)^6 * mk (tsInv6 c) = 1` for `c ≠ 0` (the local inverse), via
  `PowerSeries.invOneSubPow` and `rescale`.
* fold lemmas : `mk (Bseries n j)` is the honest product of the factor series.
* per-pole divisibility `(X + C j)^6 ∣ (Np - term_j)` via a Taylor shift into
  `PowerSeries` and an order-≥6 argument.
* assembly : the `(X+C j)^6` are pairwise coprime, so `∏ (X+C j)^6 = D_n ∣ (Np - RHS)`;
  a degree count `deg (Np - RHS) ≤ 6n+5 < 6n+6 = deg D_n` forces `Np = RHS`.
-/

namespace Cbcert.PartialFraction

open Cbcert
open scoped BigOperators PowerSeries

/-! ## Part 1 — power-series foundations -/

/-- `List.foldl (· + f ·)` over `List.range m` is the `Finset.range` sum. -/
lemma foldl_range_sum (m : ℕ) (f : ℕ → ℚ) :
    (List.range m).foldl (fun acc s => acc + f s) 0 = ∑ s ∈ Finset.range m, f s := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
      simp

/-- `tsMul` is the exact Cauchy coefficient (no truncation). -/
lemma tsMul_eq_sum (a b : ℕ → ℚ) (r : ℕ) :
    tsMul a b r = ∑ s ∈ Finset.range (r + 1), a s * b (r - s) := by
  simp only [tsMul]
  exact foldl_range_sum (r + 1) (fun s => a s * b (r - s))

/-- **Key product lemma.** `mk (tsMul a b) = mk a * mk b`. -/
lemma mk_tsMul (a b : ℕ → ℚ) :
    PowerSeries.mk (tsMul a b) = PowerSeries.mk a * PowerSeries.mk b := by
  ext r
  rw [PowerSeries.coeff_mk, tsMul_eq_sum, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro s _
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]

/-- `mk (tsConst c) = C c`. -/
lemma mk_tsConst (c : ℚ) : PowerSeries.mk (tsConst c) = PowerSeries.C c := by
  ext r
  rw [PowerSeries.coeff_mk, tsConst]
  rcases eq_or_ne r 0 with h | h
  · subst h; simp
  · rw [if_neg h, PowerSeries.coeff_C, if_neg h]

/-- `mk (tsLin c) = C c + X`. -/
lemma mk_tsLin (c : ℚ) :
    PowerSeries.mk (tsLin c) = PowerSeries.C c + PowerSeries.X := by
  ext r
  rw [PowerSeries.coeff_mk, tsLin, map_add, PowerSeries.coeff_C, PowerSeries.coeff_X]
  rcases eq_or_ne r 0 with h | h
  · subst h; simp
  · rw [if_neg h, if_neg h]
    rcases eq_or_ne r 1 with h1 | h1
    · subst h1; simp
    · rw [if_neg h1]; simp

/-- **Local inverse.** For `c ≠ 0`, `mk (tsInv6 c)` is the inverse of `(C c + X)^6`. -/
lemma tsInv6_inv (c : ℚ) (hc : c ≠ 0) :
    (PowerSeries.C c + PowerSeries.X) ^ 6 * PowerSeries.mk (tsInv6 c) = 1 := by
  set r : ℚ := -c⁻¹ with hr
  -- the (1-X)^{-6} series
  set g6 : ℚ⟦X⟧ := PowerSeries.mk (fun n => (Nat.choose (5 + n) 5 : ℚ)) with hg6
  have hg6mul : g6 * (1 - PowerSeries.X) ^ 6 = 1 := by
    have := PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one (S := ℚ) (d := 5)
    simpa using this
  -- Claim A : mk (tsInv6 c) = C (c^6)⁻¹ * rescale r g6
  have hA : PowerSeries.mk (tsInv6 c)
      = PowerSeries.C (c ^ 6)⁻¹ * PowerSeries.rescale r g6 := by
    ext m
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
        hg6, PowerSeries.coeff_mk, tsInv6]
    have hcs : (Nat.choose (5 + m) 5 : ℚ) = (Nat.choose (5 + m) m : ℚ) := by
      have : Nat.choose (5 + m) (5 + m - 5) = Nat.choose (5 + m) 5 :=
        Nat.choose_symm (by omega)
      rw [show 5 + m - 5 = m by omega] at this
      rw [this]
    rw [hcs, hr]
    have hneg : (-c⁻¹ : ℚ) ^ m = (-1) ^ m * (c ^ m)⁻¹ := by
      rw [← neg_one_mul, mul_pow, inv_pow]
    rw [hneg]
    field_simp
    ring
  -- Claim B : (C c + X)^6 = C (c^6) * rescale r ((1-X)^6)
  have hB : (PowerSeries.C c + PowerSeries.X) ^ 6
      = PowerSeries.C (c ^ 6) * PowerSeries.rescale r ((1 - PowerSeries.X) ^ 6) := by
    have hrX : PowerSeries.rescale r (1 - PowerSeries.X)
        = 1 + PowerSeries.C c⁻¹ * PowerSeries.X := by
      rw [map_sub, map_one, PowerSeries.rescale_X, hr, map_neg, neg_mul, sub_neg_eq_add]
    have hfac : PowerSeries.C c + PowerSeries.X
        = PowerSeries.C c * (1 + PowerSeries.C c⁻¹ * PowerSeries.X) := by
      rw [mul_add, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
    rw [hfac, mul_pow, ← map_pow PowerSeries.C c 6, ← hrX,
        ← map_pow (PowerSeries.rescale r) (1 - PowerSeries.X) 6]
  rw [hA, hB, mul_mul_mul_comm, ← map_mul, ← map_mul, mul_inv_cancel₀ (pow_ne_zero 6 hc),
      map_one, one_mul, mul_comm ((1 - PowerSeries.X) ^ 6), hg6mul, map_one]

/-! ## Part 2 — fold identities: `mk (Bseries n j)` as a product of factor series -/

/-- Single-`tsMul` fold. -/
lemma mk_foldl_tsMul {α : Type*} (g : α → (ℕ → ℚ)) (l : List α) (s0 : ℕ → ℚ) :
    PowerSeries.mk (l.foldl (fun s x => tsMul s (g x)) s0)
      = PowerSeries.mk s0 * (l.map (fun x => PowerSeries.mk (g x))).prod := by
  induction l generalizing s0 with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih (tsMul s0 (g x)), mk_tsMul, List.map_cons, List.prod_cons]
      ring

/-- Double-`tsMul` fold (used by the linear-factor pass of `Bseries`). -/
lemma mk_foldl_tsMul2 {α : Type*} (g h : α → (ℕ → ℚ)) (l : List α) (s0 : ℕ → ℚ) :
    PowerSeries.mk (l.foldl (fun s x => tsMul (tsMul s (g x)) (h x)) s0)
      = PowerSeries.mk s0
        * (l.map (fun x => PowerSeries.mk (g x) * PowerSeries.mk (h x))).prod := by
  induction l generalizing s0 with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih (tsMul (tsMul s0 (g x)) (h x)), mk_tsMul, mk_tsMul,
          List.map_cons, List.prod_cons]
      ring

/-- `mk (Bseries n j)` = (linear-factor product) · (inverse-factor product). -/
lemma mk_Bseries (n j : ℕ) :
    PowerSeries.mk (Bseries n j)
      = (PowerSeries.C ((Nat.factorial n : ℚ) ^ 4)
          * (PowerSeries.C ((n : ℚ) / 2 - j) + PowerSeries.X))
        * ((List.range n).map (fun m : ℕ =>
            (PowerSeries.C (-(j : ℚ) - ((m : ℚ) + 1)) + PowerSeries.X)
            * (PowerSeries.C ((n : ℚ) + ((m : ℚ) + 1) - j) + PowerSeries.X))).prod
        * (((List.range (n + 1)).filter (· ≠ j)).map (fun m : ℕ =>
            PowerSeries.mk (tsInv6 ((m : ℚ) - j)))).prod := by
  simp only [Bseries, bind_pure_comp, List.map_eq_map, List.foldl_map]
  rw [mk_foldl_tsMul (g := fun m : ℕ => tsInv6 ((m : ℚ) - (j : ℚ))),
      mk_foldl_tsMul2 (g := fun m : ℕ => tsLin (-(j : ℚ) - ((m : ℚ) + 1)))
        (h := fun m : ℕ => tsLin ((n : ℚ) + ((m : ℚ) + 1) - j)),
      mk_tsMul, mk_tsConst, mk_tsLin]
  simp only [mk_tsLin]

/-! ## Part 3 — the polynomials and the assembly -/

/-- `N_n(k)` — the numerator of `R_n`. -/
def Nnum (n : ℕ) (k : ℚ) : ℚ :=
  (Nat.factorial n : ℚ) ^ 4 * (k + (n : ℚ) / 2)
    * (∏ m ∈ Finset.Icc 1 n, (k - (m : ℚ)))
    * (∏ m ∈ Finset.Icc 1 n, (k + (n : ℚ) + (m : ℚ)))

open Polynomial in
/-- `N_n` as a polynomial (indexed by `range n`, matching `Bseries`). -/
noncomputable def Np (n : ℕ) : ℚ[X] :=
  Polynomial.C ((Nat.factorial n : ℚ) ^ 4) * (X + Polynomial.C ((n : ℚ) / 2))
    * (∏ m ∈ Finset.range n, (X - Polynomial.C ((m : ℚ) + 1)))
    * (∏ m ∈ Finset.range n, (X + Polynomial.C (n : ℚ) + Polynomial.C ((m : ℚ) + 1)))

open Polynomial in
/-- The `j`-th cleared principal part, as a polynomial. -/
noncomputable def termP (n j : ℕ) : ℚ[X] :=
  (∑ i ∈ Finset.Icc 1 6, Polynomial.C (acoeff n i j) * (X + Polynomial.C (j : ℚ)) ^ (6 - i))
    * ∏ m ∈ (Finset.range (n + 1)).erase j, (X + Polynomial.C (m : ℚ)) ^ 6

open Polynomial in
/-- The full cleared right-hand side. -/
noncomputable def RHSp (n : ℕ) : ℚ[X] := ∑ j ∈ Finset.range (n + 1), termP n j

open Polynomial in
/-- `D_n = ∏_{j=0}^n (X+j)^6`. -/
noncomputable def Dprod (n : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.range (n + 1), (X + Polynomial.C (j : ℚ)) ^ 6

/-- Reindex `∏_{m=1}^n f m = ∏_{m<n} f (m+1)`. -/
lemma prod_Icc_one_eq_range {M : Type*} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∏ m ∈ Finset.Icc 1 n, f m = ∏ m ∈ Finset.range n, f (m + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ← ih, ← Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]

open Polynomial in
lemma Nnum_eq_eval (n : ℕ) (k : ℚ) : Nnum n k = (Np n).eval k := by
  rw [Nnum, Np, prod_Icc_one_eq_range n (fun m => k - (m : ℚ)),
      prod_Icc_one_eq_range n (fun m => k + (n : ℚ) + (m : ℚ))]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_prod]
  push_cast
  ring

open Polynomial in
lemma RHS_eq_eval (n : ℕ) (k : ℚ) :
    (∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.Icc 1 6,
        acoeff n i j * (k + (j : ℚ)) ^ (6 - i)
          * ∏ m ∈ (Finset.range (n + 1)).erase j, (k + (m : ℚ)) ^ 6)
      = (RHSp n).eval k := by
  rw [RHSp]
  simp only [termP, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    Finset.sum_mul]

/-! ### Per-pole divisibility -/

/-- The degree-≤5 principal jet, as a power series. -/
noncomputable def P5expr (n j : ℕ) : ℚ⟦X⟧ :=
  ∑ i ∈ Finset.Icc 1 6, PowerSeries.C (acoeff n i j) * PowerSeries.X ^ (6 - i)

/-- The (analytic) denominator jet at the pole `−j`. -/
noncomputable def Sjexpr (n j : ℕ) : ℚ⟦X⟧ :=
  ∏ m ∈ (Finset.range (n + 1)).erase j, (PowerSeries.X + PowerSeries.C ((m : ℚ) - j)) ^ 6

/-- `List.range` product = `Finset.range` product. -/
lemma list_range_map_prod {M : Type*} [CommMonoid M] (m : ℕ) (F : ℕ → M) :
    ((List.range m).map F).prod = ∏ i ∈ Finset.range m, F i := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]
      simp

/-- Product over the `(· ≠ j)`-filtered range list = product over `erase j`. -/
lemma list_filter_prod_eq {M : Type*} [CommMonoid M] (n j : ℕ) (F : ℕ → M) :
    (((List.range (n + 1)).filter (· ≠ j)).map F).prod
      = ∏ m ∈ (Finset.range (n + 1)).erase j, F m := by
  have htf : ((List.range (n + 1)).filter (· ≠ j)).toFinset = (Finset.range (n + 1)).erase j := by
    ext m
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_erase,
      Finset.mem_range, decide_eq_true_eq, ne_eq]
    tauto
  rw [← List.prod_toFinset F (List.nodup_range.filter _), htf]

open Polynomial in
/-- `taylor` distributes over finite products. -/
lemma taylor_prod {ι : Type*} (r : ℚ) (s : Finset ι) (f : ι → ℚ[X]) :
    Polynomial.taylor r (∏ i ∈ s, f i) = ∏ i ∈ s, Polynomial.taylor r (f i) := by
  simp only [← Polynomial.coe_taylorAlgHom]
  exact map_prod (Polynomial.taylorAlgHom r) f s

open Polynomial in
/-- `taylor` distributes over powers. -/
lemma taylor_pow (r : ℚ) (p : ℚ[X]) (k : ℕ) :
    Polynomial.taylor r (p ^ k) = (Polynomial.taylor r p) ^ k := by
  simp only [← Polynomial.coe_taylorAlgHom]
  exact map_pow (Polynomial.taylorAlgHom r) p k

open Polynomial in
lemma coe_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    (↑(∏ i ∈ s, f i) : ℚ⟦X⟧) = ∏ i ∈ s, (↑(f i) : ℚ⟦X⟧) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply]

open Polynomial in
lemma coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    (↑(∑ i ∈ s, f i) : ℚ⟦X⟧) = ∑ i ∈ s, (↑(f i) : ℚ⟦X⟧) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply]

open Polynomial in
/-- `taylor(-j)(X + C j) = X` (shift the pole to `0`), as a power series. -/
lemma coe_taylor_X_add_C (j : ℕ) :
    (↑(Polynomial.taylor (-(j : ℚ)) (X + Polynomial.C (j : ℚ))) : ℚ⟦X⟧) = PowerSeries.X := by
  rw [map_add, Polynomial.taylor_X, Polynomial.taylor_C, Polynomial.coe_add, Polynomial.coe_add,
      Polynomial.coe_X, Polynomial.coe_C, Polynomial.coe_C, add_assoc, ← map_add, neg_add_cancel,
      map_zero, add_zero]

open Polynomial in
/-- The shifted denominator product, as a power series. -/
lemma taylor_prodpart_coe (n j : ℕ) :
    (↑(Polynomial.taylor (-(j : ℚ))
        (∏ m ∈ (Finset.range (n + 1)).erase j, (X + Polynomial.C (m : ℚ)) ^ 6)) : ℚ⟦X⟧)
      = Sjexpr n j := by
  rw [taylor_prod, coe_prod, Sjexpr]
  apply Finset.prod_congr rfl
  intro m _
  rw [taylor_pow, Polynomial.coe_pow]
  congr 1
  rw [map_add, Polynomial.taylor_X, Polynomial.taylor_C, Polynomial.coe_add, Polynomial.coe_add,
      Polynomial.coe_X, Polynomial.coe_C, Polynomial.coe_C, add_assoc, ← map_add]
  congr 2
  ring

open Polynomial in
/-- **(A)** The shifted numerator equals `mk (Bseries) · Sⱼ`. -/
lemma taylor_Np_coe (n j : ℕ) :
    (↑(Polynomial.taylor (-(j : ℚ)) (Np n)) : ℚ⟦X⟧) = PowerSeries.mk (Bseries n j) * Sjexpr n j := by
  -- cancel the inverse factors against `Sⱼ`
  have hcancel : (∏ m ∈ (Finset.range (n + 1)).erase j, PowerSeries.mk (tsInv6 ((m : ℚ) - j)))
      * Sjexpr n j = 1 := by
    rw [Sjexpr, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro m hm
    have hmj : (m : ℚ) - (j : ℚ) ≠ 0 := by
      have := (Finset.mem_erase.mp hm).1
      simp only [sub_ne_zero]; exact_mod_cast this
    rw [add_comm PowerSeries.X (PowerSeries.C ((m : ℚ) - j)), mul_comm]
    exact tsInv6_inv _ hmj
  rw [mk_Bseries,
      list_filter_prod_eq n j (fun m : ℕ => PowerSeries.mk (tsInv6 ((m : ℚ) - (j : ℚ)))),
      mul_assoc, hcancel, mul_one, List.prod_map_mul, list_range_map_prod, list_range_map_prod]
  -- now the linear-factor part
  rw [Np, Polynomial.taylor_mul, Polynomial.taylor_mul, Polynomial.taylor_mul, taylor_prod,
      taylor_prod, Polynomial.taylor_C, Polynomial.coe_mul, Polynomial.coe_mul,
      Polynomial.coe_mul, Polynomial.coe_C, coe_prod, coe_prod]
  -- per-factor coe identities (with the constants recombined)
  have hc0 : (↑(Polynomial.taylor (-(j : ℚ)) (X + Polynomial.C ((n : ℚ) / 2))) : ℚ⟦X⟧)
      = PowerSeries.C ((n : ℚ) / 2 - j) + PowerSeries.X := by
    rw [map_add, Polynomial.taylor_X, Polynomial.taylor_C, Polynomial.coe_add, Polynomial.coe_add,
        Polynomial.coe_X, Polynomial.coe_C, Polynomial.coe_C, add_assoc, ← map_add, add_comm]
    congr 2; ring
  have hc1 : ∀ m : ℕ, (↑(Polynomial.taylor (-(j : ℚ)) (X - Polynomial.C ((m : ℚ) + 1))) : ℚ⟦X⟧)
      = PowerSeries.C (-(j : ℚ) - ((m : ℚ) + 1)) + PowerSeries.X := by
    intro m
    rw [map_sub, Polynomial.taylor_X, Polynomial.taylor_C, Polynomial.coe_sub, Polynomial.coe_add,
        Polynomial.coe_X, Polynomial.coe_C, Polynomial.coe_C, add_sub_assoc, ← map_sub, add_comm]
  have hc2 : ∀ m : ℕ,
      (↑(Polynomial.taylor (-(j : ℚ)) (X + Polynomial.C (n : ℚ) + Polynomial.C ((m : ℚ) + 1))) : ℚ⟦X⟧)
      = PowerSeries.C ((n : ℚ) + ((m : ℚ) + 1) - j) + PowerSeries.X := by
    intro m
    rw [map_add, map_add, Polynomial.taylor_X, Polynomial.taylor_C, Polynomial.taylor_C,
        Polynomial.coe_add, Polynomial.coe_add, Polynomial.coe_add, Polynomial.coe_X,
        Polynomial.coe_C, Polynomial.coe_C, Polynomial.coe_C, add_assoc, add_assoc, ← map_add,
        ← map_add, add_comm]
    congr 2; ring
  rw [hc0, Finset.prod_congr rfl (fun m _ => hc1 m), Finset.prod_congr rfl (fun m _ => hc2 m)]
  ring

open Polynomial in
/-- **(B)** The shifted `j`-term equals `(principal jet) · Sⱼ`. -/
lemma taylor_termP_coe (n j : ℕ) :
    (↑(Polynomial.taylor (-(j : ℚ)) (termP n j)) : ℚ⟦X⟧) = P5expr n j * Sjexpr n j := by
  rw [termP, Polynomial.taylor_mul, Polynomial.coe_mul, taylor_prodpart_coe]
  congr 1
  rw [P5expr, map_sum, coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.taylor_mul, Polynomial.taylor_C, taylor_pow, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_pow, coe_taylor_X_add_C]

open Polynomial in
/-- **The per-pole congruence** (the analytic heart): the `j`-th cleared term agrees with
`N_n` to order 6 at the pole `−j`. -/
lemma per_pole_congr (n j : ℕ) (_hjn : j ≤ n) :
    (X + Polynomial.C (j : ℚ)) ^ 6 ∣ (Np n - termP n j) := by
  -- Reduce to `X^6 ∣ taylor(-j) (Np - termP)` by shifting the pole to 0.
  suffices hX : Polynomial.X ^ 6 ∣ Polynomial.taylor (-(j : ℚ)) (Np n - termP n j) by
    obtain ⟨q, hq⟩ := hX
    refine ⟨Polynomial.taylor (j : ℚ) q, ?_⟩
    have hgg : Polynomial.taylor (j : ℚ) (Polynomial.taylor (-(j : ℚ)) (Np n - termP n j))
        = Np n - termP n j := by
      rw [Polynomial.taylor_taylor, add_neg_cancel, Polynomial.taylor_zero]
    calc Np n - termP n j
        = Polynomial.taylor (j : ℚ) (Polynomial.taylor (-(j : ℚ)) (Np n - termP n j)) := hgg.symm
      _ = Polynomial.taylor (j : ℚ) (Polynomial.X ^ 6 * q) := by rw [hq]
      _ = (X + Polynomial.C (j : ℚ)) ^ 6 * Polynomial.taylor (j : ℚ) q := by
            rw [Polynomial.taylor_mul, Polynomial.taylor_X_pow]
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [← Polynomial.coeff_coe]
  -- The shifted difference factors as `(mk Bseries - P5) · Sⱼ`.
  have hdecomp : (↑(Polynomial.taylor (-(j : ℚ)) (Np n - termP n j)) : ℚ⟦X⟧)
      = (PowerSeries.mk (Bseries n j) - P5expr n j) * Sjexpr n j := by
    rw [map_sub, Polynomial.coe_sub, taylor_Np_coe, taylor_termP_coe, sub_mul]
  rw [hdecomp]
  -- `mk Bseries - P5` vanishes to order 6.
  have hdvd : PowerSeries.X ^ 6 ∣ (PowerSeries.mk (Bseries n j) - P5expr n j) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro e he
    rw [map_sub, PowerSeries.coeff_mk]
    have hP5 : (PowerSeries.coeff e) (P5expr n j) = Bseries n j e := by
      rw [P5expr, map_sum, Finset.sum_eq_single (6 - e)]
      · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_pos (by omega), mul_one, acoeff,
            if_pos ⟨by omega, by omega⟩, show 6 - (6 - e) = e by omega]
      · intro i hi hne
        rw [Finset.mem_Icc] at hi
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (by omega), mul_zero]
      · intro h
        exact absurd (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) h
    rw [hP5, sub_self]
  exact PowerSeries.X_pow_dvd_iff.mp (hdvd.mul_right (Sjexpr n j)) d hd

open Polynomial in
/-- For a different pole `j' ≠ j`, the whole `j'`-term is divisible by `(X+j)^6`. -/
lemma other_pole_dvd (n j j' : ℕ) (hj : j ∈ Finset.range (n + 1))
    (_hj' : j' ∈ Finset.range (n + 1)) (hne : j' ≠ j) :
    (X + Polynomial.C (j : ℚ)) ^ 6 ∣ termP n j' := by
  rw [termP]
  have h : (X + Polynomial.C (j : ℚ)) ^ 6
      ∣ ∏ m ∈ (Finset.range (n + 1)).erase j', (X + Polynomial.C (m : ℚ)) ^ 6 :=
    Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hne.symm, hj⟩)
  exact h.mul_left _

open Polynomial in
/-- Each `(X+j)^6` divides `N_n − RHS_n`. -/
lemma per_pole_dvd (n j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
    (X + Polynomial.C (j : ℚ)) ^ 6 ∣ (Np n - RHSp n) := by
  have hjn : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
  have hcongr := per_pole_congr n j hjn
  have hsplit : RHSp n = termP n j + ∑ j' ∈ (Finset.range (n + 1)).erase j, termP n j' := by
    rw [RHSp, ← Finset.add_sum_erase _ _ hj]
  have hother : (X + Polynomial.C (j : ℚ)) ^ 6
      ∣ ∑ j' ∈ (Finset.range (n + 1)).erase j, termP n j' := by
    refine Finset.dvd_sum ?_
    intro j' hj'
    rw [Finset.mem_erase] at hj'
    exact other_pole_dvd n j j' hj hj'.2 hj'.1
  have : Np n - RHSp n = (Np n - termP n j) - ∑ j' ∈ (Finset.range (n + 1)).erase j, termP n j' := by
    rw [hsplit]; ring
  rw [this]
  exact dvd_sub hcongr hother

/-! ### Coprimality and degree -/

open Polynomial in
lemma Dprod_dvd (n : ℕ) : Dprod n ∣ (Np n - RHSp n) := by
  rw [Dprod]
  refine Finset.prod_dvd_of_coprime ?_ (fun j hj => per_pole_dvd n j hj)
  intro i _ j _ hij
  have hbase : IsCoprime (X - Polynomial.C (-(i : ℚ))) (X - Polynomial.C (-(j : ℚ))) := by
    have hinj : Function.Injective (fun k : ℕ => -(k : ℚ)) := by
      intro a b h; exact_mod_cast neg_injective h
    exact pairwise_coprime_X_sub_C hinj hij
  have e1 : X - Polynomial.C (-(i : ℚ)) = X + Polynomial.C (i : ℚ) := by
    rw [map_neg, sub_neg_eq_add]
  have e2 : X - Polynomial.C (-(j : ℚ)) = X + Polynomial.C (j : ℚ) := by
    rw [map_neg, sub_neg_eq_add]
  rw [e1, e2] at hbase
  exact hbase.pow

open Polynomial in
lemma natDegree_Dprod (n : ℕ) : (Dprod n).natDegree = 6 * (n + 1) := by
  rw [Dprod, natDegree_prod _ _ (fun j _ => pow_ne_zero _ (monic_X_add_C _).ne_zero)]
  have h : ∀ j ∈ Finset.range (n + 1), ((X + Polynomial.C (j : ℚ)) ^ 6).natDegree = 6 := by
    intro j _; rw [(monic_X_add_C _).natDegree_pow, natDegree_X_add_C]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

open Polynomial in
lemma natDegree_Np_le (n : ℕ) : (Np n).natDegree ≤ 6 * n + 5 := by
  have h1 : (Polynomial.C ((Nat.factorial n : ℚ) ^ 4) * (X + Polynomial.C ((n : ℚ) / 2))).natDegree
      ≤ 1 := (natDegree_C_mul_le _ _).trans (le_of_eq (natDegree_X_add_C _))
  have hP1 : (∏ m ∈ Finset.range n, (X - Polynomial.C ((m : ℚ) + 1))).natDegree ≤ n := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun m _ => le_of_eq (natDegree_X_sub_C _))).trans ?_
    simp
  have hP2 : (∏ m ∈ Finset.range n,
      (X + Polynomial.C (n : ℚ) + Polynomial.C ((m : ℚ) + 1))).natDegree ≤ n := by
    refine (natDegree_prod_le _ _).trans ?_
    have hle : ∀ m ∈ Finset.range n,
        (X + Polynomial.C (n : ℚ) + Polynomial.C ((m : ℚ) + 1)).natDegree ≤ 1 := by
      intro m _; rw [add_assoc, ← map_add]; exact le_of_eq (natDegree_X_add_C _)
    exact (Finset.sum_le_sum hle).trans (by simp)
  rw [Np]
  refine (natDegree_mul_le).trans ?_
  refine (add_le_add ((natDegree_mul_le).trans (add_le_add h1 hP1)) hP2).trans ?_
  omega

open Polynomial in
lemma natDegree_termP_le (n j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
    (termP n j).natDegree ≤ 6 * n + 5 := by
  rw [termP]
  have hsum : (∑ i ∈ Finset.Icc 1 6,
      Polynomial.C (acoeff n i j) * (X + Polynomial.C (j : ℚ)) ^ (6 - i)).natDegree ≤ 5 := by
    refine natDegree_sum_le_of_forall_le (Finset.Icc 1 6)
      (fun i => Polynomial.C (acoeff n i j) * (X + Polynomial.C (j : ℚ)) ^ (6 - i))
      (fun i hi => ?_)
    refine (natDegree_C_mul_le _ _).trans ((natDegree_pow_le).trans ?_)
    rw [natDegree_X_add_C]
    rw [Finset.mem_Icc] at hi; omega
  have hprod : (∏ m ∈ (Finset.range (n + 1)).erase j,
      (X + Polynomial.C (m : ℚ)) ^ 6).natDegree ≤ 6 * n := by
    refine (natDegree_prod_le _ _).trans ?_
    have hle : ∀ m ∈ (Finset.range (n + 1)).erase j,
        ((X + Polynomial.C (m : ℚ)) ^ 6).natDegree ≤ 6 := by
      intro m _; rw [natDegree_pow, natDegree_X_add_C]
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_const, Finset.card_erase_of_mem hj, Finset.card_range, smul_eq_mul]
    omega
  exact (natDegree_mul_le).trans ((add_le_add hsum hprod).trans (by omega))

open Polynomial in
lemma natDegree_diff_lt (n : ℕ) : (Np n - RHSp n).natDegree < 6 * (n + 1) := by
  refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
  refine max_lt (lt_of_le_of_lt (natDegree_Np_le n) (by omega)) ?_
  rw [RHSp]
  refine lt_of_le_of_lt
    (natDegree_sum_le_of_forall_le (Finset.range (n + 1)) (termP n)
      (fun j hj => natDegree_termP_le n j hj)) ?_
  omega

open Polynomial in
lemma main_poly_identity (n : ℕ) : Np n = RHSp n := by
  by_contra h
  have hne : Np n - RHSp n ≠ 0 := sub_ne_zero.2 h
  have hle := natDegree_le_of_dvd (Dprod_dvd n) hne
  rw [natDegree_Dprod] at hle
  exact absurd (lt_of_lt_of_le (natDegree_diff_lt n) hle) (lt_irrefl _)

/-- **The cleared partial-fraction identity.** For all `n` and all `k : ℚ`. -/
theorem pf_cleared (n : ℕ) (k : ℚ) :
    Nnum n k
      = ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.Icc 1 6,
          acoeff n i j * (k + (j : ℚ)) ^ (6 - i)
            * ∏ m ∈ (Finset.range (n + 1)).erase j, (k + (m : ℚ)) ^ 6 := by
  rw [Nnum_eq_eval, RHS_eq_eval, main_poly_identity]

end Cbcert.PartialFraction
