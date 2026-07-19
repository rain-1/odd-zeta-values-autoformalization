import Cbcert.Certificate
import Cbcert.Integrality
import Cbcert.Decay

/-!
# Assembly (Layer L3)

Combines Lemma A (`Decay`), Lemma B (`Certificate`, DONE) and Lemma C
(`Integrality`) into the proven main theorems `w_congruence'`,
`wtilde_congruence'`, `pn_valuation'` (the frozen statements in `Defs.lean` are
identical; these are the discharged versions).

Structure: a residue map `res p : ℚ → ZMod p` on `p`-integral rationals, the
`p`-integrality predicate `pInt` (= `0 ≤ padicValRat p ·`, matching `Integrality`),
and the bridge `pInt x → (res p x = 0 → 1 ≤ padicValRat p x)`. The heart is
`res_congruence_w/wt`: `res p (w n) = 0`, proved by the `ZMod p` reordering of
`Certificate.certificate` against `Decay.decay_*`.

See the module docstring history / `PROGRESS.md` for the full derivation.
-/

namespace Cbcert.Main

open Cbcert Finset

variable {p : ℕ}

/-! ## `p`-integrality (aligned with `Integrality`: `0 ≤ padicValRat p ·`) -/

/-- `x` is a `p`-adic integer. -/
def pInt (p : ℕ) (x : ℚ) : Prop := 0 ≤ padicValRat p x

lemma pInt_zero : pInt p 0 := by simp [pInt]

/-- Sum of `p`-integers is a `p`-integer. -/
lemma pInt_add [Fact p.Prime] {x y : ℚ} (hx : pInt p x) (hy : pInt p y) :
    pInt p (x + y) := by
  by_cases h : x + y = 0
  · simp [pInt, h]
  · exact le_trans (le_min hx hy) (padicValRat.min_le_padicValRat_add h)

lemma pInt_sum [Fact p.Prime] {ι : Type*} {s : Finset ι} {f : ι → ℚ}
    (h : ∀ i ∈ s, pInt p (f i)) : pInt p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using pInt_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact pInt_add (h a (Finset.mem_insert_self _ _))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma pInt_mul [Fact p.Prime] {x y : ℚ} (hx : pInt p x) (hy : pInt p y) :
    pInt p (x * y) := by
  by_cases hx0 : x = 0
  · simp [pInt, hx0]
  by_cases hy0 : y = 0
  · simp [pInt, hy0]
  · rw [pInt, padicValRat.mul hx0 hy0]; exact add_nonneg hx hy

lemma pInt_neg {x : ℚ} (hx : pInt p x) : pInt p (-x) := by
  simpa [pInt, padicValRat.neg] using hx

lemma pInt_sub [Fact p.Prime] {x y : ℚ} (hx : pInt p x) (hy : pInt p y) :
    pInt p (x - y) := by
  rw [sub_eq_add_neg]; exact pInt_add hx (pInt_neg hy)

lemma pInt_one : pInt p 1 := by simp [pInt]

lemma pInt_natCast (m : ℕ) : pInt p ((m : ℚ)) := zero_le_padicValRat_of_nat m

lemma pInt_intCast [Fact p.Prime] (m : ℤ) : pInt p ((m : ℚ)) := by
  rw [pInt, padicValRat.of_int, padicValInt]; positivity

lemma pInt_pow [Fact p.Prime] {x : ℚ} (hx : pInt p x) (k : ℕ) : pInt p (x ^ k) := by
  induction k with
  | zero => simpa using (pInt_one : pInt p 1)
  | succ k ih => rw [pow_succ]; exact pInt_mul ih hx

/-! ## The residue map -/

/-- Residue of a rational modulo `p` (well-defined on `p`-integers). -/
def res (p : ℕ) (x : ℚ) : ZMod p := (x.num : ZMod p) * ((x.den : ZMod p))⁻¹

/-- A `p`-integral rational has denominator coprime to `p`. -/
lemma pInt_den [Fact p.Prime] {x : ℚ} (hx : pInt p x) : ¬ (p : ℤ) ∣ (x.den : ℤ) := by
  intro hdvd
  have hpp : p.Prime := Fact.out
  have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
  have hnum : ¬ (p : ℤ) ∣ x.num := fun hn =>
    hp_int.not_unit ((Rat.isCoprime_num_den x).isUnit_of_dvd' hn hdvd)
  have hden0 : x.den ≠ 0 := x.den_nz
  have h1 : 1 ≤ padicValNat p x.den :=
    one_le_padicValNat_of_dvd hden0 (by exact_mod_cast hdvd)
  have h2 : padicValInt p x.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
  have : padicValRat p x < 0 := by rw [padicValRat_def]; omega
  exact absurd hx (by rw [pInt]; omega)

/-- Representation independence: `res p (a /. b) = ā · b̄⁻¹` for any `p`-coprime `b`. -/
lemma res_divInt [Fact p.Prime] (a b : ℤ) (hb0 : b ≠ 0) (hbp : ¬ (p : ℤ) ∣ b) :
    res p (Rat.divInt a b) = (a : ZMod p) * (b : ZMod p)⁻¹ := by
  set x : ℚ := Rat.divInt a b with hx
  have hden0 : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_nz
  have hcross : x.num * b = a * (x.den : ℤ) :=
    (Rat.divInt_eq_divInt_iff hden0 hb0).1 (by rw [Rat.num_divInt_den])
  have hxdp : ¬ (p : ℤ) ∣ (x.den : ℤ) := fun h => hbp (dvd_trans h (Rat.den_dvd a b))
  have hbz : (b : ZMod p) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hbp
  have hdz : (x.den : ZMod p) ≠ 0 := by
    rw [Ne, ← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hxdp
  have hcz : (x.num : ZMod p) * (b : ZMod p) = (a : ZMod p) * (x.den : ZMod p) := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) hcross; push_cast at this ⊢; exact this
  rw [res]; field_simp; linear_combination hcz

/-- **Bridge.** For `p`-integral `x`, `res p x = 0 ↔ (x = 0 ∨ 1 ≤ padicValRat p x)`.
The `x = 0` branch is essential: Mathlib sets `padicValRat p 0 = 0`, so the bare
`1 ≤ padicValRat` form fails at `0`. (This is why the frozen `padicValRat`-form main
theorems require nonvanishing — see `w_ne_zero` etc.) -/
lemma res_eq_zero_iff [Fact p.Prime] {x : ℚ} (hx : pInt p x) :
    res p x = 0 ↔ x = 0 ∨ 1 ≤ padicValRat p x := by
  have hxd := pInt_den hx
  have hdz : (x.den : ZMod p) ≠ 0 := by
    rw [Ne, ← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hxd
  have hden0 : ¬ p ∣ x.den := by exact_mod_cast hxd
  have hnum0den : padicValNat p x.den = 0 := padicValNat.eq_zero_of_not_dvd hden0
  have hres : res p x = 0 ↔ (p : ℤ) ∣ x.num := by
    rw [res, mul_eq_zero, inv_eq_zero]
    constructor
    · rintro (h | h)
      · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
      · exact absurd h hdz
    · intro h; exact Or.inl ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h)
  rw [hres]
  rcases eq_or_ne x 0 with hx0 | hx0
  · subst hx0; simp
  · have hv : (1 ≤ padicValRat p x) ↔ (p : ℤ) ∣ x.num := by
      rw [padicValRat_def, hnum0den, Nat.cast_zero, sub_zero]
      constructor
      · intro h
        by_contra hc
        rw [padicValInt.eq_zero_of_not_dvd hc] at h; omega
      · intro h
        have hna : x.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hx0)
        have hd : p ∣ x.num.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr h
        rw [padicValInt]
        exact_mod_cast one_le_padicValNat_of_dvd hna hd
    rw [hv]; exact ⟨fun h => Or.inr h, fun h => h.resolve_left hx0⟩

/-- For nonzero `p`-integral `x`, `res p x = 0 → 1 ≤ padicValRat p x`. -/
lemma bridge [Fact p.Prime] {x : ℚ} (hx : pInt p x) (hne : x ≠ 0) (h0 : res p x = 0) :
    1 ≤ padicValRat p x := ((res_eq_zero_iff hx).mp h0).resolve_left hne

/-- `res` is additive on `p`-integers. -/
lemma res_add [Fact p.Prime] {x y : ℚ} (hx : pInt p x) (hy : pInt p y) :
    res p (x + y) = res p x + res p y := by
  have hxd := pInt_den hx; have hyd := pInt_den hy
  have hxd0 : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_nz
  have hyd0 : (y.den : ℤ) ≠ 0 := by exact_mod_cast y.den_nz
  have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hbp : ¬ (p : ℤ) ∣ ((x.den : ℤ) * (y.den : ℤ)) := by
    intro h; rcases hp_int.dvd_or_dvd h with h | h; exact hxd h; exact hyd h
  have hsum : x + y = Rat.divInt (x.num * y.den + y.num * x.den) ((x.den : ℤ) * (y.den : ℤ)) := by
    conv_lhs => rw [← Rat.num_divInt_den x, ← Rat.num_divInt_den y]
    rw [Rat.divInt_add_divInt _ _ hxd0 hyd0]
  have hdxz : (x.den : ZMod p) ≠ 0 := by
    rw [Ne, ← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hxd
  have hdyz : (y.den : ZMod p) ≠ 0 := by
    rw [Ne, ← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hyd
  rw [hsum, res_divInt _ _ (mul_ne_zero hxd0 hyd0) hbp,
      show res p x = (x.num : ZMod p) * (x.den : ZMod p)⁻¹ from rfl,
      show res p y = (y.num : ZMod p) * (y.den : ZMod p)⁻¹ from rfl]
  push_cast; field_simp

/-- `res` is multiplicative on `p`-integers. -/
lemma res_mul [Fact p.Prime] {x y : ℚ} (hx : pInt p x) (hy : pInt p y) :
    res p (x * y) = res p x * res p y := by
  have hxd := pInt_den hx; have hyd := pInt_den hy
  have hxd0 : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_nz
  have hyd0 : (y.den : ℤ) ≠ 0 := by exact_mod_cast y.den_nz
  have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hbp : ¬ (p : ℤ) ∣ ((x.den : ℤ) * (y.den : ℤ)) := by
    intro h; rcases hp_int.dvd_or_dvd h with h | h; exact hxd h; exact hyd h
  have hprod : x * y = Rat.divInt (x.num * y.num) ((x.den : ℤ) * (y.den : ℤ)) := by
    conv_lhs => rw [← Rat.num_divInt_den x, ← Rat.num_divInt_den y]
    rw [Rat.divInt_mul_divInt]
  have hdxz : (x.den : ZMod p) ≠ 0 := by
    rw [Ne, ← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hxd
  have hdyz : (y.den : ZMod p) ≠ 0 := by
    rw [Ne, ← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hyd
  rw [hprod, res_divInt _ _ (mul_ne_zero hxd0 hyd0) hbp,
      show res p x = (x.num : ZMod p) * (x.den : ZMod p)⁻¹ from rfl,
      show res p y = (y.num : ZMod p) * (y.den : ZMod p)⁻¹ from rfl]
  push_cast; field_simp

lemma res_neg {x : ℚ} : res p (-x) = - res p x := by
  simp [res, Rat.neg_num, Rat.neg_den]

lemma res_sub [Fact p.Prime] {x y : ℚ} (hx : pInt p x) (hy : pInt p y) :
    res p (x - y) = res p x - res p y := by
  rw [sub_eq_add_neg, res_add hx (pInt_neg hy), res_neg, ← sub_eq_add_neg]

lemma res_sum [Fact p.Prime] {ι : Type*} {s : Finset ι} {f : ι → ℚ}
    (h : ∀ i ∈ s, pInt p (f i)) : res p (∑ i ∈ s, f i) = ∑ i ∈ s, res p (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [res]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        res_add (h a (Finset.mem_insert_self _ _))
          (pInt_sum (fun i hi => h i (Finset.mem_insert_of_mem hi))),
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]

lemma res_one : res p 1 = 1 := by simp [res]

lemma res_intCast [Fact p.Prime] (m : ℤ) : res p ((m : ℚ)) = (m : ZMod p) := by
  have hp1 : ¬ (p : ℤ) ∣ 1 := by
    intro h
    have h2 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h
    have hp2 : p ≤ 1 := by exact_mod_cast h2
    have := (Fact.out : p.Prime).one_lt; omega
  rw [Rat.intCast_eq_divInt, res_divInt m 1 one_ne_zero hp1]; simp

lemma res_pow [Fact p.Prime] {x : ℚ} (hx : pInt p x) (k : ℕ) :
    res p (x ^ k) = (res p x) ^ k := by
  induction k with
  | zero => simpa using res_one
  | succ k ih => rw [pow_succ, pow_succ, res_mul (pInt_pow hx k) hx, ih]

/-! ## `p`-integrality of the functionals (from Lemma C) -/

-- Lemma C is TRUE only on the core region `j ≤ n`, `p ≠ 2` (Worker C: the public
-- `integrality_a/at` are false as stated; the `_core` versions are proven). Both
-- hold in our use: `j ∈ range (n+1) ⇒ j ≤ n`, and `5 ≤ p ⇒ p ≠ 2`.
lemma acoeff_pInt (n i j : ℕ) (hp : p.Prime) (h1 : n < p) (hjn : j ≤ n) (hp2 : p ≠ 2) :
    pInt p (acoeff n i j) :=
  Integrality.integrality_a_core n i j p hp h1 hjn hp2

lemma atcoeff_pInt (n i j : ℕ) (hp : p.Prime) (h1 : n < p) (hjn : j ≤ n) (hp2 : p ≠ 2) :
    pInt p (atcoeff n i j) :=
  Integrality.integrality_at_core n i j p hp h1 hjn hp2

lemma Hh_pInt (i j : ℕ) (hp : p.Prime) (hj : j < p) : pInt p (Hh i j) :=
  Integrality.integrality_H i j p hp hj

lemma w_pInt (n : ℕ) (hp : p.Prime) (h1 : n < p) (hp2 : p ≠ 2) : pInt p (w n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact pInt_sum (fun j hj => acoeff_pInt n 3 j hp h1
    (by have := Finset.mem_range.mp hj; omega) hp2)

lemma wt_pInt (n : ℕ) (hp : p.Prime) (h1 : n < p) (hp2 : p ≠ 2) : pInt p (wt n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact pInt_sum (fun j hj => atcoeff_pInt n 3 j hp h1
    (by have := Finset.mem_range.mp hj; omega) hp2)

lemma vv_pInt (n : ℕ) (hp : p.Prime) (h1 : n < p) (hp2 : p ≠ 2) : pInt p (vv n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine pInt_sum (fun i _ => pInt_sum (fun j hj =>
    pInt_mul (acoeff_pInt n i j hp h1 (by have := Finset.mem_range.mp hj; omega) hp2) ?_))
  exact Hh_pInt i j hp (by have := Finset.mem_range.mp hj; omega)

lemma vt_pInt (n : ℕ) (hp : p.Prime) (h1 : n < p) (hp2 : p ≠ 2) : pInt p (vt n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine pInt_sum (fun i _ => pInt_sum (fun j hj =>
    pInt_mul (atcoeff_pInt n i j hp h1 (by have := Finset.mem_range.mp hj; omega) hp2) ?_))
  exact Hh_pInt i j hp (by have := Finset.mem_range.mp hj; omega)

lemma pn_pInt (n : ℕ) (hp : p.Prime) (h1 : n < p) (hp2 : p ≠ 2) : pInt p (pn n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact pInt_sub (pInt_mul (wt_pInt n hp h1 hp2) (vv_pInt n hp h1 hp2))
    (pInt_mul (w_pInt n hp h1 hp2) (vt_pInt n hp h1 hp2))

/-! ## The `ZMod p` reordering (the heart) — coefficient-agnostic -/

lemma res_natCast [Fact p.Prime] (m : ℕ) : res p ((m : ℚ)) = (m : ZMod p) := by
  have : ((m : ℚ)) = ((m : ℤ) : ℚ) := by push_cast; ring
  rw [this, res_intCast]; push_cast; ring

/-- `res` distributes over `E_M`: `res(E_M(b)) = Σ_i (Cneg i (M-i)) Σ_j j^{M-i} res(b_{i,j})`. -/
lemma res_EM_gen [Fact p.Prime] (n M : ℕ) (b : ℕ → ℕ → ℚ)
    (hb : ∀ i, ∀ j ∈ Finset.range (n + 1), pInt p (b i j)) :
    res p (EM n M b) = ∑ i ∈ Finset.Icc 1 (min 6 M),
      (Cneg i (M - i) : ZMod p) * ∑ j ∈ Finset.range (n + 1),
        (j : ZMod p) ^ (M - i) * res p (b i j) := by
  have hcoef : ∀ i ∈ Finset.Icc 1 (min 6 M), ∀ j ∈ Finset.range (n + 1),
      pInt p ((j : ℚ) ^ (M - i) * b i j) := fun i _ j hj =>
    pInt_mul (pInt_pow (pInt_natCast _) _) (hb i j hj)
  rw [EM, res_sum (fun i hi => pInt_mul (pInt_intCast _) (pInt_sum (hcoef i hi)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [res_mul (pInt_intCast _) (pInt_sum (hcoef i hi)), res_intCast, res_sum (hcoef i hi)]
  refine congrArg _ (Finset.sum_congr rfl (fun j hj => ?_))
  rw [res_mul (pInt_pow (pInt_natCast _) _) (hb i j hj), res_pow (pInt_natCast _), res_natCast]

/-- Per-`j` collapse: the three-term certificate sum (over `i`) equals `r 3`. -/
lemma cert_sum_j [Fact p.Prime] (h5 : 5 ≤ p) (j : ℕ) (r : ℕ → ZMod p) :
    (∑ i ∈ Finset.Icc 1 3, (Cneg i (3 - i) : ZMod p) * (j : ZMod p) ^ (3 - i) * r i)
    + (∑ i ∈ Finset.Icc 1 6,
        (-2 : ZMod p) * (Cneg i (p + 2 - i) : ZMod p) * (j : ZMod p) ^ (p + 2 - i) * r i)
    + (∑ i ∈ Finset.Icc 1 6,
        (Cneg i (2 * p + 1 - i) : ZMod p) * (j : ZMod p) ^ (2 * p + 1 - i) * r i)
    = r 3 := by
  set x : ZMod p := (j : ZMod p)
  have hfirst : (∑ i ∈ Finset.Icc 1 3, (Cneg i (3 - i) : ZMod p) * x ^ (3 - i) * r i)
      = ∑ i ∈ Finset.Icc 1 6,
          (if i ≤ 3 then (Cneg i (3 - i) : ZMod p) * x ^ (3 - i) else 0) * r i := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 6) (· ≤ 3)]
    have h2 : ∑ i ∈ (Finset.Icc 1 6).filter (¬ · ≤ 3),
        (if i ≤ 3 then (Cneg i (3 - i) : ZMod p) * x ^ (3 - i) else 0) * r i = 0 := by
      apply Finset.sum_eq_zero; intro i hi
      rw [Finset.mem_filter] at hi; rw [if_neg hi.2]; ring
    rw [h2, add_zero]
    apply Finset.sum_congr
    · ext i; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    · intro i hi; rw [Finset.mem_filter] at hi; rw [if_pos hi.2]
  rw [hfirst, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [show r 3 = ∑ i ∈ Finset.Icc 1 6, (if i = 3 then (1 : ZMod p) else 0) * r i by
      rw [Finset.sum_eq_single 3]
      · rw [if_pos rfl, one_mul]
      · intro i _ hi; rw [if_neg hi, zero_mul]
      · intro h; exact absurd (by simp : (3 : ℕ) ∈ Finset.Icc 1 6) h]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  have := Certificate.certificate h5 hi.1 hi.2 x
  rw [← this]; ring

/-- **The reordering, coefficient-agnostic.** Given decay `E_M(b)=0` for the three
certificate indices, `res p (Σ_j b_{3,j}) = 0`. Works for `acoeff` (⇒ `w`) and
`atcoeff` (⇒ `w̃`) alike — the certificate is the same. -/
theorem res_congruence_of [Fact p.Prime] (n : ℕ) (h2 : p ≤ 2 * n) (h5 : 5 ≤ p)
    (b : ℕ → ℕ → ℚ) (hb : ∀ i, ∀ j ∈ Finset.range (n + 1), pInt p (b i j))
    (hd3 : EM n 3 b = 0) (hd2 : EM n (p + 2) b = 0) (hd1 : EM n (2 * p + 1) b = 0) :
    res p (∑ j ∈ Finset.range (n + 1), b 3 j) = 0 := by
  rw [res_sum (fun j hj => hb 3 j hj)]
  have hT0 : (1 : ZMod p) * res p (EM n 3 b) + (-2) * res p (EM n (p + 2) b)
      + (1 : ZMod p) * res p (EM n (2 * p + 1) b) = 0 := by
    rw [hd3, hd2, hd1]; simp [res]
  rw [← hT0, res_EM_gen n 3 b hb, res_EM_gen n (p + 2) b hb, res_EM_gen n (2 * p + 1) b hb,
      show min 6 3 = 3 by norm_num, show min 6 (p + 2) = 6 by omega,
      show min 6 (2 * p + 1) = 6 by omega, one_mul, one_mul]
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm (s := Finset.Icc 1 3), Finset.sum_comm (s := Finset.Icc 1 6),
      Finset.sum_comm (s := Finset.Icc 1 6), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact (cert_sum_j h5 j (fun i => res p (b i j))).symm

/-- **(W).** `res p (w_n) = 0`. Reordering DONE (via `res_congruence_of`); the three
`EM n M (acoeff n) = 0` obligations are exactly `Decay.decay_a` (Lemma A, Worker A2,
in flight) — the ONLY remaining gap here. Ranges `3, p+2, 2p+1 ≤ 4n+4` (as `p ≤ 2n`). -/
theorem res_congruence_w (n : ℕ) (hp : p.Prime) (h1 : n < p) (h2 : p ≤ 2 * n)
    (h5 : 5 ≤ p) : res p (w n) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  rw [w]
  refine res_congruence_of n h2 h5 (acoeff n)
    (fun i j hj => acoeff_pInt n i j hp h1 (by have := Finset.mem_range.mp hj; omega) hp2)
    (Decay.decay_a n 3 (by omega) (by omega))
    (Decay.decay_a n (p + 2) (by omega) (by omega))
    (Decay.decay_a n (2 * p + 1) (by omega) (by omega))

/-- **(W̃).** `res p (w̃_n) = 0`. Same reordering; the three obligations are
`Decay.decay_at` (range `≤ 4n+2`; `2p+1 ≤ 4n+1 ≤ 4n+2` as `p ≤ 2n`). -/
theorem res_congruence_wt (n : ℕ) (hp : p.Prime) (h1 : n < p) (h2 : p ≤ 2 * n)
    (h5 : 5 ≤ p) : res p (wt n) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  rw [wt]
  refine res_congruence_of n h2 h5 (atcoeff n)
    (fun i j hj => atcoeff_pInt n i j hp h1 (by have := Finset.mem_range.mp hj; omega) hp2)
    (Decay.decay_at n 3 (by omega) (by omega))
    (Decay.decay_at n (p + 2) (by omega) (by omega))
    (Decay.decay_at n (2 * p + 1) (by omega) (by omega))

/-- **(CB₁), residue form — fully proven.** `res p (p_n) = 0`, i.e. `p ∣ p_n`.
`p_n = w̃_n v_n − w_n ṽ_n`, `v_n, ṽ_n` are `p`-integral (Lemma C) and `res(w_n)=res(w̃_n)=0`
(the (W) congruences). Needs NO nonvanishing. Standard axioms only. -/
theorem res_congruence_pn (n : ℕ) (hp : p.Prime) (h1 : n < p) (h2 : p ≤ 2 * n)
    (h5 : 5 ≤ p) : res p (pn n) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  rw [pn, res_sub (pInt_mul (wt_pInt n hp h1 hp2) (vv_pInt n hp h1 hp2))
        (pInt_mul (w_pInt n hp h1 hp2) (vt_pInt n hp h1 hp2)),
      res_mul (wt_pInt n hp h1 hp2) (vv_pInt n hp h1 hp2),
      res_mul (w_pInt n hp h1 hp2) (vt_pInt n hp h1 hp2),
      res_congruence_w n hp h1 h2 h5, res_congruence_wt n hp h1 h2 h5]
  ring

/-! ## The main theorems — canonical, faithful, sorry-free

Faithful `padicValRat` renderings of "`p` divides", handling the `padicValRat p 0 = 0`
convention with an explicit `= 0` disjunct. Each is immediate from `res_eq_zero_iff`
(`p`-integrality, Lemma C) applied to the corresponding `res_congruence_*`. No
nonvanishing needed; standard axioms only. (The pure `1 ≤ padicValRat` form would
additionally require `w_n, w̃_n, p_n ≠ 0` — an explicitly-OPEN mini-campaign, see
`PROGRESS.md`; the residue forms `res_congruence_*` are the complete result.) -/

/-- **(W) for `w`.** `p ∣ w_n`: for every prime `n < p ≤ 2n`, `p ≥ 5`. -/
theorem w_congruence (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime)
    (h1 : n < p) (h2 : p ≤ 2 * n) (h5 : 5 ≤ p) : w n = 0 ∨ 1 ≤ padicValRat p (w n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact (res_eq_zero_iff (w_pInt n hp h1 (by omega))).mp (res_congruence_w n hp h1 h2 h5)

/-- **(W) for `w̃`.** `p ∣ w̃_n`. -/
theorem wtilde_congruence (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime)
    (h1 : n < p) (h2 : p ≤ 2 * n) (h5 : 5 ≤ p) : wt n = 0 ∨ 1 ≤ padicValRat p (wt n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact (res_eq_zero_iff (wt_pInt n hp h1 (by omega))).mp (res_congruence_wt n hp h1 h2 h5)

/-- **(CB₁).** `p ∣ p_n` — the central-binomial cancellation on the clean interval. -/
theorem pn_valuation (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime)
    (h1 : n < p) (h2 : p ≤ 2 * n) (h5 : 5 ≤ p) : pn n = 0 ∨ 1 ≤ padicValRat p (pn n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  exact (res_eq_zero_iff (pn_pInt n hp h1 hp2)).mp (res_congruence_pn n hp h1 h2 h5)

end Cbcert.Main
