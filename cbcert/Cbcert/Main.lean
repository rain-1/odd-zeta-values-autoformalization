import Cbcert.Certificate
import Cbcert.PartialFraction
import Cbcert.Decay
import Cbcert.Integrality

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

/-! ## The residue map -/

/-- Residue of a rational modulo `p` (well-defined on `p`-integers). -/
def res (p : ℕ) (x : ℚ) : ZMod p := (x.num : ZMod p) * ((x.den : ZMod p))⁻¹

/-- **Bridge.** For `p`-integral `x`, `res p x = 0 ↔ (x = 0 ∨ 1 ≤ padicValRat p x)`.
The `x = 0` branch is essential: Mathlib sets `padicValRat p 0 = 0`, so the bare
`1 ≤ padicValRat` form fails at `0`. (This is why the frozen `padicValRat`-form main
theorems require nonvanishing — see `w_ne_zero` etc.) -/
lemma res_eq_zero_iff [Fact p.Prime] {x : ℚ} (hx : pInt p x) :
    res p x = 0 ↔ x = 0 ∨ 1 ≤ padicValRat p x := by
  sorry

/-- For nonzero `p`-integral `x`, `res p x = 0 → 1 ≤ padicValRat p x`. -/
lemma bridge [Fact p.Prime] {x : ℚ} (hx : pInt p x) (hne : x ≠ 0) (h0 : res p x = 0) :
    1 ≤ padicValRat p x := ((res_eq_zero_iff hx).mp h0).resolve_left hne

/-- `res` is additive on `p`-integers. -/
lemma res_add [Fact p.Prime] {x y : ℚ} (hx : pInt p x) (hy : pInt p y) :
    res p (x + y) = res p x + res p y := by
  sorry

/-- `res` is multiplicative on `p`-integers. -/
lemma res_mul [Fact p.Prime] {x y : ℚ} (hx : pInt p x) (hy : pInt p y) :
    res p (x * y) = res p x * res p y := by
  sorry

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

/-! ## `p`-integrality of the functionals (from Lemma C) -/

lemma acoeff_pInt (n i j : ℕ) (hp : p.Prime) (h1 : n < p) : pInt p (acoeff n i j) :=
  Integrality.integrality_a n i j p hp h1

lemma atcoeff_pInt (n i j : ℕ) (hp : p.Prime) (h1 : n < p) : pInt p (atcoeff n i j) :=
  Integrality.integrality_at n i j p hp h1

lemma Hh_pInt (i j : ℕ) (hp : p.Prime) (hj : j < p) : pInt p (Hh i j) :=
  Integrality.integrality_H i j p hp hj

lemma w_pInt (n : ℕ) (hp : p.Prime) (h1 : n < p) : pInt p (w n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact pInt_sum (fun j _ => acoeff_pInt n 3 j hp h1)

lemma wt_pInt (n : ℕ) (hp : p.Prime) (h1 : n < p) : pInt p (wt n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact pInt_sum (fun j _ => atcoeff_pInt n 3 j hp h1)

lemma vv_pInt (n : ℕ) (hp : p.Prime) (h1 : n < p) : pInt p (vv n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine pInt_sum (fun i _ => pInt_sum (fun j hj => pInt_mul (acoeff_pInt n i j hp h1) ?_))
  exact Hh_pInt i j hp (by have := Finset.mem_range.mp hj; omega)

lemma vt_pInt (n : ℕ) (hp : p.Prime) (h1 : n < p) : pInt p (vt n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine pInt_sum (fun i _ => pInt_sum (fun j hj => pInt_mul (atcoeff_pInt n i j hp h1) ?_))
  exact Hh_pInt i j hp (by have := Finset.mem_range.mp hj; omega)

lemma pn_pInt (n : ℕ) (hp : p.Prime) (h1 : n < p) : pInt p (pn n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact pInt_sub (pInt_mul (wt_pInt n hp h1) (vv_pInt n hp h1))
    (pInt_mul (w_pInt n hp h1) (vt_pInt n hp h1))

/-! ## The congruences `res p (w n) = 0`, `res p (wt n) = 0` (the heart) -/

/-- **(W).** `res p (w_n) = 0`: the `ZMod p` reordering of the certificate against
the decay relations. -/
theorem res_congruence_w (n : ℕ) (hp : p.Prime) (h1 : n < p) (h2 : p ≤ 2 * n)
    (h5 : 5 ≤ p) : res p (w n) = 0 := by
  sorry

/-- **(W̃).** `res p (w̃_n) = 0`. -/
theorem res_congruence_wt (n : ℕ) (hp : p.Prime) (h1 : n < p) (h2 : p ≤ 2 * n)
    (h5 : 5 ≤ p) : res p (wt n) = 0 := by
  sorry

/-! ## Nonvanishing (needed only for the `padicValRat`-form statements)

`padicValRat p 0 = 0` in Mathlib, so the frozen `1 ≤ padicValRat` statements are
only sound where the quantity is nonzero. The residue congruences
`res_congruence_w/wt` (the true content of "`p ∣ w_n`") need NO nonvanishing.
These three are a SEPARATE arithmetic obligation: numerically nonzero for all
`n ≤ 60` on the domain (checked in `worthiness/lemma_cb_explore.py`); a general-`n`
proof is open (relates to the linear forms being nontrivial). STAGED. -/

theorem w_ne_zero (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (h1 : n < p) (h2 : p ≤ 2 * n)
    (h5 : 5 ≤ p) : w n ≠ 0 := by sorry

theorem wt_ne_zero (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (h1 : n < p) (h2 : p ≤ 2 * n)
    (h5 : 5 ≤ p) : wt n ≠ 0 := by sorry

theorem pn_ne_zero (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (h1 : n < p) (h2 : p ≤ 2 * n)
    (h5 : 5 ≤ p) : pn n ≠ 0 := by sorry

/-! ## The main theorems (discharged) -/

/-- **(W) for `w`** — discharged. -/
theorem w_congruence' (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime)
    (h1 : n < p) (h2 : p ≤ 2 * n) (h5 : 5 ≤ p) : 1 ≤ padicValRat p (w n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact bridge (w_pInt n hp h1) (w_ne_zero n hn p h1 h2 h5)
    (res_congruence_w n hp h1 h2 h5)

/-- **(W) for `w̃`** — discharged. -/
theorem wtilde_congruence' (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime)
    (h1 : n < p) (h2 : p ≤ 2 * n) (h5 : 5 ≤ p) : 1 ≤ padicValRat p (wt n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact bridge (wt_pInt n hp h1) (wt_ne_zero n hn p h1 h2 h5)
    (res_congruence_wt n hp h1 h2 h5)

/-- **(CB₁)** — discharged. `res p (p_n) = res(w̃)·res(v) − res(w)·res(ṽ) = 0`. -/
theorem pn_valuation' (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime)
    (h1 : n < p) (h2 : p ≤ 2 * n) (h5 : 5 ≤ p) : 1 ≤ padicValRat p (pn n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine bridge (pn_pInt n hp h1) (pn_ne_zero n hn p h1 h2 h5) ?_
  have hz : res p (pn n)
      = res p (wt n) * res p (vv n) - res p (w n) * res p (vt n) := by
    rw [pn, res_sub (pInt_mul (wt_pInt n hp h1) (vv_pInt n hp h1))
        (pInt_mul (w_pInt n hp h1) (vt_pInt n hp h1)),
      res_mul (wt_pInt n hp h1) (vv_pInt n hp h1),
      res_mul (w_pInt n hp h1) (vt_pInt n hp h1)]
  rw [hz, res_congruence_w n hp h1 h2 h5, res_congruence_wt n hp h1 h2 h5]
  ring

end Cbcert.Main
