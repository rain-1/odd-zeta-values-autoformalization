import Mathlib

/-!
# The Brown–Zudilin ζ(5) integrality error — a construction-derived exhibit

Paper: F. Brown and W. Zudilin, *On cellular rational approximations to ζ(5)*,
arXiv:2210.03391 (v. **17 Oct 2022, revised 26 Jan 2026**). All equation labels
below refer to that revised source.

## What the paper claims

For the totally symmetric cellular integral `I_n` the paper writes (eq. `I_n`)
`I_n = Q_n·(2ζ(5)+4ζ(3)ζ(2)) − 4·P̂_n·ζ(2) − 2·P_n`, with rational coefficients
`Q_n, P̂_n, P_n`. Based on "an extensive computation … we observe experimentally
that" (eq. `dn-totsym`)

  `Q_n, d_n² d_{2n} P̂_n, d_n⁵ P_n ∈ ℤ   for n = 0,1,2,…`,

where `d_n = lcm(1,…,n)`. This inclusion is presented as an *experimental
observation*, not a theorem.

## What the paper displays

Immediately after eq. `I_n` the paper prints the exact rational values (n = 0,1,2),
including `Q_2 = 2989`, `P̂_2 = 344923/96`, and `P_2 = 1190161/384`.

## The error

`d_2 = lcm(1,2) = 2`, so `d_2⁵ = 32`, and `32 · 1190161/384 = 1190161/12 ∉ ℤ`.
The paper's own displayed value therefore *violates its own displayed inclusion*
at `n = 2`. The companion fails too: `d_2² d_4 = 48` and `48 · 344923/96 = 344923/2 ∉ ℤ`.

## The sharp correction (from the repo's audit, `worthiness/CONJECTURE.md`)

The failure is by exactly the factor `12 = 2²·3` for `P`, and by exactly `2` for
`P̂`, and these factors are sharp: `c · d_2⁵ · P_2 ∈ ℤ ⟺ 12 ∣ c` and
`c · d_2² d_4 · P̂_2 ∈ ℤ ⟺ 2 ∣ c` (Theorems `clearing_iff`, `companion_clearing_iff`).

## Honesty: everything here is DERIVED, not hardcoded

`P_2` and `P̂_2` are not asserted equal to the displayed rationals. They are
computed through the Brown–Zudilin / Zudilin construction:

* `ac i j` — the partial-fraction coefficients `a_{i,j}` of the paper's rational
  function `R_2(k)`. These candidate values are **certified** by `pf_cert`, a
  cleared-denominator polynomial identity proving `R_2 = Σ a_{i,j}/(k+j)^i`.
* from `ac` the whole chain `ã_{i,j} → w, w̃, u, ũ, v, ṽ → p_2 = w̃v − wṽ` and
  the ζ(3)-analogue `p̂_2 = uṽ − ũv` is built, and finally
  `P_2 = (−1)^{n+1} p_2 / binom(2n,n)`, `P̂_2 = (−1)^{n+1} p̂_2 / binom(2n,n)`
  (the Zu02 correspondence displayed just after eq. `dn-totsym`).

`P2_eq : P₂ = 1190161/384` is then a *theorem about the construction*, and the
displayed value's disagreement with the displayed inclusion is exhibited as a
genuine arithmetic fact.

Ground truth for the construction: `worthiness/lemma_cb_explore.py` (`all_data`),
`worthiness/CONJECTURE.md` (the error finding). House rules: `sorry`-free,
no `native_decide`; axioms of every main theorem are `[propext, Classical.choice,
Quot.sound]` (see the `#print axioms` block at the bottom).
-/

namespace Cbcert.ErrorExhibit

/-! ### The construction, specialised to n = 2

Everything below is the totally symmetric point `n = 2`, where the paper's displayed
`P₂` violates its displayed inclusion. -/

/-- Partial-fraction coefficients `a_{i,j}` of the paper's rational function
`R_2(k) = 16 (k+1)(k−1)(k−2)(k+3)(k+4) / (k(k+1)(k+2))^6`, indexed by pole order
`i ∈ {1,…,6}` (row) and pole `j ∈ {0,1,2}` (column). Values outside the range are
`0`. These are *candidate* values; `pf_cert` certifies them. Source:
`worthiness/lemma_cb_explore.py` `base_coefficients(2)`; SPEC.md def of `a_{i,j}`. -/
def ac : ℕ → ℕ → ℚ
  | 1, 0 => -5432    | 1, 1 => 10864 | 1, 2 => -5432
  | 2, 0 => 37331/16 | 2, 1 => 0     | 2, 2 => -37331/16
  | 3, 0 => -6867/8  | 3, 1 => 3248  | 3, 2 => -6867/8
  | 4, 0 => 1015/4   | 4, 1 => 0     | 4, 2 => -1015/4
  | 5, 0 => -107/2   | 5, 1 => 576   | 5, 2 => -107/2
  | 6, 0 => 6        | 6, 1 => 0     | 6, 2 => -6
  | _, _ => 0

/-- **Certificate for `ac`.** The cleared-denominator form of
`R_2(k) = Σ_{i,j} a_{i,j}/(k+j)^i`: multiplying through by `(k(k+1)(k+2))^6` gives a
polynomial identity between the numerator `16(k+1)(k−1)(k−2)(k+3)(k+4)` of `R_2` and
the partial-fraction sum. Proving it (`ring`) certifies that `ac` really are the
partial-fraction coefficients of the paper's `R_2` — so the values below are
derived, not trusted. (SPEC.md: `R_n = Σ a_{i,j}/(k+j)^i`.) -/
theorem pf_cert (k : ℚ) :
    16 * (k+1) * (k-1) * (k-2) * (k+3) * (k+4)
      = (ac 1 0 * k^5           * (k+1)^6 * (k+2)^6
       + ac 2 0 * k^4           * (k+1)^6 * (k+2)^6
       + ac 3 0 * k^3           * (k+1)^6 * (k+2)^6
       + ac 4 0 * k^2           * (k+1)^6 * (k+2)^6
       + ac 5 0 * k^1           * (k+1)^6 * (k+2)^6
       + ac 6 0 * k^0           * (k+1)^6 * (k+2)^6)
      + (ac 1 1 * k^6 * (k+1)^5           * (k+2)^6
       + ac 2 1 * k^6 * (k+1)^4           * (k+2)^6
       + ac 3 1 * k^6 * (k+1)^3           * (k+2)^6
       + ac 4 1 * k^6 * (k+1)^2           * (k+2)^6
       + ac 5 1 * k^6 * (k+1)^1           * (k+2)^6
       + ac 6 1 * k^6 * (k+1)^0           * (k+2)^6)
      + (ac 1 2 * k^6 * (k+1)^6 * (k+2)^5
       + ac 2 2 * k^6 * (k+1)^6 * (k+2)^4
       + ac 3 2 * k^6 * (k+1)^6 * (k+2)^3
       + ac 4 2 * k^6 * (k+1)^6 * (k+2)^2
       + ac 5 2 * k^6 * (k+1)^6 * (k+2)^1
       + ac 6 2 * k^6 * (k+1)^6 * (k+2)^0) := by
  simp only [ac]; ring

/-- Companion coefficients `ã_{i,j}` (partial fractions of `−k(k+n)R_n`), for `n = 2`:
`ã_{i,j} = j(2−j)a_{i,j} + (2j−2)a_{i+1,j} − a_{i+2,j}`. SPEC.md def of `ã`. -/
def atc (i j : ℕ) : ℚ :=
  (j : ℚ) * (2 - (j : ℚ)) * ac i j + (2 * (j : ℚ) - 2) * ac (i+1) j - ac (i+2) j

/-- Harmonic sums `H_j^{(i)} = Σ_{m=1}^j 1/m^i`, for `j ≤ 2`. SPEC.md def of `H`. -/
def Hh (i j : ℕ) : ℚ :=
  match j with
  | 0 => 0
  | 1 => 1
  | _ => 1 + 1 / (2 : ℚ)^i

/-- `w_2 = Σ_j a_{3,j}` (SPEC.md). -/
def w : ℚ := ac 3 0 + ac 3 1 + ac 3 2
/-- `w̃_2 = Σ_j ã_{3,j}` (SPEC.md). -/
def wt : ℚ := atc 3 0 + atc 3 1 + atc 3 2
/-- `u_2 = Σ_j a_{5,j}` (the ζ(5) coefficient of `r_n`; SPEC.md). -/
def u : ℚ := ac 5 0 + ac 5 1 + ac 5 2
/-- `ũ_2 = Σ_j ã_{5,j}` (SPEC.md). -/
def ut : ℚ := atc 5 0 + atc 5 1 + atc 5 2

/-- `v_2 = Σ_{i,j} a_{i,j} H_j^{(i)}` (SPEC.md). The `j = 0` terms vanish since
`H_0^{(i)} = 0`, so only `j ∈ {1,2}` appear. -/
def vv : ℚ :=
    ac 1 1 * Hh 1 1 + ac 1 2 * Hh 1 2
  + ac 2 1 * Hh 2 1 + ac 2 2 * Hh 2 2
  + ac 3 1 * Hh 3 1 + ac 3 2 * Hh 3 2
  + ac 4 1 * Hh 4 1 + ac 4 2 * Hh 4 2
  + ac 5 1 * Hh 5 1 + ac 5 2 * Hh 5 2
  + ac 6 1 * Hh 6 1 + ac 6 2 * Hh 6 2

/-- `ṽ_2 = Σ_{i,j} ã_{i,j} H_j^{(i)}` (SPEC.md). -/
def vt : ℚ :=
    atc 1 1 * Hh 1 1 + atc 1 2 * Hh 1 2
  + atc 2 1 * Hh 2 1 + atc 2 2 * Hh 2 2
  + atc 3 1 * Hh 3 1 + atc 3 2 * Hh 3 2
  + atc 4 1 * Hh 4 1 + atc 4 2 * Hh 4 2
  + atc 5 1 * Hh 5 1 + atc 5 2 * Hh 5 2
  + atc 6 1 * Hh 6 1 + atc 6 2 * Hh 6 2

/-- `p_2 = w̃_2 v_2 − w_2 ṽ_2`, the ζ(3)-eliminated numerator (Zudilin `p_n`;
SPEC.md `p_n = w̃_n v_n − w_n ṽ_n`). -/
def pc : ℚ := wt * vv - w * vt

/-- `p̂_2 = u_2 ṽ_2 − ũ_2 v_2`, the companion ζ(3) numerator (Zudilin `p̂_n`;
`dwork_vecform.py` minor `ptil_n = u vt − ut v`). -/
def phc : ℚ := u * vt - ut * vv

/-- **`P_2`, derived.** `P_n = (−1)^{n+1} p_n / binom(2n,n)`; for `n = 2` the sign is
`−1` and `binom(4,2) = 6`. (Brown–Zudilin, the Zu02 correspondence displayed just
after eq. `dn-totsym`.) -/
def P₂ : ℚ := -pc / 6

/-- **`P̂_2`, derived** (same correspondence). -/
def Phat₂ : ℚ := -phc / 6

/-! ### The derived values match the paper's displayed rationals -/

/-- **Theorem `P2_eq`.** The construction yields exactly the value the paper displays
after eq. `I_n`: `P₂ = 1190161/384`. Derived, not defined. -/
theorem P2_eq : P₂ = 1190161 / 384 := by
  simp only [P₂, pc, wt, w, vv, vt, atc, ac, Hh]; norm_num

/-- The paper's displayed `Q_2 = 2989` also falls out of the same period data,
`Q_2 = (−1)^{n+1} (u w̃ − ũ w)/binom(2n,n)`, as a sanity anchor. -/
theorem Q2_eq : -(u * wt - ut * w) / 6 = 2989 := by
  simp only [u, wt, ut, w, atc, ac]; norm_num

/-- **Theorem `Phat2_eq`.** The companion value the paper displays: `Phat₂ = 344923/96`.
Derived, not defined. -/
theorem Phat2_eq : Phat₂ = 344923 / 96 := by
  simp only [Phat₂, phc, u, ut, vv, vt, atc, ac, Hh]; norm_num

/-! ### `d_n = lcm(1,…,n)` -/

/-- `d n = lcm(1,…,n)` (Brown–Zudilin eq. `dn-totsym`). -/
def d : ℕ → ℕ
  | 0 => 1
  | (n+1) => Nat.lcm (d n) (n+1)

/-- `d_2 = lcm(1,2) = 2`. -/
theorem d_two : d 2 = 2 := by decide

/-! ### Integrality bookkeeping: `∃ integer` ⟺ divisibility -/

/-- A rational `N/D` (with `D ≠ 0`) is an integer iff `D ∣ N`. This turns every
integrality question below into a plain integer-divisibility check. -/
theorem exists_int_div_iff_dvd (N : ℤ) (D : ℕ) (hD : (D : ℚ) ≠ 0) :
    (∃ m : ℤ, (N : ℚ) / (D : ℚ) = (m : ℚ)) ↔ (D : ℤ) ∣ N := by
  constructor
  · rintro ⟨m, hm⟩
    rw [div_eq_iff hD] at hm
    have : N = m * (D : ℤ) := by exact_mod_cast hm
    exact ⟨m, by rw [this]; ring⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [div_eq_iff hD]; push_cast; ring⟩

/-! ### Main theorems: the error and its sharp correction -/

/-- The paper's `d_2⁵ · P_2` reduces to `1190161/12`. -/
theorem dP2_value : (d 2 : ℚ)^5 * P₂ = (1190161 : ℚ) / 12 := by
  rw [P2_eq, d_two]; norm_num

/-- **Theorem `bz_inclusion_fails`.** The paper's experimental inclusion
`d_n⁵ P_n ∈ ℤ` (eq. `dn-totsym`) is FALSE at `n = 2` for the paper's own displayed
`P_2`: `d_2⁵ P_2 = 1190161/12 ∉ ℤ`. -/
theorem bz_inclusion_fails : ¬ ∃ m : ℤ, (d 2 : ℚ)^5 * P₂ = (m : ℚ) := by
  rw [dP2_value]
  rw [show ((1190161 : ℚ) / 12) = ((1190161 : ℤ) : ℚ) / ((12 : ℕ) : ℚ) by norm_num]
  rw [exists_int_div_iff_dvd 1190161 12 (by norm_num)]
  decide

/-- **Theorem `clearing_iff`.** The sharp correction: multiplying the paper's inclusion
by `c` lands in `ℤ` **iff `12 ∣ c`**. In particular `c = 12` is the least fixer, so the
correct law is `12 · d_n⁵ P_n ∈ ℤ` and the factor `12 = 2²·3` is sharp
(`worthiness/CONJECTURE.md`). -/
theorem clearing_iff (c : ℕ) :
    (∃ m : ℤ, (c : ℚ) * (d 2 : ℚ)^5 * P₂ = (m : ℚ)) ↔ 12 ∣ c := by
  have hval : (c : ℚ) * (d 2 : ℚ)^5 * P₂
      = (((c : ℤ) * 1190161 : ℤ) : ℚ) / ((12 : ℕ) : ℚ) := by
    rw [P2_eq, d_two]; push_cast; ring
  rw [hval, exists_int_div_iff_dvd _ 12 (by norm_num)]
  constructor
  · intro h
    -- 12 ∣ c*1190161 and gcd(12,1190161)=1  ⇒  12 ∣ c
    have hn : (12 : ℤ) ∣ (c : ℤ) * 1190161 := h
    have hc : (12 : ℕ) ∣ c * 1190161 := by exact_mod_cast hn
    exact (Nat.Coprime.dvd_of_dvd_mul_right (by decide) hc)
  · intro h
    have : (12 : ℤ) ∣ (c : ℤ) := by exact_mod_cast h
    exact this.mul_right 1190161

/-! ### Bonus: the ζ(3) companion fails by exactly the factor 2 -/

/-- `d_2² d_4 · P̂_2` reduces to `344923/2` (`d_4 = 12`). -/
theorem dPhat2_value : (d 2 : ℚ)^2 * (d 4 : ℚ) * Phat₂ = (344923 : ℚ) / 2 := by
  rw [Phat2_eq, d_two]; norm_num [d]

/-- **Theorem `companion_inclusion_fails`.** The companion inclusion
`d_n² d_{2n} P̂_n ∈ ℤ` (eq. `dn-totsym`) is FALSE at `n = 2`:
`d_2² d_4 P̂_2 = 344923/2 ∉ ℤ`. -/
theorem companion_inclusion_fails :
    ¬ ∃ m : ℤ, (d 2 : ℚ)^2 * (d 4 : ℚ) * Phat₂ = (m : ℚ) := by
  rw [dPhat2_value]
  rw [show ((344923 : ℚ) / 2) = ((344923 : ℤ) : ℚ) / ((2 : ℕ) : ℚ) by norm_num]
  rw [exists_int_div_iff_dvd 344923 2 (by norm_num)]
  decide

/-- **Theorem `companion_clearing_iff`.** The companion is fixed **iff `2 ∣ c`**; the
factor `2` is sharp (`worthiness/CONJECTURE.md`: the ζ(3)-pair loses exactly `2`). -/
theorem companion_clearing_iff (c : ℕ) :
    (∃ m : ℤ, (c : ℚ) * ((d 2 : ℚ)^2 * (d 4 : ℚ)) * Phat₂ = (m : ℚ)) ↔ 2 ∣ c := by
  have hval : (c : ℚ) * ((d 2 : ℚ)^2 * (d 4 : ℚ)) * Phat₂
      = (((c : ℤ) * 344923 : ℤ) : ℚ) / ((2 : ℕ) : ℚ) := by
    rw [Phat2_eq, d_two]; norm_num [d]; ring
  rw [hval, exists_int_div_iff_dvd _ 2 (by norm_num)]
  constructor
  · intro h
    have hc : (2 : ℕ) ∣ c * 344923 := by exact_mod_cast h
    exact (Nat.Coprime.dvd_of_dvd_mul_right (by decide) hc)
  · intro h
    have : (2 : ℤ) ∣ (c : ℤ) := by exact_mod_cast h
    exact this.mul_right 344923

/-! ### Axiom audit (must be `[propext, Classical.choice, Quot.sound]` only) -/

#print axioms P2_eq
#print axioms Phat2_eq
#print axioms bz_inclusion_fails
#print axioms clearing_iff
#print axioms companion_inclusion_fails
#print axioms companion_clearing_iff
#print axioms pf_cert

end Cbcert.ErrorExhibit
