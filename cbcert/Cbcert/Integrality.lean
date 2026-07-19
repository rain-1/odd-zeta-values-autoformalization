import Cbcert.Defs

/-!
# Lemma C — p-integrality (Layer L3, part 1)

For a prime `p > n`, every `a_{i,j}`, `ã_{i,j}` (`j ≤ n`) and `H_j^{(i)}` (`j < p`)
is `p`-integral: `padicValRat p (·) ≥ 0` (`cb_certificate.tex`, §1 and the proof of
Prop. 1). This legitimises reduction mod `p` in the assembly.

## Status of the three theorems

* `integrality_H` — **fully proven, sorry-free** (true exactly as stated).
* `integrality_a`, `integrality_at` — the *literal universal statements are FALSE*;
  see the counterexample note on `integrality_a` below. They are proven **fully and
  sorry-free** on the region that actually occurs downstream, namely `j ≤ n ∧ p ≠ 2`
  (reusable cores `integrality_a_core` / `integrality_at_core`), and a single `sorry`
  remains for the genuinely-false complementary region, with the exact counterexample
  recorded. The manager should tighten the two signatures with hypotheses `j ≤ n` and
  `p ≠ 2` (equivalently `2 < p`; note the real domain has `p ≥ 5`), after which the
  cores discharge them with no `sorry`.

## The p-integrality mechanism (why the core is true)
`acoeff n i j = [t^{6-i}] B_j`, a product/sum (`Bseries`, a `List.foldl` of `tsMul`)
of: the integer `(n!)^4`; the linear factors `tsLin c` with `c = n/2 - j` (integer for
`p ≠ 2`) and `c = ±(integer)`; and reciprocals `tsInv6 (m - j)` with `m ∈ {0..n}\{j}`,
so `1 ≤ |m - j| ≤ n < p`, hence `p ∤ (m - j)`. Working with `padicNorm p (·) ≤ 1`
(⇔ `padicValRat ≥ 0`), every coefficient of every truncated series in the fold stays
`≤ 1`: integers and `1` have norm `≤ 1`, the pole reciprocals have norm exactly `1`,
and `tsMul`/`+` preserve `≤ 1` (multiplicativity + non-archimedean).

## Why the literal statements are false
* `j > n`: a pole difference `m - j` can be a multiple of `p` (denominator), e.g.
  `acoeff 1 5 2 = 9/128` with `p = 2` (`128 = 2^7`), `padicValRat 2 = -7 < 0`.
* `p = 2` with `n` odd: the `n/2 - j` factor contributes a `1/2`, e.g.
  `acoeff 1 5 0 = 9/2`, `padicValRat 2 = -1 < 0`. (`p = 2` forces `n ≤ 1`, and `n = 1`
  is odd, so this is the only `p = 2` failure; for `n ≥ 3` the least prime `> n` is odd.)
Both are outside the downstream usage (`j ∈ range (n+1)`, `p ≥ 5`).
-/

namespace Cbcert.Integrality

open Cbcert

variable {p : ℕ}

/-! ## Bridge: `padicNorm ≤ 1` ⇒ `padicValRat ≥ 0` -/

/-- A rational with `p`-adic norm `≤ 1` is a `p`-adic integer. -/
theorem padicValRat_nonneg_of_padicNorm_le_one [hp : Fact p.Prime] {q : ℚ}
    (h : padicNorm p q ≤ 1) : 0 ≤ padicValRat p q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [padicValRat.zero]
  · have hpq : padicNorm p q = (p : ℚ) ^ (-padicValRat p q) :=
      padicNorm.eq_zpow_of_nonzero hq
    rw [hpq] at h
    have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
    have := (zpow_le_one_iff_right₀ hp1).mp h
    omega

/-! ## `padicNorm` of powers and helper closure lemmas -/

theorem padicNorm_pow [Fact p.Prime] (q : ℚ) (k : ℕ) :
    padicNorm p (q ^ k) = padicNorm p q ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, padicNorm.mul, ih]

/-- A `foldl` of `acc + g x` starting from a `≤ 1` accumulator, with every `g x`
having norm `≤ 1`, stays `≤ 1`. This handles the Cauchy sum inside `tsMul`. -/
theorem foldl_add_le_one [Fact p.Prime] {β : Type*} (g : β → ℚ) :
    ∀ (l : List β) (acc : ℚ), padicNorm p acc ≤ 1 →
      (∀ x ∈ l, padicNorm p (g x) ≤ 1) →
      padicNorm p (l.foldl (fun a x => a + g x) acc) ≤ 1 := by
  intro l
  induction l with
  | nil => intro acc hacc _; simpa using hacc
  | cons x xs ih =>
    intro acc hacc hg
    simp only [List.foldl_cons]
    apply ih
    · calc padicNorm p (acc + g x)
          ≤ max (padicNorm p acc) (padicNorm p (g x)) := padicNorm.nonarchimedean
        _ ≤ 1 := max_le hacc (hg x List.mem_cons_self)
    · intro y hy; exact hg y (List.mem_cons_of_mem _ hy)

/-! A truncated series is `p`-integral if all its coefficients have norm `≤ 1`. -/

theorem tsMul_pn [Fact p.Prime] {a b : ℕ → ℚ}
    (ha : ∀ r, padicNorm p (a r) ≤ 1) (hb : ∀ r, padicNorm p (b r) ≤ 1) :
    ∀ r, padicNorm p (tsMul a b r) ≤ 1 := by
  intro r
  unfold tsMul
  apply foldl_add_le_one
  · simp [padicNorm.zero]
  · intro s _
    rw [padicNorm.mul]
    exact mul_le_one₀ (ha s) (padicNorm.nonneg _) (hb (r - s))

theorem tsConst_pn {c : ℚ} (hc : padicNorm p c ≤ 1) :
    ∀ r, padicNorm p (tsConst c r) ≤ 1 := by
  intro r; unfold tsConst
  split
  · exact hc
  · simp [padicNorm.zero]

theorem tsLin_pn {c : ℚ} (hc : padicNorm p c ≤ 1) :
    ∀ r, padicNorm p (tsLin c r) ≤ 1 := by
  intro r; unfold tsLin
  split
  · exact hc
  · split
    · simp
    · simp [padicNorm.zero]

/-- The order-5 expansion of `(c + t)^(-6)` is `p`-integral when `c` is a unit
(`padicNorm p c = 1`): the denominators `c^(6+r)` then have norm `1`, and the
numerators `(-1)^r · C(5+r,r)` are integers. -/
theorem tsInv6_pn [Fact p.Prime] {c : ℚ} (hc : padicNorm p c = 1) :
    ∀ r, padicNorm p (tsInv6 c r) ≤ 1 := by
  intro r
  unfold tsInv6
  rw [padicNorm.div, padicNorm_pow, hc, one_pow, div_one, padicNorm.mul]
  have h1 : padicNorm p ((-1 : ℚ) ^ r) ≤ 1 := by
    rw [padicNorm_pow]
    have : padicNorm p (-1 : ℚ) = 1 := by
      rw [show (-1 : ℚ) = -(1 : ℚ) by ring, padicNorm.neg, padicNorm.one]
    rw [this, one_pow]
  have h2 : padicNorm p ((Nat.choose (5 + r) r : ℚ)) ≤ 1 := padicNorm.of_nat _
  calc padicNorm p ((-1 : ℚ) ^ r) * padicNorm p ((Nat.choose (5 + r) r : ℚ))
      ≤ 1 * 1 := mul_le_mul h1 h2 (padicNorm.nonneg _) (by norm_num)
    _ = 1 := by ring

/-- General `foldl`-of-`tsMul`-style closure: if the accumulator is `p`-integral and
every step preserves `p`-integrality (for factors drawn from the list), the fold is
`p`-integral. Membership-restricted so the pole reciprocals can use `m ≤ n`. -/
theorem foldl_pn_gen [Fact p.Prime] {β : Type*} (g : (ℕ → ℚ) → β → (ℕ → ℚ)) :
    ∀ (l : List β) (init : ℕ → ℚ), (∀ r, padicNorm p (init r) ≤ 1) →
      (∀ (s : ℕ → ℚ) (x : β), x ∈ l → (∀ r, padicNorm p (s r) ≤ 1) →
        ∀ r, padicNorm p (g s x r) ≤ 1) →
      ∀ r, padicNorm p (l.foldl g init r) ≤ 1 := by
  intro l
  induction l with
  | nil => intro init hinit _ r; simpa using hinit r
  | cons x xs ih =>
    intro init hinit hg
    simp only [List.foldl_cons]
    exact ih (g init x) (hg init x List.mem_cons_self hinit)
      (fun s y hy hs => hg s y (List.mem_cons_of_mem _ hy) hs)

/-! ## The core: `Bseries` is `p`-integral for `j ≤ n < p`, `p ≠ 2` -/

/-- Every coefficient of `Bseries n j` has `p`-adic norm `≤ 1`, when `j ≤ n < p` and
`p ≠ 2`. -/
theorem Bseries_padicNorm_le_one [Fact p.Prime] (n j : ℕ) (hpn : n < p) (hjn : j ≤ n)
    (hp2 : p ≠ 2) : ∀ r, padicNorm p (Bseries n j r) ≤ 1 := by
  -- norm ≤ 1 for the constant `(n!)^4`
  have hFact : padicNorm p (((Nat.factorial n : ℚ)) ^ 4) ≤ 1 := by
    rw [padicNorm_pow]; exact pow_le_one₀ (padicNorm.nonneg _) (padicNorm.of_nat _)
  -- norm ≤ 1 for the half-integer linear factor `n/2 - j` (uses `p ≠ 2`)
  have hHalf : padicNorm p ((n : ℚ) / 2 - (j : ℚ)) ≤ 1 := by
    have e : (n : ℚ) / 2 - (j : ℚ) = (((n : ℤ) - 2 * (j : ℤ) : ℤ) : ℚ) / ((2 : ℤ) : ℚ) := by
      push_cast; ring
    rw [e, padicNorm.div]
    have h2 : padicNorm p ((2 : ℤ) : ℚ) = 1 := by
      rw [padicNorm.int_eq_one_iff]
      intro hd
      have hd2 : p ∣ 2 := by exact_mod_cast hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp hd2)
    rw [h2, div_one]; exact padicNorm.of_int _
  -- `init` factor
  have hinit : ∀ r, padicNorm p
      (tsMul (tsConst ((Nat.factorial n : ℚ) ^ 4)) (tsLin ((n : ℚ) / 2 - j)) r) ≤ 1 :=
    tsMul_pn (tsConst_pn hFact) (tsLin_pn hHalf)
  -- The two folds in `Bseries` are over the `Nat`-lists coerced into `List ℚ`, so the
  -- fold variable is a rational that is a `Nat`-cast; recover the `Nat` via `mem`.
  unfold Bseries
  -- outer fold: pole reciprocals `tsInv6 (m - j)`, each a unit
  refine foldl_pn_gen _ _ _ ?_ ?_
  · -- inner (middle) fold: linear factors with integer coefficients
    refine foldl_pn_gen _ _ _ hinit ?_
    intro s m hm hs
    simp only [List.bind_eq_flatMap, List.pure_def, List.mem_flatMap, List.mem_singleton,
      List.mem_range] at hm
    obtain ⟨m₀, _, rfl⟩ := hm
    have hA : padicNorm p (-(j : ℚ) - ((m₀ : ℚ) + 1)) ≤ 1 := by
      have : -(j : ℚ) - ((m₀ : ℚ) + 1) = -(((j + m₀ + 1 : ℕ) : ℚ)) := by push_cast; ring
      rw [this, padicNorm.neg]; exact padicNorm.of_nat _
    have hB : padicNorm p ((n : ℚ) + ((m₀ : ℚ) + 1) - j) ≤ 1 := by
      have : (n : ℚ) + ((m₀ : ℚ) + 1) - (j : ℚ)
          = (((n : ℤ) + (m₀ : ℤ) + 1 - (j : ℤ) : ℤ) : ℚ) := by push_cast; ring
      rw [this]; exact padicNorm.of_int _
    exact tsMul_pn (tsMul_pn hs (tsLin_pn hA)) (tsLin_pn hB)
  · intro s m hm hs
    apply tsMul_pn hs
    apply tsInv6_pn
    simp only [List.bind_eq_flatMap, List.pure_def, List.mem_flatMap, List.mem_singleton,
      List.mem_filter, List.mem_range, decide_eq_true_eq] at hm
    obtain ⟨m₀, ⟨hm₀lt, hmj⟩, rfl⟩ := hm
    -- `padicNorm p (m₀ - j) = 1` since `1 ≤ |m₀ - j| ≤ n < p`
    have hmn : m₀ ≤ n := by omega
    have ecast : ((m₀ : ℚ) - (j : ℚ)) = (((m₀ : ℤ) - (j : ℤ) : ℤ) : ℚ) := by push_cast; ring
    rw [ecast, padicNorm.int_eq_one_iff]
    intro hdvd
    have hne : ((m₀ : ℤ) - (j : ℤ)) ≠ 0 := by
      have : (m₀ : ℤ) ≠ (j : ℤ) := by exact_mod_cast hmj
      omega
    have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hne
    omega

/-! ## The three theorems -/

/-- **Lemma C core (base coefficients).** For `p` prime with `n < p`, `p ≠ 2`, and
`j ≤ n`, every `a_{i,j}` is `p`-integral. This is the reusable, sorry-free content. -/
theorem integrality_a_core (n i j : ℕ) (p : ℕ) (hp : p.Prime) (hpn : n < p)
    (hjn : j ≤ n) (hp2 : p ≠ 2) : 0 ≤ padicValRat p (acoeff n i j) := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply padicValRat_nonneg_of_padicNorm_le_one
  unfold acoeff
  split
  · exact Bseries_padicNorm_le_one n j hpn hjn hp2 (6 - i)
  · simp [padicNorm.zero]

/-- `padicNorm p (acoeff n i j) ≤ 1` on the core region, packaged for `atcoeff`. -/
theorem acoeff_padicNorm_le_one [Fact p.Prime] (n i j : ℕ) (hpn : n < p) (hjn : j ≤ n)
    (hp2 : p ≠ 2) : padicNorm p (acoeff n i j) ≤ 1 := by
  unfold acoeff
  split
  · exact Bseries_padicNorm_le_one n j hpn hjn hp2 (6 - i)
  · simp [padicNorm.zero]

/-- **Lemma C core (companion coefficients).** `ã_{i,j}` is `p`-integral on the core
region: it is an integer-coefficient combination of the `p`-integral `a`'s. -/
theorem integrality_at_core (n i j : ℕ) (p : ℕ) (hp : p.Prime) (hpn : n < p)
    (hjn : j ≤ n) (hp2 : p ≠ 2) : 0 ≤ padicValRat p (atcoeff n i j) := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply padicValRat_nonneg_of_padicNorm_le_one
  unfold atcoeff
  -- `j(n-j)·a_{i,j}`
  have t1 : padicNorm p ((j : ℚ) * ((n : ℚ) - j) * acoeff n i j) ≤ 1 := by
    rw [padicNorm.mul]
    refine mul_le_one₀ ?_ (padicNorm.nonneg _) (acoeff_padicNorm_le_one n i j hpn hjn hp2)
    have : (j : ℚ) * ((n : ℚ) - j) = (((j : ℤ) * ((n : ℤ) - (j : ℤ)) : ℤ) : ℚ) := by
      push_cast; ring
    rw [this]; exact padicNorm.of_int _
  -- `(2j-n)·a_{i+1,j}`
  have t2 : padicNorm p ((2 * (j : ℚ) - (n : ℚ)) * acoeff n (i + 1) j) ≤ 1 := by
    rw [padicNorm.mul]
    refine mul_le_one₀ ?_ (padicNorm.nonneg _)
      (acoeff_padicNorm_le_one n (i + 1) j hpn hjn hp2)
    have : (2 * (j : ℚ) - (n : ℚ)) = (((2 * (j : ℤ) - (n : ℤ)) : ℤ) : ℚ) := by push_cast; ring
    rw [this]; exact padicNorm.of_int _
  -- `a_{i+2,j}`
  have t3 : padicNorm p (acoeff n (i + 2) j) ≤ 1 :=
    acoeff_padicNorm_le_one n (i + 2) j hpn hjn hp2
  calc padicNorm p
        ((j : ℚ) * ((n : ℚ) - j) * acoeff n i j
          + (2 * (j : ℚ) - (n : ℚ)) * acoeff n (i + 1) j
          - acoeff n (i + 2) j)
      ≤ max (padicNorm p
          ((j : ℚ) * ((n : ℚ) - j) * acoeff n i j
            + (2 * (j : ℚ) - (n : ℚ)) * acoeff n (i + 1) j))
          (padicNorm p (acoeff n (i + 2) j)) := padicNorm.sub
    _ ≤ 1 := by
        refine max_le ?_ t3
        calc padicNorm p
              ((j : ℚ) * ((n : ℚ) - j) * acoeff n i j
                + (2 * (j : ℚ) - (n : ℚ)) * acoeff n (i + 1) j)
            ≤ max (padicNorm p ((j : ℚ) * ((n : ℚ) - j) * acoeff n i j))
                (padicNorm p ((2 * (j : ℚ) - (n : ℚ)) * acoeff n (i + 1) j)) :=
              padicNorm.nonarchimedean
          _ ≤ 1 := max_le t1 t2

/-! The public `integrality_a`/`integrality_at` were REMOVED: the literal universal
statements are FALSE (fail for `j > n` and for `p = 2`; e.g. `acoeff 1 5 2 = 9/128`).
The correct, proven results are `integrality_a_core`/`integrality_at_core` above
(hypotheses `j ≤ n`, `p ≠ 2`), which is what the assembly (`Main`) uses. -/

/-- **Lemma C (harmonic sums).** `H_j^{(i)}` is `p`-integral for `j < p`. This one is
TRUE exactly as stated and is proven sorry-free: the denominators are `m^i` with
`1 ≤ m ≤ j < p`, so `p ∤ m`. -/
theorem integrality_H (i j : ℕ) (p : ℕ) (hp : p.Prime) (hpj : j < p) :
    0 ≤ padicValRat p (Hh i j) := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply padicValRat_nonneg_of_padicNorm_le_one
  unfold Hh
  apply padicNorm.sum_le' _ (by norm_num : (0 : ℚ) ≤ 1)
  intro m hm
  rw [Finset.mem_Icc] at hm
  -- `padicNorm p (1 / m^i) = 1`
  rw [padicNorm.div, padicNorm_pow]
  have hmp : padicNorm p (m : ℚ) = 1 := by
    rw [padicNorm.nat_eq_one_iff]
    intro hdvd
    have : p ≤ m := Nat.le_of_dvd (by omega) hdvd
    omega
  rw [hmp, one_pow, padicNorm.one]; norm_num

end Cbcert.Integrality
