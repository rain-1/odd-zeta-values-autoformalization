/-
Piece 2 of Lemma 4: the termwise ratio c/ĉ on the window.
Owner file — only `term_ratio_on_window` (and its private helpers) lives here.
Key available input: `centralBinom_rate` in Basic.lean.
-/
import Zeta5Odd.Basic

open Filter Finset
open scoped Nat Topology

namespace Zeta5Odd

/-! ### Product-of-odds identity (for the `chat` half-integer product)

`∏_{j<N} (2(m+j)+1) · (2m)! · 2^N · (m+N)! = (2m+2N)! · m!`.
Splitting `(2m+2N)!/(2m)!` into its odd part (the product) and even part
(`2^N · (m+N)!/m!`). Proved by induction on `N`. -/
private lemma prod_odd_cleared (m : ℕ) : ∀ N : ℕ,
    (∏ j ∈ range N, (2 * (m + j) + 1)) * (2 * m)! * 2 ^ N * (m + N)!
      = (2 * m + 2 * N)! * m ! := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    have hf1 : (m + (N + 1))! = (m + N + 1) * (m + N)! := by
      rw [show m + (N + 1) = (m + N) + 1 from rfl, Nat.factorial_succ]
    have hf2 : (2 * m + 2 * (N + 1))! = (2 * m + 2 * N + 2) * (2 * m + 2 * N + 1) * (2 * m + 2 * N)! := by
      rw [show 2 * m + 2 * (N + 1) = (2 * m + 2 * N + 1) + 1 from by ring, Nat.factorial_succ,
        show 2 * m + 2 * N + 1 = (2 * m + 2 * N) + 1 from rfl, Nat.factorial_succ]
      ring
    rw [Finset.prod_range_succ, pow_succ, hf1, hf2,
      show (∏ j ∈ range N, (2 * (m + j) + 1)) * (2 * (m + N) + 1) * (2 * m)! * (2 ^ N * 2)
            * ((m + N + 1) * (m + N)!)
          = ((∏ j ∈ range N, (2 * (m + j) + 1)) * (2 * m)! * 2 ^ N * (m + N)!)
            * ((2 * (m + N) + 1) * 2 * (m + N + 1)) from by ring, ih]
    ring

/-! ### The exact term-ratio identity (paper eq. (e10))

`c/ĉ = (6n+2k+2)/(2k+1) · (2^{-2(n+1)} · C(4n+2k+2,2n+k+1)/C(2n+2k,n+k))^{2q}`,
where the two binomials are the central binomials `centralBinom (2n+k+1)` and
`centralBinom (n+k)`.  Proved in two steps: a factorial/product ratio form, then
the conversion of the half-integer product to central binomials. -/

/-- Step 1: the ratio in factorial/product form.  Each of `c` and `chat` is
factored as `base ^ (2q) · rational`; taking the ratio combines the two `2q`-th
powers into a single grouped power (via `← div_pow`), which avoids leaving an
uncancelled `a ^ (2q) · (a⁻¹) ^ (2q)` residue. -/
private lemma ratio_prod_form (q n k : ℕ) :
    c q n k / chat q n k
      = ((6 * n + 2 * k + 2 : ℝ) / (2 * k + 1))
        * ((((n + k)! : ℝ) * (∏ j ∈ range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ)))
            / (((2 * n + k + 1)! : ℝ) * 2 ^ (n + 1))) ^ (2 * q) := by
  set P : ℝ := ∏ j ∈ range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ) with hP
  have pP : (0:ℝ) < P := by
    rw [hP]; apply prod_pos; intro j _; exact_mod_cast Nat.succ_pos _
  have pX : (0:ℝ) < (n ! : ℝ) ^ (2 * q - 6) := by positivity
  have p2k1 : (0:ℝ) < ((2 * k + 1)! : ℝ) := by exact_mod_cast (2*k+1).factorial_pos
  have p2k : (0:ℝ) < ((2 * k)! : ℝ) := by exact_mod_cast (2*k).factorial_pos
  have p6b : (0:ℝ) < ((6 * n + 2 * k + 1)! : ℝ) := by exact_mod_cast (6*n+2*k+1).factorial_pos
  have p2nk1 : (0:ℝ) < ((2 * n + k + 1)! : ℝ) := by exact_mod_cast (2*n+k+1).factorial_pos
  have hfac_a : ((6 * n + 2 * k + 2)! : ℝ) = (6 * n + 2 * k + 2 : ℝ) * ((6 * n + 2 * k + 1)! : ℝ) := by
    rw [show 6 * n + 2 * k + 2 = (6 * n + 2 * k + 1) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
  have hfac_b : ((2 * k + 1)! : ℝ) = (2 * k + 1 : ℝ) * ((2 * k)! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  -- Factor `c` and `chat`.
  have hcfac : c q n k
      = (((n + k)! : ℝ) / ((2 * n + k + 1)! : ℝ)) ^ (2 * q)
        * ((n ! : ℝ) ^ (2 * q - 6) * ((6 * n + 2 * k + 2)! : ℝ) / (2 * ((2 * k + 1)! : ℝ))) := by
    unfold c; rw [div_pow]; field_simp
  have hchatfac : chat q n k
      = ((2:ℝ) ^ (n + 1) / P) ^ (2 * q)
        * ((2:ℝ) ^ (6 * n) * (n ! : ℝ) ^ (2 * q - 6) * ((6 * n + 2 * k + 1)! : ℝ)
            / (((2 * k)! : ℝ) * 2 ^ (6 * n + 1))) := by
    unfold chat
    rw [← hP, show (P / (2:ℝ) ^ (n + 1)) = ((2:ℝ) ^ (n + 1) / P)⁻¹ from (inv_div _ _).symm,
      inv_pow, div_inv_eq_mul]
    ring
  rw [hcfac, hchatfac, mul_div_mul_comm, ← div_pow]
  rw [show (((n + k)! : ℝ) / ((2 * n + k + 1)! : ℝ)) / ((2:ℝ) ^ (n + 1) / P)
        = (((n + k)! : ℝ) * P) / (((2 * n + k + 1)! : ℝ) * 2 ^ (n + 1)) from by
      field_simp]
  rw [show ((n ! : ℝ) ^ (2 * q - 6) * ((6 * n + 2 * k + 2)! : ℝ) / (2 * ((2 * k + 1)! : ℝ)))
          / ((2:ℝ) ^ (6 * n) * (n ! : ℝ) ^ (2 * q - 6) * ((6 * n + 2 * k + 1)! : ℝ)
              / (((2 * k)! : ℝ) * 2 ^ (6 * n + 1)))
        = (6 * n + 2 * k + 2 : ℝ) / (2 * k + 1) from by
      rw [hfac_a, hfac_b]; field_simp; ring]
  ring

/-- Step 2: the half-integer product bracket equals the central-binomial ratio. -/
private lemma bracket_centralBinom (n k : ℕ) :
    (((n + k)! : ℝ) * (∏ j ∈ range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ)))
        / (((2 * n + k + 1)! : ℝ) * 2 ^ (n + 1))
      = (Nat.centralBinom (2 * n + k + 1) : ℝ) / (Nat.centralBinom (n + k) : ℝ)
          / 2 ^ (2 * (n + 1)) := by
  -- central binomial factorial relation `C(M)·(M!)² = (2M)!`
  have hcbrel : ∀ M : ℕ, (Nat.centralBinom M : ℝ) * ((M ! : ℝ) * (M ! : ℝ)) = ((2 * M)! : ℝ) := by
    intro M
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_mul_of_pos_left M (by norm_num : 0 < 2))
    rw [show 2 * M - M = M by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose]
    have h2 : ((2 * M).choose M * M ! * M ! : ℕ) = ((2 * M)! : ℕ) := h
    push_cast [← h2]; ring
  -- Nat product identity from `prod_odd_cleared`
  have hProd : (∏ j ∈ range (n + 1), (2 * (n + k + j) + 1)) * (2 * (n + k))! * 2 ^ (n + 1)
        * (2 * n + k + 1)! = (4 * n + 2 * k + 2)! * (n + k)! := by
    have h := prod_odd_cleared (n + k) (n + 1)
    rw [show n + k + (n + 1) = 2 * n + k + 1 from by ring,
        show 2 * (n + k) + 2 * (n + 1) = 4 * n + 2 * k + 2 from by ring] at h
    exact h
  -- cast product to ℝ
  have hPcast : (∏ j ∈ range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ))
      = ((∏ j ∈ range (n + 1), (2 * (n + k + j) + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
  have hProdR : (∏ j ∈ range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ)) * ((2 * (n + k))! : ℝ)
        * 2 ^ (n + 1) * ((2 * n + k + 1)! : ℝ) = ((4 * n + 2 * k + 2)! : ℝ) * ((n + k)! : ℝ) := by
    rw [hPcast]; exact_mod_cast hProd
  -- central-binomial identities at the two arguments
  have hcbA : (Nat.centralBinom (2 * n + k + 1) : ℝ) * (((2 * n + k + 1)! : ℝ) * ((2 * n + k + 1)! : ℝ))
      = ((4 * n + 2 * k + 2)! : ℝ) := by
    have := hcbrel (2 * n + k + 1)
    rwa [show 2 * (2 * n + k + 1) = 4 * n + 2 * k + 2 from by ring] at this
  have hcbB : (Nat.centralBinom (n + k) : ℝ) * (((n + k)! : ℝ) * ((n + k)! : ℝ))
      = ((2 * (n + k))! : ℝ) := hcbrel (n + k)
  -- positivity / nonzero facts
  have pnk : (0:ℝ) < ((n + k)! : ℝ) := by exact_mod_cast (n+k).factorial_pos
  have p2nk1 : (0:ℝ) < ((2 * n + k + 1)! : ℝ) := by exact_mod_cast (2*n+k+1).factorial_pos
  have p2nk : (0:ℝ) < ((2 * (n + k))! : ℝ) := by exact_mod_cast (2*(n+k)).factorial_pos
  have pcbA : (0:ℝ) < (Nat.centralBinom (2 * n + k + 1) : ℝ) := by exact_mod_cast (2*n+k+1).centralBinom_pos
  have pcbB : (0:ℝ) < (Nat.centralBinom (n + k) : ℝ) := by exact_mod_cast (n+k).centralBinom_pos
  have pP : (0:ℝ) < ∏ j ∈ range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ) := by
    apply prod_pos; intro j _; exact_mod_cast Nat.succ_pos _
  -- nonzero facts for `field_simp`
  have hden : ((2 * n + k + 1)! : ℝ) * ((2 * (n + k))! : ℝ) * 2 ^ (n + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero p2nk1.ne' p2nk.ne') (by positivity)
  -- Express `P` in closed form, substitute, and reduce via the central-binomial identities.
  have hPval : (∏ j ∈ range (n + 1), ((2 * (n + k + j) + 1 : ℕ) : ℝ))
      = ((4 * n + 2 * k + 2)! : ℝ) * ((n + k)! : ℝ)
          / (((2 * n + k + 1)! : ℝ) * ((2 * (n + k))! : ℝ) * 2 ^ (n + 1)) := by
    rw [eq_div_iff hden]; linear_combination hProdR
  rw [hPval, show (2:ℝ) ^ (2 * (n + 1)) = 2 ^ (n + 1) * 2 ^ (n + 1) from by rw [two_mul, pow_add],
    ← hcbA, ← hcbB]
  have e1 : (2:ℝ) ^ (n + 1) ≠ 0 := by positivity
  field_simp

/-- The exact term ratio (paper eq. (e10)), central-binomial form. -/
private lemma e10_identity (q n k : ℕ) :
    c q n k / chat q n k
      = ((6 * n + 2 * k + 2 : ℝ) / (2 * k + 1))
        * ((Nat.centralBinom (2 * n + k + 1) : ℝ) / (Nat.centralBinom (n + k) : ℝ)
            / 2 ^ (2 * (n + 1))) ^ (2 * q) := by
  rw [ratio_prod_form, bracket_centralBinom]

/-! ### Applying the central-binomial rate

The Stirling leading terms combine to `√((n+k)/(2n+k+1))`, since
`4^(2n+k+1)/4^(n+k) = 2^(2(n+1))`.  This is the exp-free main factor. -/

open Real in
/-- The ratio of Stirling leading terms, divided by `2^(2(n+1))`, is exactly
`√((n+k)/(2n+k+1))`. -/
private lemma mainratio_eq (n k : ℕ) (hn : 1 ≤ n) :
    ((4:ℝ) ^ (2 * n + k + 1) / Real.sqrt (Real.pi * ((2 * n + k + 1 : ℕ) : ℝ)))
      / ((4:ℝ) ^ (n + k) / Real.sqrt (Real.pi * ((n + k : ℕ) : ℝ)))
      / 2 ^ (2 * (n + 1))
      = Real.sqrt (((n + k : ℕ) : ℝ) / ((2 * n + k + 1 : ℕ) : ℝ)) := by
  have hBpos : (0:ℝ) < ((n + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n + k)
  have hApos : (0:ℝ) < ((2 * n + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * n + k + 1)
  have h4 : (4:ℝ) ^ (2 * n + k + 1) = 4 ^ (n + k) * 2 ^ (2 * (n + 1)) := by
    rw [show 2 * n + k + 1 = (n + k) + (n + 1) from by ring, pow_add,
      show (4:ℝ) ^ (n + 1) = 2 ^ (2 * (n + 1)) from by rw [show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul]]
  have hsπ : Real.sqrt Real.pi ≠ 0 := Real.sqrt_pos.mpr Real.pi_pos |>.ne'
  have hsA : Real.sqrt ((2 * n + k + 1 : ℕ) : ℝ) ≠ 0 := Real.sqrt_pos.mpr hApos |>.ne'
  have hsB : Real.sqrt ((n + k : ℕ) : ℝ) ≠ 0 := Real.sqrt_pos.mpr hBpos |>.ne'
  rw [Real.sqrt_mul Real.pi_pos.le, Real.sqrt_mul Real.pi_pos.le,
    Real.sqrt_div hBpos.le, h4]
  field_simp

open Real in
/-- Two-sided bound on the exp-free-times-Stirling central-binomial ratio. -/
private lemma R_bounds (n k : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (((n + k : ℕ) : ℝ) / ((2 * n + k + 1 : ℕ) : ℝ))
        * Real.exp (-((1:ℝ) / (6 * ((2 * n + k + 1 : ℕ) : ℝ)) + 1 / (24 * ((n + k : ℕ) : ℝ))))
      ≤ (Nat.centralBinom (2 * n + k + 1) : ℝ) / (Nat.centralBinom (n + k) : ℝ) / 2 ^ (2 * (n + 1))
    ∧ (Nat.centralBinom (2 * n + k + 1) : ℝ) / (Nat.centralBinom (n + k) : ℝ) / 2 ^ (2 * (n + 1))
      ≤ Real.sqrt (((n + k : ℕ) : ℝ) / ((2 * n + k + 1 : ℕ) : ℝ))
        * Real.exp ((1:ℝ) / (24 * ((2 * n + k + 1 : ℕ) : ℝ)) + 1 / (6 * ((n + k : ℕ) : ℝ))) := by
  obtain ⟨hAlo, hAhi⟩ := centralBinom_rate (2 * n + k + 1) (by omega)
  obtain ⟨hBlo, hBhi⟩ := centralBinom_rate (n + k) (by omega)
  set A : ℝ := ((2 * n + k + 1 : ℕ) : ℝ) with hAdef
  set B : ℝ := ((n + k : ℕ) : ℝ) with hBdef
  have hApos : (0:ℝ) < A := by rw [hAdef]; exact_mod_cast (by omega : 0 < 2 * n + k + 1)
  have hBpos : (0:ℝ) < B := by rw [hBdef]; exact_mod_cast (by omega : 0 < n + k)
  set UA : ℝ := (4:ℝ) ^ (2 * n + k + 1) / Real.sqrt (Real.pi * A) with hUAdef
  set UB : ℝ := (4:ℝ) ^ (n + k) / Real.sqrt (Real.pi * B) with hUBdef
  have hUApos : 0 < UA := by
    rw [hUAdef]; apply div_pos (by positivity) (Real.sqrt_pos.mpr (by positivity))
  have hUBpos : 0 < UB := by
    rw [hUBdef]; apply div_pos (by positivity) (Real.sqrt_pos.mpr (by positivity))
  have hD : (0:ℝ) < 2 ^ (2 * (n + 1)) := by positivity
  have hcBB : (0:ℝ) < (Nat.centralBinom (n + k) : ℝ) := by exact_mod_cast (n + k).centralBinom_pos
  -- the Stirling ratio simplification
  have hmain : UA / UB / 2 ^ (2 * (n + 1)) = Real.sqrt (B / A) := by
    rw [hUAdef, hUBdef, hBdef, hAdef]; exact mainratio_eq n k hn
  have hexpBlo : (0:ℝ) < Real.exp (-(1 / (6 * B))) := Real.exp_pos _
  constructor
  · -- lower bound
    calc Real.sqrt (B / A) * Real.exp (-(1 / (6 * A) + 1 / (24 * B)))
        = (UA * Real.exp (-(1 / (6 * A)))) / (UB * Real.exp (1 / (24 * B)))
            / 2 ^ (2 * (n + 1)) := by
          rw [← hmain]
          simp only [neg_add, Real.exp_add, Real.exp_neg]
          field_simp
      _ ≤ (Nat.centralBinom (2 * n + k + 1) : ℝ) / (Nat.centralBinom (n + k) : ℝ)
            / 2 ^ (2 * (n + 1)) := by
          gcongr
  · -- upper bound
    calc (Nat.centralBinom (2 * n + k + 1) : ℝ) / (Nat.centralBinom (n + k) : ℝ)
            / 2 ^ (2 * (n + 1))
        ≤ (UA * Real.exp (1 / (24 * A))) / (UB * Real.exp (-(1 / (6 * B))))
            / 2 ^ (2 * (n + 1)) := by
          gcongr
      _ = Real.sqrt (B / A) * Real.exp (1 / (24 * A) + 1 / (6 * B)) := by
          rw [← hmain]
          simp only [Real.exp_add, Real.exp_neg]
          field_simp

open Real in
/-- The inner ratio raised to `2q`: two-sided, with the exp-free main term
`((n+k)/(2n+k+1))^q` and an explicit exponential error factor. -/
private lemma Rpow_bounds (q n k : ℕ) (hn : 1 ≤ n) :
    (((n + k : ℕ) : ℝ) / ((2 * n + k + 1 : ℕ) : ℝ)) ^ q
        * Real.exp (2 * (q:ℝ) * (-((1:ℝ) / (6 * ((2 * n + k + 1 : ℕ) : ℝ))
            + 1 / (24 * ((n + k : ℕ) : ℝ)))))
      ≤ ((Nat.centralBinom (2 * n + k + 1) : ℝ) / (Nat.centralBinom (n + k) : ℝ)
          / 2 ^ (2 * (n + 1))) ^ (2 * q)
    ∧ ((Nat.centralBinom (2 * n + k + 1) : ℝ) / (Nat.centralBinom (n + k) : ℝ)
          / 2 ^ (2 * (n + 1))) ^ (2 * q)
      ≤ (((n + k : ℕ) : ℝ) / ((2 * n + k + 1 : ℕ) : ℝ)) ^ q
        * Real.exp (2 * (q:ℝ) * ((1:ℝ) / (24 * ((2 * n + k + 1 : ℕ) : ℝ))
            + 1 / (6 * ((n + k : ℕ) : ℝ)))) := by
  obtain ⟨hlo, hhi⟩ := R_bounds n k hn
  set A : ℝ := ((2 * n + k + 1 : ℕ) : ℝ) with hAdef
  set B : ℝ := ((n + k : ℕ) : ℝ) with hBdef
  have hynn : (0:ℝ) ≤ B / A := by rw [hAdef, hBdef]; positivity
  set R : ℝ := (Nat.centralBinom (2 * n + k + 1) : ℝ) / (Nat.centralBinom (n + k) : ℝ)
      / 2 ^ (2 * (n + 1)) with hR
  -- `(√(B/A)·exp t)^(2q) = (B/A)^q · exp (2q·t)`
  have hpow : ∀ t : ℝ, (Real.sqrt (B / A) * Real.exp t) ^ (2 * q)
      = (B / A) ^ q * Real.exp (2 * (q:ℝ) * t) := by
    intro t
    rw [mul_pow, pow_mul, Real.sq_sqrt hynn, ← Real.exp_nat_mul]
    congr 2
    push_cast; ring
  have hSlo_nonneg : (0:ℝ) ≤ Real.sqrt (B / A) * Real.exp (-(1 / (6 * A) + 1 / (24 * B))) := by
    positivity
  constructor
  · calc (B / A) ^ q * Real.exp (2 * (q:ℝ) * (-(1 / (6 * A) + 1 / (24 * B))))
        = (Real.sqrt (B / A) * Real.exp (-(1 / (6 * A) + 1 / (24 * B)))) ^ (2 * q) := (hpow _).symm
      _ ≤ R ^ (2 * q) := by
          apply pow_le_pow_left₀ hSlo_nonneg hlo
  · calc R ^ (2 * q)
        ≤ (Real.sqrt (B / A) * Real.exp (1 / (24 * A) + 1 / (6 * B))) ^ (2 * q) := by
          apply pow_le_pow_left₀ (by positivity) hhi
      _ = (B / A) ^ q * Real.exp (2 * (q:ℝ) * (1 / (24 * A) + 1 / (6 * B))) := hpow _

/-! ### The main (exp-free) factor is near 1 on the window

`M₀(n,k) = (6n+2k+2)/(2k+1) · ((n+k)/(2n+k+1))^q = φ(k/n, 1/n)`, where `φ` is a
continuous function with `φ(x₀,0) = f(x₀) = 1`.  Joint continuity at `(x₀,0)`
gives uniform closeness on the window. -/
private lemma mainFactor_near_one (q : ℕ) {x₀ : ℝ} (hx₀ : 0 < x₀) (hfx₀ : f q x₀ = 1)
    {δ' : ℝ} (hδ' : 0 < δ') :
    ∃ ε, 0 < ε ∧ ε < x₀ ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ k : ℕ,
      (x₀ - ε) * n ≤ (k : ℝ) → (k : ℝ) ≤ (x₀ + ε) * n →
      |(6 * (n : ℝ) + 2 * k + 2) / (2 * k + 1)
          * (((n + k : ℕ) : ℝ) / ((2 * n + k + 1 : ℕ) : ℝ)) ^ q - 1| ≤ δ' := by
  set prof : ℝ × ℝ → ℝ := fun p => (6 + 2 * p.1 + 2 * p.2) / (2 * p.1 + p.2)
      * ((1 + p.1) / (2 + p.1 + p.2)) ^ q with hprof
  -- value at (x₀,0)
  have hval : prof (x₀, 0) = 1 := by
    have hf : (x₀ + 3) / x₀ * ((x₀ + 1) / (x₀ + 2)) ^ q = 1 := by rw [← f]; exact hfx₀
    rw [hprof]
    show (6 + 2 * x₀ + 2 * 0) / (2 * x₀ + 0) * ((1 + x₀) / (2 + x₀ + 0)) ^ q = 1
    rw [mul_zero, add_zero, add_zero, add_zero,
      show (6 + 2 * x₀) / (2 * x₀) = (x₀ + 3) / x₀ from by
        rw [div_eq_div_iff (by positivity) (by positivity)]; ring,
      show (1 + x₀) / (2 + x₀) = (x₀ + 1) / (x₀ + 2) from by
        rw [div_eq_div_iff (by positivity) (by positivity)]; ring]
    exact hf
  -- continuity at (x₀,0)
  have hcont : ContinuousAt prof (x₀, 0) := by
    rw [hprof]
    have hnum1 : Continuous (fun p : ℝ × ℝ => 6 + 2 * p.1 + 2 * p.2) := by fun_prop
    have hden1 : Continuous (fun p : ℝ × ℝ => 2 * p.1 + p.2) := by fun_prop
    have hnum2 : Continuous (fun p : ℝ × ℝ => 1 + p.1) := by fun_prop
    have hden2 : Continuous (fun p : ℝ × ℝ => 2 + p.1 + p.2) := by fun_prop
    exact (hnum1.continuousAt.div hden1.continuousAt (by show (2:ℝ) * x₀ + 0 ≠ 0; positivity)).mul
      ((hnum2.continuousAt.div hden2.continuousAt (by show (2:ℝ) + x₀ + 0 ≠ 0; positivity)).pow q)
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨γ, hγ, hball⟩ := hcont δ' hδ'
  set ε : ℝ := min (x₀ / 2) (γ / 2) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hεlt : ε < x₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεγ : ε < γ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / ε)
  refine ⟨ε, hεpos, hεlt, max N 1, le_max_right _ _, ?_⟩
  intro n hn k hk1 hk2
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hnne : (n:ℝ) ≠ 0 := hnpos.ne'
  -- `1/n ≤ ε`
  have hNn : 1 / ε ≤ (n:ℝ) := le_trans hN (by exact_mod_cast le_trans (le_max_left N 1) hn)
  have h1n : 1 / (n:ℝ) ≤ ε := by
    rw [div_le_iff₀ hnpos]
    have := (div_le_iff₀ hεpos).mp hNn
    linarith
  -- `|k/n - x₀| ≤ ε`
  have hx1 : x₀ - ε ≤ (k:ℝ) / n := (le_div_iff₀ hnpos).mpr hk1
  have hx2 : (k:ℝ) / n ≤ x₀ + ε := (div_le_iff₀ hnpos).mpr hk2
  have habs : |(k:ℝ) / n - x₀| ≤ ε := abs_le.mpr ⟨by linarith, by linarith⟩
  -- distance bound
  have hdle : dist ((k:ℝ) / n, 1 / (n:ℝ)) (x₀, (0:ℝ)) ≤ ε := by
    rw [Prod.dist_eq]
    apply max_le
    · rw [Real.dist_eq]; exact habs
    · rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; exact h1n
  have hprofp := hball (lt_of_le_of_lt hdle hεγ)
  rw [hval, Real.dist_eq] at hprofp
  -- `M₀ = prof(k/n, 1/n)`
  have hM0 : (6 * (n : ℝ) + 2 * k + 2) / (2 * k + 1)
        * (((n + k : ℕ) : ℝ) / ((2 * n + k + 1 : ℕ) : ℝ)) ^ q
      = prof ((k:ℝ) / n, 1 / (n:ℝ)) := by
    rw [hprof]
    show _ = (6 + 2 * ((k:ℝ)/n) + 2 * (1/n)) / (2 * ((k:ℝ)/n) + 1/n)
        * ((1 + (k:ℝ)/n) / (2 + (k:ℝ)/n + 1/n)) ^ q
    have e1 : (6 * (n:ℝ) + 2 * k + 2) / (2 * k + 1)
        = (6 + 2 * ((k:ℝ)/n) + 2 * (1/n)) / (2 * ((k:ℝ)/n) + 1/n) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]; field_simp
    have e2 : (((n + k : ℕ) : ℝ) / ((2 * n + k + 1 : ℕ) : ℝ))
        = (1 + (k:ℝ)/n) / (2 + (k:ℝ)/n + 1/n) := by
      push_cast
      rw [div_eq_div_iff (by positivity) (by positivity)]; field_simp
    rw [e1, e2]
  rw [hM0]
  exact le_of_lt hprofp

/-! ### The exponential error factor is near 1 on the window

The exp arguments are bounded by `5q/(12n) → 0` uniformly in `k` (since
`2n+k+1 ≥ n` and `n+k ≥ n`), so both error factors are within `δ'` of 1
eventually. -/
private lemma exp_err_control (q : ℕ) {δ' : ℝ} (hδ' : 0 < δ') (hδ'1 : δ' ≤ 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ k : ℕ,
      Real.exp (2 * (q:ℝ) * ((1:ℝ) / (24 * ((2 * n + k + 1 : ℕ) : ℝ))
          + 1 / (6 * ((n + k : ℕ) : ℝ)))) ≤ 1 + δ'
      ∧ 1 - δ' ≤ Real.exp (2 * (q:ℝ) * (-((1:ℝ) / (6 * ((2 * n + k + 1 : ℕ) : ℝ))
          + 1 / (24 * ((n + k : ℕ) : ℝ))))) := by
  have hL : 0 < Real.log (1 + δ') := Real.log_pos (by linarith)
  set thr : ℝ := min (Real.log (1 + δ')) δ' with hthr
  have hthrpos : 0 < thr := lt_min hL hδ'
  obtain ⟨N, hN⟩ := exists_nat_ge (5 * (q:ℝ) / (12 * thr) + 1)
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro n hn k
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hknn : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hAge : (n:ℝ) ≤ ((2 * n + k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hBge : (n:ℝ) ≤ ((n + k : ℕ) : ℝ) := by push_cast; linarith
  set A : ℝ := ((2 * n + k + 1 : ℕ) : ℝ) with hAdef
  set B : ℝ := ((n + k : ℕ) : ℝ) with hBdef
  have hApos : 0 < A := lt_of_lt_of_le hnpos hAge
  have hBpos : 0 < B := lt_of_lt_of_le hnpos hBge
  -- `5q/(12n) ≤ thr`
  have hNn : (N:ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left N 1) hn
  have hn_ge : 5 * (q:ℝ) / (12 * thr) ≤ (n:ℝ) := by linarith
  have hsn : 5 * (q:ℝ) / (12 * n) ≤ thr := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hn_ge
    nlinarith [hn_ge]
  -- reciprocal comparisons
  have hia : 1 / (24 * A) ≤ 1 / (24 * (n:ℝ)) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have hib : 1 / (6 * B) ≤ 1 / (6 * (n:ℝ)) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have hic : 1 / (6 * A) ≤ 1 / (6 * (n:ℝ)) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have hid : 1 / (24 * B) ≤ 1 / (24 * (n:ℝ)) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have hup : 2 * (q:ℝ) * (1 / (24 * A) + 1 / (6 * B)) ≤ 5 * (q:ℝ) / (12 * n) := by
    refine le_trans (mul_le_mul_of_nonneg_left (add_le_add hia hib) (by positivity)) (le_of_eq ?_)
    field_simp; ring
  have hlow : 2 * (q:ℝ) * (1 / (6 * A) + 1 / (24 * B)) ≤ 5 * (q:ℝ) / (12 * n) := by
    refine le_trans (mul_le_mul_of_nonneg_left (add_le_add hic hid) (by positivity)) (le_of_eq ?_)
    field_simp; ring
  refine ⟨?_, ?_⟩
  · -- upper
    have h1 : 2 * (q:ℝ) * (1 / (24 * A) + 1 / (6 * B)) ≤ Real.log (1 + δ') :=
      le_trans hup (le_trans hsn (min_le_left _ _))
    calc Real.exp (2 * (q:ℝ) * (1 / (24 * A) + 1 / (6 * B)))
        ≤ Real.exp (Real.log (1 + δ')) := Real.exp_le_exp.mpr h1
      _ = 1 + δ' := Real.exp_log (by linarith)
  · -- lower
    have h2 : 2 * (q:ℝ) * (1 / (6 * A) + 1 / (24 * B)) ≤ δ' :=
      le_trans hlow (le_trans hsn (min_le_right _ _))
    have hexp := Real.add_one_le_exp (-(2 * (q:ℝ) * (1 / (6 * A) + 1 / (24 * B))))
    rw [show 2 * (q:ℝ) * (-(1 / (6 * A) + 1 / (24 * B)))
        = -(2 * (q:ℝ) * (1 / (6 * A) + 1 / (24 * B))) from by ring]
    linarith

/-- Piece 2 (termwise ratio on the window): uniformly over
`|k - x₀ n| ≤ εn`, the ratio `c k / ĉ k` is eventually within `δ(ε)` of 1,
where `δ(ε) → 0` with `ε`.  Uses the two-sided central-binomial rate
`centralBinom_rate` for the expression (e10) of the paper. -/
theorem term_ratio_on_window (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (x₀ - ε) * n ≤ k → (k : ℝ) ≤ (x₀ + ε) * n →
      |c q n k / chat q n k - 1| ≤ δ := by
  -- work with `δ' = min (δ/3) 1`
  set δ' : ℝ := min (δ / 3) 1 with hδ'def
  have hδ'pos : 0 < δ' := by rw [hδ'def]; positivity
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'3 : 3 * δ' ≤ δ := by have : δ' ≤ δ / 3 := min_le_left _ _; linarith
  obtain ⟨ε, hεpos, _hεx₀, N₁, hN₁1, hmain⟩ := mainFactor_near_one q hx₀ hfx₀ hδ'pos
  obtain ⟨N₂, _hN₂1, hexp⟩ := exp_err_control q hδ'pos hδ'1
  refine ⟨ε, hεpos, ?_⟩
  rw [eventually_atTop]
  refine ⟨max N₁ N₂, fun n hn k hk1 hk2 => ?_⟩
  have hnN₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnN₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : 1 ≤ n := le_trans hN₁1 hnN₁
  -- the three ingredients
  have hMF := hmain n hnN₁ k hk1 hk2
  obtain ⟨hexpU, hexpL⟩ := hexp n hnN₂ k
  obtain ⟨hlo, hhi⟩ := Rpow_bounds q n k hn1
  rw [e10_identity]
  set coef : ℝ := (6 * n + 2 * k + 2 : ℝ) / (2 * k + 1) with hcoefdef
  set y : ℝ := ((n + k : ℕ) : ℝ) / ((2 * n + k + 1 : ℕ) : ℝ) with hydef
  set Rp : ℝ := ((Nat.centralBinom (2 * n + k + 1) : ℝ) / (Nat.centralBinom (n + k) : ℝ)
      / 2 ^ (2 * (n + 1))) ^ (2 * q) with hRpdef
  have hcoef_nn : (0:ℝ) ≤ coef := by rw [hcoefdef]; positivity
  rw [abs_le] at hMF
  have hM0u : coef * y ^ q ≤ 1 + δ' := by linarith [hMF.2]
  have hM0l : 1 - δ' ≤ coef * y ^ q := by linarith [hMF.1]
  have hM0nn : (0:ℝ) ≤ coef * y ^ q := by linarith [hM0l]
  have hupper : coef * Rp ≤ (1 + δ') * (1 + δ') := by
    calc coef * Rp
        ≤ coef * (y ^ q * Real.exp (2 * (q:ℝ) * ((1:ℝ) / (24 * ((2 * n + k + 1 : ℕ) : ℝ))
            + 1 / (6 * ((n + k : ℕ) : ℝ))))) := mul_le_mul_of_nonneg_left hhi hcoef_nn
      _ = (coef * y ^ q) * Real.exp (2 * (q:ℝ) * ((1:ℝ) / (24 * ((2 * n + k + 1 : ℕ) : ℝ))
            + 1 / (6 * ((n + k : ℕ) : ℝ)))) := by ring
      _ ≤ (1 + δ') * (1 + δ') := mul_le_mul hM0u hexpU (Real.exp_pos _).le (by linarith)
  have hlower : (1 - δ') * (1 - δ') ≤ coef * Rp := by
    calc (1 - δ') * (1 - δ')
        ≤ (coef * y ^ q) * Real.exp (2 * (q:ℝ) * (-((1:ℝ) / (6 * ((2 * n + k + 1 : ℕ) : ℝ))
            + 1 / (24 * ((n + k : ℕ) : ℝ))))) := mul_le_mul hM0l hexpL (by linarith) hM0nn
      _ = coef * (y ^ q * Real.exp (2 * (q:ℝ) * (-((1:ℝ) / (6 * ((2 * n + k + 1 : ℕ) : ℝ))
            + 1 / (24 * ((n + k : ℕ) : ℝ)))))) := by ring
      _ ≤ coef * Rp := mul_le_mul_of_nonneg_left hlo hcoef_nn
  rw [abs_le]
  constructor
  · nlinarith [hlower, hδ'3, hδ'pos, hδ'1]
  · nlinarith [hupper, hδ'3, hδ'pos, hδ'1]

end Zeta5Odd
