import Cbcert.Defs

/-!
# Lemma B — the Frobenius certificate (Layer L2)

The mathematically new content of `worthiness/cb_certificate.tex` (§3–4), and the
self-contained mod-`p` heart of the argument.

For a prime `p ≥ 5`, `i ∈ {1,…,6}` and every `x : ZMod p`, the three-term
combination of decay functionals reproduces `δ_{i,3}`:
`(c₃·C(-i,3-i)·x^{3-i})[i≤3] − 2·C(-i,p+2-i)·x^{p+2-i} + C(-i,2p+1-i)·x^{2p+1-i}
 = δ_{i,3}`
with `(c₃, c_{p+2}, c_{2p+1}) = (1, −2, 1)`, i.e. `φ = (k^p − k)^2`.

Proof: the left side is `[X^{i-1}] φ(X − C x)` and in characteristic `p`,
`(X − C x)^p = X^p − C x` (`sub_pow_char` + `ZMod.pow_card`), so
`φ(X − C x) = (X^p − X)^2 = X^{2p} − 2X^{p+1} + X^2`, whose `(i-1)`-th coefficient
is `δ_{i,3}` because `i-1 ≤ 5 < 6 ≤ p+1 ≤ 2p`.

The Frobenius collapse `x^p = x` is essential and uniform: at the boundary `p = 5`
the individual binomial coefficients do NOT vanish (`C(6,5) ≡ 1`), so a term-by-term
argument would fail — only the polynomial identity closes it.
-/

namespace Cbcert.Certificate

open Polynomial

variable {p : ℕ}

/-- The `(i-1)`-th coefficient of `(X^p − X)^2` over `ZMod p`, for `p ≥ 5` and the
relevant low range `m ≤ 5`: it is `1` exactly at `m = 2`. -/
lemma frob_sq_coeff [Fact p.Prime] (h5 : 5 ≤ p) {m : ℕ} (hm : m ≤ 5) :
    (((X : (ZMod p)[X]) ^ p - X) ^ 2).coeff m = if m = 2 then 1 else 0 := by
  have e : ((X : (ZMod p)[X]) ^ p - X) ^ 2
      = X ^ (2 * p) - (X ^ (p + 1) + X ^ (p + 1)) + X ^ 2 := by ring
  rw [e]
  have h1 : m ≠ 2 * p := by omega
  have h2 : m ≠ p + 1 := by omega
  simp only [coeff_add, coeff_sub, coeff_X_pow]
  rw [if_neg h1, if_neg h2]
  simp

/-- Per-term bridge: the `Cneg`-weighted monomial equals the `(i-1)`-th coefficient
of `(X + C(-x))^n`, via `coeff_X_add_C_pow` and
`Cneg i (n+1-i) = (-1)^{n+1-i} C(n, i-1)`. Requires `1 ≤ i ≤ n+1`. -/
lemma term_bridge (i n : ℕ) (hi : 1 ≤ i) (hin : i ≤ n + 1) (x : ZMod p) :
    (Cneg i (n + 1 - i) : ZMod p) * x ^ (n + 1 - i)
      = ((X + C (-x)) ^ n : (ZMod p)[X]).coeff (i - 1) := by
  rw [coeff_X_add_C_pow]
  have hexp : n - (i - 1) = n + 1 - i := by omega
  have hidx : i + (n + 1 - i) - 1 = n := by omega
  have hsym : Nat.choose n (n + 1 - i) = Nat.choose n (i - 1) := by
    rw [← hexp]; exact Nat.choose_symm (by omega)
  rw [hexp]
  simp only [Cneg, hidx, hsym]
  push_cast
  rw [neg_pow]
  ring

/-- **Lemma B (the certificate).** For `p` prime, `p ≥ 5`, `i ∈ {1,…,6}` and every
`x : ZMod p`, the three-term certificate reproduces `δ_{i,3}`. The `i ≤ 3` guard on
the first term is the faithful rendering of "terms with `M − i < 0` are omitted"
(matching the `Finset.Icc 1 (min 6 M)` index range in `EM`). -/
theorem certificate [Fact p.Prime] (h5 : 5 ≤ p) {i : ℕ} (hi1 : 1 ≤ i) (hi6 : i ≤ 6)
    (x : ZMod p) :
    (if i ≤ 3 then (Cneg i (3 - i) : ZMod p) * x ^ (3 - i) else 0)
      + (-2 : ZMod p) * ((Cneg i (p + 2 - i) : ZMod p) * x ^ (p + 2 - i))
      + (Cneg i (2 * p + 1 - i) : ZMod p) * x ^ (2 * p + 1 - i)
      = if i = 3 then 1 else 0 := by
  set Y : (ZMod p)[X] := X + C (-x) with hY
  -- Term 2 (M = p+2, n = p+1).
  have t2 : (Cneg i (p + 2 - i) : ZMod p) * x ^ (p + 2 - i) = (Y ^ (p + 1)).coeff (i - 1) := by
    have h := term_bridge i (p + 1) hi1 (by omega) x
    rw [show (p + 1) + 1 - i = p + 2 - i from by omega] at h
    exact h
  -- Term 3 (M = 2p+1, n = 2p).
  have t3 : (Cneg i (2 * p + 1 - i) : ZMod p) * x ^ (2 * p + 1 - i)
      = (Y ^ (2 * p)).coeff (i - 1) := by
    have h := term_bridge i (2 * p) hi1 (by omega) x
    rw [show 2 * p + 1 - i = 2 * p + 1 - i from rfl] at h
    exact h
  -- Term 1 (M = 3, n = 2) with the guard.
  have t1 : (if i ≤ 3 then (Cneg i (3 - i) : ZMod p) * x ^ (3 - i) else 0)
      = (Y ^ 2).coeff (i - 1) := by
    by_cases h : i ≤ 3
    · rw [if_pos h]
      have hb := term_bridge i 2 hi1 (by omega) x
      rw [show 2 + 1 - i = 3 - i from by omega] at hb
      exact hb
    · rw [if_neg h, hY, coeff_X_add_C_pow]
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
  rw [t1, t2, t3]
  -- Combine the coefficients.
  have hcomb : (Y ^ 2).coeff (i - 1) + (-2 : ZMod p) * (Y ^ (p + 1)).coeff (i - 1)
        + (Y ^ (2 * p)).coeff (i - 1)
      = (Y ^ 2 - 2 * Y ^ (p + 1) + Y ^ (2 * p)).coeff (i - 1) := by
    simp only [coeff_add, coeff_sub, coeff_ofNat_mul]
    ring
  rw [hcomb]
  -- Y^2 - 2 Y^(p+1) + Y^(2p) = (Y^p - Y)^2 = (X^p - X)^2.
  have hYpow : Y ^ 2 - 2 * Y ^ (p + 1) + Y ^ (2 * p) = (Y ^ p - Y) ^ 2 := by ring
  have hfrob : Y ^ p - Y = (X : (ZMod p)[X]) ^ p - X := by
    have hYval : Y = (X : (ZMod p)[X]) - C x := by rw [hY, C_neg]; ring
    rw [hYval, sub_pow_char, ← C_pow, ZMod.pow_card]; ring
  rw [hYpow, hfrob, frob_sq_coeff h5 (show i - 1 ≤ 5 from by omega)]
  by_cases h : i = 3
  · subst h; norm_num
  · rw [if_neg h, if_neg (show i - 1 ≠ 2 from by omega)]

end Cbcert.Certificate
