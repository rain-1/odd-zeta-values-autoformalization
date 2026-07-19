import Mathlib

/-!
# cbcert — definitions and main theorem statements (Layer L0, frozen)

Concrete/computable formalization of the objects in `worthiness/cb_certificate.tex`,
following the reference implementation `worthiness/lemma_cb_explore.py`
(`base_coefficients`, `companion_coefficients`, `all_data`).

All objects live over `ℚ` and are *computable* so that the finite numeric sanity
checks (`Cbcert/Numeric.lean`) can reduce them for small `n`.

The three main theorems (`w_congruence`, `wtilde_congruence`, `pn_valuation`) are
stated here with `sorry` bodies; they are discharged in `Cbcert/Main.lean`.

Design decision (orchestrator): the partial-fraction coefficients `a_{i,j}` are
defined *concretely* as the truncated local Taylor coefficients of
`B_j(k) = (k+j)^6 R_n(k)` at `k = -j`, exactly mirroring the Python. The
partial-fraction identity `R_n = Σ a_{i,j}/(k+j)^i` is then a *lemma*
(`Cbcert/PartialFraction.lean`), not a definition.
-/

namespace Cbcert

/-! ## Truncated power series (order ≤ 5)

A truncated series is represented as a coefficient function `ℕ → ℚ`; only the
coefficients `0,1,…,5` are ever read (we need Taylor order 5 to reach `a_{1,j}`
from the sixth-order pole). This mirrors `mul_trunc`/`linear_factor`/
`inverse_sixth_factor` in `lemma_cb_explore.py`. -/

/-- Truncated (order ≤ 5) power-series multiplication (Cauchy product). Mirrors
`mul_trunc` in the reference. Only coefficients `r ≤ 5` are meaningful.
Implemented via `List.foldl` so that closed instances reduce cheaply. -/
def tsMul (a b : ℕ → ℚ) : ℕ → ℚ :=
  fun r => (List.range (r + 1)).foldl (fun acc s => acc + a s * b (r - s)) 0

/-- The constant series `c`. -/
def tsConst (c : ℚ) : ℕ → ℚ := fun r => if r = 0 then c else 0

/-- The linear factor `c + t` (reference `linear_factor(c) = [c, 1]`). -/
def tsLin (c : ℚ) : ℕ → ℚ := fun r => if r = 0 then c else if r = 1 then 1 else 0

/-- Expansion of `(c + t)^(-6)` to order 5:
`[t^r] = (-1)^r · C(5+r, r) · c^(-6-r)` (reference `inverse_sixth_factor`). -/
def tsInv6 (c : ℚ) : ℕ → ℚ :=
  fun r => (-1) ^ r * (Nat.choose (5 + r) r : ℚ) / c ^ (6 + r)

/-- The truncated local Taylor series of `B_j(k) = (k+j)^6 R_n(k)` at `k = -j`,
in the local variable `t = k + j`, to order 5. This is exactly
`base_coefficients`'s inner `series` in `lemma_cb_explore.py`:

    (n!)^4 · ((n/2 - j) + t) · ∏_{m=1}^n ((-(j+m)) + t)·((n+m-j) + t)
           · ∏_{m=0, m≠j}^n ((m-j) + t)^{-6}. -/
def Bseries (n j : ℕ) : ℕ → ℚ :=
  let init := tsMul (tsConst ((Nat.factorial n : ℚ) ^ 4)) (tsLin ((n : ℚ) / 2 - j))
  let withLin :=
    (List.range n).foldl
      (fun s m => tsMul (tsMul s (tsLin (-(j : ℚ) - ((m : ℚ) + 1))))
                        (tsLin ((n : ℚ) + ((m : ℚ) + 1) - j)))
      init
  ((List.range (n + 1)).filter (· ≠ j)).foldl
    (fun s m => tsMul s (tsInv6 ((m : ℚ) - j))) withLin

/-- The partial-fraction coefficient `a_{i,j}` of `R_n`, for `1 ≤ i ≤ 6` and
`0 ≤ j ≤ n`: `a_{i,j} = [t^{6-i}] B_j`. Zero outside the pole-order range. -/
def acoeff (n i j : ℕ) : ℚ :=
  if 1 ≤ i ∧ i ≤ 6 then Bseries n j (6 - i) else 0

/-- The companion coefficient `ã_{i,j}` = partial-fraction coefficients of
`-k(k+n)R_n`: `ã_{i,j} = j(n-j)a_{i,j} + (2j-n)a_{i+1,j} - a_{i+2,j}`
(indices `> 6` give `0` via `acoeff`). Reference `companion_coefficients`. -/
def atcoeff (n i j : ℕ) : ℚ :=
  (j : ℚ) * ((n : ℚ) - j) * acoeff n i j
    + (2 * (j : ℚ) - (n : ℚ)) * acoeff n (i + 1) j
    - acoeff n (i + 2) j

/-- Harmonic sum `H_j^{(i)} = Σ_{m=1}^j 1/m^i`. -/
def Hh (i j : ℕ) : ℚ := ∑ m ∈ Finset.Icc 1 j, (1 : ℚ) / (m : ℚ) ^ i

/-! ## The functionals -/

/-- `w_n = Σ_{j=0}^n a_{3,j}` (the ζ(3)-coefficient of `r_n`). -/
def w (n : ℕ) : ℚ := ∑ j ∈ Finset.range (n + 1), acoeff n 3 j

/-- `w̃_n = Σ_{j=0}^n ã_{3,j}`. -/
def wt (n : ℕ) : ℚ := ∑ j ∈ Finset.range (n + 1), atcoeff n 3 j

/-- `u_n = Σ_{j=0}^n a_{5,j}` (the ζ(5)-coefficient of `r_n`). -/
def u (n : ℕ) : ℚ := ∑ j ∈ Finset.range (n + 1), acoeff n 5 j

/-- `ũ_n = Σ_{j=0}^n ã_{5,j}`. -/
def ut (n : ℕ) : ℚ := ∑ j ∈ Finset.range (n + 1), atcoeff n 5 j

/-- `v_n = Σ_{i,j} a_{i,j} H_j^{(i)}`. -/
def vv (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 6, ∑ j ∈ Finset.range (n + 1), acoeff n i j * Hh i j

/-- `ṽ_n = Σ_{i,j} ã_{i,j} H_j^{(i)}`. -/
def vt (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 6, ∑ j ∈ Finset.range (n + 1), atcoeff n i j * Hh i j

/-- `p_n = w̃_n v_n − w_n ṽ_n` (the ζ(3)-eliminated numerator). -/
def pn (n : ℕ) : ℚ := wt n * vv n - w n * vt n

/-! ## Binomial constants and the decay functional `E_M` -/

/-- `C(-i, r) = (-1)^r · C(i+r-1, r)` (an integer), for `i ≥ 1`. -/
def Cneg (i r : ℕ) : ℤ := (-1) ^ r * (Nat.choose (i + r - 1) r : ℤ)

/-- The decay functional
`E_M(b) = Σ_{i=1}^{min(6,M)} C(-i, M-i) · Σ_{j=0}^n j^{M-i} b_{i,j}`
(over ℚ). Lemma A asserts `E_M(a) = 0` for `1 ≤ M ≤ 4n+4`. -/
def EM (n M : ℕ) (b : ℕ → ℕ → ℚ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 (min 6 M),
    (Cneg i (M - i) : ℚ) * ∑ j ∈ Finset.range (n + 1), (j : ℚ) ^ (M - i) * b i j

/-! ## Main theorem statements (frozen; proved in `Main.lean`)

`padicValRat p x ≥ 1` is the faithful rendering of `p ∣ x` for a `p`-integral
rational `x ≠ 0` (all `w_n, w̃_n, p_n` are nonzero on the theorem's domain,
verified numerically for `n ≤ 60`). -/

/-- **(W) for `w`.** For every `n ≥ 1` and prime `p` with `n < p ≤ 2n`, `p ≥ 5`:
`p ∣ w_n`. -/
theorem w_congruence (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime)
    (h1 : n < p) (h2 : p ≤ 2 * n) (h5 : 5 ≤ p) :
    1 ≤ padicValRat p (w n) := by
  sorry

/-- **(W) for `w̃`.** Same hypotheses: `p ∣ w̃_n`. -/
theorem wtilde_congruence (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime)
    (h1 : n < p) (h2 : p ≤ 2 * n) (h5 : 5 ≤ p) :
    1 ≤ padicValRat p (wt n) := by
  sorry

/-- **(CB₁).** Same hypotheses: `p ∣ p_n`. -/
theorem pn_valuation (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime)
    (h1 : n < p) (h2 : p ≤ 2 * n) (h5 : 5 ≤ p) :
    1 ≤ padicValRat p (pn n) := by
  sorry

end Cbcert
