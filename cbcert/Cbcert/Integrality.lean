import Cbcert.Defs

/-!
# Lemma C — p-integrality (Layer L3, part 1) — STAGED

For a prime `p > n`, every `a_{i,j}`, `ã_{i,j}` (`j ≤ n`) and `H_j^{(i)}` (`j ≤ n`)
is `p`-integral: `padicValRat p (·) ≥ 0` (`cb_certificate.tex`, §1 and the proof of
Prop. 1). This legitimises reduction mod `p` in the assembly.

## Status: STATED, proof STAGED (`sorry`).

## Intended route
`acoeff n i j = [t^{6-i}] B_j`, a `ℤ`-linear combination of `(n!)^4`, `(n/2 - j)`
and reciprocals of integers `m - j` with `|m - j| ≤ n` (the pole differences), plus
the `(k+n+m)` / `(k-m)` numerator factors with `|·| ≤ 2n`. The ONLY denominators
come from `tsInv6 (m - j)`, i.e. powers of `(m - j)` with `0 ≤ m,j ≤ n`, `m ≠ j`, so
`1 ≤ |m - j| ≤ n < p`: no denominator is divisible by `p`. Hence `padicValRat ≥ 0`.
CAREFUL (SPEC pitfall): numerator factors `n + m - j` can equal `p`, but they sit in
the numerator, harmless for integrality; only the `m - j` pole differences (all
`< p` in absolute value) enter denominators. `H_j^{(i)} = Σ_{m=1}^j m^{-i}` has
denominators `m ≤ j ≤ n < p`.

Concretely provable from `acoeff`'s definition via `padicValRat`/`padicValNat`
bounds on `tsMul`, `tsLin`, `tsInv6` (each `tsInv6 c` with `1 ≤ |c| ≤ n < p` is a
`p`-adic integer), plus `padicValRat.mul`/`add` monotonicity.
-/

namespace Cbcert.Integrality

open Cbcert

/-- **Lemma C (base coefficients).** For `p` prime with `n < p`, every `a_{i,j}` is
`p`-integral. -/
theorem integrality_a (n i j : ℕ) (p : ℕ) (hp : p.Prime) (hpn : n < p) :
    0 ≤ padicValRat p (acoeff n i j) := by
  sorry

/-- **Lemma C (companion coefficients).** `ã_{i,j}` is `p`-integral for `n < p`. -/
theorem integrality_at (n i j : ℕ) (p : ℕ) (hp : p.Prime) (hpn : n < p) :
    0 ≤ padicValRat p (atcoeff n i j) := by
  sorry

/-- **Lemma C (harmonic sums).** `H_j^{(i)}` is `p`-integral for `j < p`. -/
theorem integrality_H (i j : ℕ) (p : ℕ) (hp : p.Prime) (hpj : j < p) :
    0 ≤ padicValRat p (Hh i j) := by
  sorry

end Cbcert.Integrality
