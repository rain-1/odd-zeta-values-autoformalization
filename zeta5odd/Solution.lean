/-
Solution for `leanprover/comparator`.

Proves the exact Mathlib-only statement of `Challenge.lean` by unfolding the
project's abbreviations `Zeta5Odd.oddIdx` and `Zeta5Odd.zetaVal` — which are,
definitionally,

  oddIdx  = (Finset.Icc 5 33).filter (fun j => Odd j)
  zetaVal j = ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ j

— and applying the project's main theorem `Zeta5Odd.zeta_odd_irrational`.

`#print axioms zeta_odd_irrational` yields exactly
`[propext, Classical.choice, Quot.sound]` (the standard Mathlib axioms; no
`sorryAx`, no `native_decide`/`ofReduceBool`).
-/
import Mathlib
import Zeta5Odd

open scoped BigOperators

theorem zeta_odd_irrational :
    ∃ j ∈ (Finset.Icc 5 33).filter (fun j => Odd j),
      Irrational (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ j) :=
  Zeta5Odd.zeta_odd_irrational
