/-
Challenge statement for `leanprover/comparator`.

This file imports **only Mathlib**: it fixes, in self-contained Mathlib
vocabulary, exactly what the formalization claims, with the proof left as
`sorry`.  `Solution.lean` discharges the same statement from the project.

Statement: at least one of ζ(5), ζ(7), …, ζ(33) is irrational, where each
ζ(j) is the real series ∑_{n≥1} 1/nʲ = ∑_{n≥0} 1/(n+1)ʲ and the index set is
the odd integers in [5, 33].
-/
import Mathlib

open scoped BigOperators

theorem zeta_odd_irrational :
    ∃ j ∈ (Finset.Icc 5 33).filter (fun j => Odd j),
      Irrational (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ j) := by
  sorry
