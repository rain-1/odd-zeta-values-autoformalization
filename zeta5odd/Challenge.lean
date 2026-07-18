/-
Challenge statement for `leanprover/comparator`.

This file imports **only Mathlib**: it fixes, in self-contained Mathlib
vocabulary, exactly what the formalization claims, with the proof left as
`sorry`.  `Solution.lean` discharges the same statement from the project.

Statement: at least one of ζ(5), ζ(7), …, ζ(33) is irrational, where ζ is
Mathlib's `riemannZeta` and the index j ranges over the odd integers in
[5, 33].  `riemannZeta j` is complex; for integer j > 1 it takes a real value,
so we phrase irrationality of `(riemannZeta j).re`.
-/
import Mathlib

theorem zeta_odd_irrational :
    ∃ j : ℕ, Odd j ∧ 5 ≤ j ∧ j ≤ 33 ∧ Irrational (riemannZeta j).re := by
  sorry
