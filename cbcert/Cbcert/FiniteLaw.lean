import Cbcert.Defs
import Cbcert.ErrorExhibit

/-!
# L5 — the finite-range corrected Brown–Zudilin law

The Brown–Zudilin paper (arXiv:2210.03391) prints an experimental integrality
claim `d_n⁵·P_n ∈ ℤ` for the weight-5 symmetric linear forms; its own displayed
`P₂ = 1190161/384` violates it by exactly `12` (see `Cbcert/ErrorExhibit.lean`).
The **corrected law** is

    `12 · d_n⁵ · P_n ∈ ℤ`,     with   `P_n = (−1)^{n+1} · p_n / C(2n, n)`,

and the `{2,3}`-ceilings sharp (`worthiness/CONJECTURE.md`). This module verifies
the corrected law **per `n` by kernel computation**, one file per `n` under
`Cbcert/FiniteLaw/`, so that `lake` parallelizes the range across cores/machines.

Everything is stated against the project's **canonical** definitions: `pn` and the
whole `w, w̃, v, ṽ` chain from `Cbcert/Defs.lean` (reduced through `Bseries`/
`acoeff`), and `d = lcm(1,…,n)` from `Cbcert/ErrorExhibit.lean`. No parallel
re-definition of the arithmetic can drift from the audited construction.

House rules (inherited): no `sorry`, **no `native_decide`** (pure kernel reduction
via `norm_num`/`decide`), no new axioms — the axiom set of every `law_n` is
`[propext, Classical.choice, Quot.sound]`.

Each per-`n` file `Cbcert/FiniteLaw/N⟨n⟩.lean` proves:

* `pn_val_⟨n⟩ : pn n = ⟨literal ℚ⟩` — the expensive kernel reduction of the
  canonical construction to its exact rational value;
* `law_⟨n⟩ : CorrectedLaw n` — `∃ m : ℤ, 12·d_n⁵·P_n = m`, with the integer
  witness `m` supplied literally (computed in exact arithmetic by
  `scripts/l5_gen.py`), so the kernel only *checks* the equation;
* `pn_ne_zero_⟨n⟩ : pn n ≠ 0` — a free byproduct at the same kernel cost. On the
  verified range this upgrades the honest disjunct of `Main.pn_valuation`
  (`p_n = 0 ∨ 1 ≤ padicValRat p p_n`) to the **sharp** second alternative.

The aggregate theorem `law_upto` (bottom of this file, once the range is imported)
enumerates the verified `n`.
-/

namespace Cbcert.FiniteLaw

open Cbcert

/-- `d n = lcm(1,…,n)`, reusing the audited definition from `ErrorExhibit`. -/
abbrev d : ℕ → ℕ := Cbcert.ErrorExhibit.d

/-- The Brown–Zudilin symmetric value `P_n = (−1)^{n+1}·p_n / C(2n, n)`
(the Zu02 correspondence displayed just after eq. `dn-totsym`; for `n = 2` this
reproduces `ErrorExhibit.P₂`). Built on the canonical `pn` of `Cbcert/Defs.lean`. -/
def BZP (n : ℕ) : ℚ := (-1) ^ (n + 1) * pn n / (Nat.choose (2 * n) n : ℚ)

/-- The corrected law at `n`: `12 · d_n⁵ · P_n ∈ ℤ`. -/
def CorrectedLaw (n : ℕ) : Prop := ∃ m : ℤ, 12 * (d n : ℚ) ^ 5 * BZP n = (m : ℚ)

/-! ### Reduction tactic

`eval_pn` reduces the canonical `pn n` (through the truncated-series machinery of
`Cbcert/Defs.lean`) to a closed rational, exactly as `Numeric.eval_cb`. It is used
in each per-`n` file to prove `pn_val_⟨n⟩`. Everything downstream (`law_⟨n⟩`,
`pn_ne_zero_⟨n⟩`) is a *cheap* `norm_num` rewrite off that single literal. -/

/-- Rewrite a `Finset.Icc 1 j` sum into a `Finset.range j` sum, so that the harmonic
sums `Hh` and the outer `Finset.Icc 1 6` in `vv`/`vt` peel via `sum_range_succ`
(uniformly in `j`, no per-`n` `Finset.Icc = {…}` shows needed). -/
theorem sum_Icc_one_eq {α : Type*} [AddCommMonoid α] (f : ℕ → α) (j : ℕ) :
    ∑ m ∈ Finset.Icc 1 j, f m = ∑ i ∈ Finset.range j, f (i + 1) := by
  induction j with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

macro "eval_pn" : tactic =>
  `(tactic|
    (norm_num (config := { maxSteps := 100000000 })
      [pn, w, wt, vv, vt, acoeff, atcoeff, Bseries, Hh,
      tsMul, tsConst, tsLin, tsInv6, List.range, List.range.loop, List.foldl,
      List.filter, List.flatMap, sum_Icc_one_eq,
      Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose]))

/-- Bridge lemma: given the canonical value of `pn n` as a literal, the value of
`d n`, and the central binomial `C(2n, n)` as a literal, `12·d_n⁵·P_n` equals the
claimed integer witness. Every hypothesis except `hp` is a cheap literal check
(`d n` and `C(2n,n)` by `decide`, the final arithmetic by `norm_num`); the only
expensive obligation per file is `hp : pn n = P` (the canonical kernel reduction). -/
theorem law_of_vals (n : ℕ) (m : ℤ) (D C : ℕ) (P : ℚ)
    (hd : d n = D) (hc : Nat.choose (2 * n) n = C) (hp : pn n = P)
    (hchk : 12 * (D : ℚ) ^ 5 * ((-1) ^ (n + 1) * P / (C : ℚ)) = (m : ℚ)) :
    CorrectedLaw n :=
  ⟨m, by rw [BZP, hd, hp, hc]; exact hchk⟩

end Cbcert.FiniteLaw
