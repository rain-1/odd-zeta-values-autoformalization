import Cbcert.Defs

/-!
# Numeric sanity gate (Layer L0)

Cross-checks the concrete definitions of `Cbcert/Defs.lean` against the
independently computed reference values (`worthiness/lemma_cb_explore.py`,
`all_data(n)`), at `n = 2` (matching `ErrorExhibit`'s independently hardcoded
partial-fraction data) and `n = 3` (fully independent generality check). This is
the statement-freeze gate: the Lean definitions reproduce ground truth.

No `sorry`, no `native_decide` — pure kernel reduction via `norm_num`.
-/

namespace Cbcert.Numeric

open Cbcert

/-- Reduction tactic: unfold the truncated-series machinery and evaluate. -/
macro "eval_cb" : tactic =>
  `(tactic|
    (norm_num [w, wt, u, ut, vv, vt, pn, acoeff, atcoeff, Bseries, Hh,
      tsMul, tsConst, tsLin, tsInv6, List.range, List.range.loop, List.foldl,
      List.filter, List.flatMap, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.choose, Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
      show Finset.Icc 1 6 = {1,2,3,4,5,6} from by decide,
      show Finset.Icc 1 0 = (∅ : Finset ℕ) from by decide,
      show Finset.Icc 1 1 = {1} from by decide,
      show Finset.Icc 1 2 = {1,2} from by decide,
      show Finset.Icc 1 3 = {1,2,3} from by decide]))

set_option maxHeartbeats 4000000

/-! ### n = 2 — full chain (also cross-checks `ErrorExhibit`) -/

example : w 2   = 6125 / 4      := by eval_cb
example : wt 2  = 1764          := by eval_cb
example : u 2   = 469           := by eval_cb
example : ut 2  = 552           := by eval_cb
example : vv 2  = 74463 / 32    := by eval_cb
example : vt 2  = 43085 / 16    := by eval_cb
example : pn 2  = -1190161 / 64 := by eval_cb

/-! ### n = 3 — independent generality check (base + companion coefficients) -/

example : w 3   = 1524635 / 12  := by eval_cb
example : wt 3  = 346485        := by eval_cb
example : u 3   = 38601         := by eval_cb
example : ut 3  = 105156        := by eval_cb

end Cbcert.Numeric
