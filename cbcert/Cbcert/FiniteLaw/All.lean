import Cbcert.FiniteLaw.N2
import Cbcert.FiniteLaw.N3
import Cbcert.FiniteLaw.N4
import Cbcert.FiniteLaw.N5
import Cbcert.FiniteLaw.N6
import Cbcert.FiniteLaw.N7
import Cbcert.FiniteLaw.N8

/-!
# L5 — aggregation of the finite-range corrected law

This module gathers the per-`n` corrected-law instances (`Cbcert/FiniteLaw/N⟨n⟩.lean`,
one file per `n` so `lake` parallelizes) into a single readable statement over the
verified range, and re-exports the sharp-nonvanishing byproducts.

**Verified range: `n = 2 … 8`** (kernel-computed, no `native_decide`, no new axioms).

## The corrected law, per `n` (integer witnesses `M = 12·d_n⁵·P_n`)

| `n` |  `d_n`  |  `C(2n,n)` | digits of `M` |
|----:|--------:|-----------:|--------------:|
|  2  |    2    |     6      |       7       |
|  3  |    6    |    20      |      11       |
|  4  |   12    |    70      |      15       |
|  5  |   60    |   252      |      21       |
|  6  |   60    |   924      |      24       |
|  7  |  420    |  3432      |      31       |
|  8  |  840    | 12870      |      35       |

(The Brown–Zudilin paper's *uncorrected* `d_n⁵·P_n ∈ ℤ` already fails at `n = 2`
by the factor `12`; see `Cbcert/ErrorExhibit.lean`. The `12` restores integrality
across the whole verified range.)

## Extending the range

To verify further `n` (locally, or split across machines — the files are
independent), run `scripts/l5_gen.py NSTART NEND` (or `scripts/l5_remote.sh`),
then add `import Cbcert.FiniteLaw.N⟨n⟩` above and bump the `Finset.Icc 2 8` bound
in `law_upto` (and the table). Nothing else changes; each new file is a leaf.
-/

namespace Cbcert.FiniteLaw

open Cbcert

/-- **The finite-range corrected Brown–Zudilin law.** For every `n` in the verified
range `2 ≤ n ≤ 8`, the corrected inclusion `12·d_n⁵·P_n ∈ ℤ` holds, where
`P_n = (−1)^{n+1}·p_n/C(2n,n)` is built from the project's canonical `pn`
(`Cbcert/Defs.lean`) and `d_n = lcm(1,…,n)` (`Cbcert/ErrorExhibit.lean`).

Proven by enumerating the kernel-verified per-`n` instances `law_2 … law_8`. -/
theorem law_upto : ∀ n ∈ Finset.Icc 2 8, CorrectedLaw n := by
  intro n hn
  fin_cases hn
  · exact law_2
  · exact law_3
  · exact law_4
  · exact law_5
  · exact law_6
  · exact law_7
  · exact law_8

/-- **Sharp nonvanishing on the verified range.** For `2 ≤ n ≤ 8`, `p_n ≠ 0`.
On this range this upgrades the honest disjunct of `Main.pn_valuation`
(`p_n = 0 ∨ 1 ≤ padicValRat p p_n`) to the sharp second alternative — the
general nonvanishing `p_n ≠ 0` for all `n` remains OPEN (see `Cbcert/Defs.lean`). -/
theorem pn_ne_zero_upto : ∀ n ∈ Finset.Icc 2 8, pn n ≠ 0 := by
  intro n hn
  fin_cases hn
  · exact pn_ne_zero_2
  · exact pn_ne_zero_3
  · exact pn_ne_zero_4
  · exact pn_ne_zero_5
  · exact pn_ne_zero_6
  · exact pn_ne_zero_7
  · exact pn_ne_zero_8

end Cbcert.FiniteLaw
