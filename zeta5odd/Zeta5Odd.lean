/-
Root module: Lemma 4 of arXiv:1801.09895, modular layout.

  Basic.lean    — definitions + all sorry-free lemmas (shared; do not edit
                  concurrently, coordinate through the orchestrator)
  Localize.lean — sum_localizes                    (worker A)
  Window.lean   — term_ratio_on_window             (worker B)
  Roots.lean    — tendsto_root_r / tendsto_root_rhat (worker C)
  Ratio.lean    — tendsto_ratio                    (worker D)
-/
import Zeta5Odd.Basic
import Zeta5Odd.Localize
import Zeta5Odd.Window
import Zeta5Odd.Roots
import Zeta5Odd.Ratio
