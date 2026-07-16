# Zudilin ζ(5)…ζ(s) irrationality — formalization progress

Paper: W. Zudilin, arXiv:1801.09895. Lean/Mathlib: `v4.33.0-rc1`, Mathlib master `cd580e54`.

## DONE (pre-existing, committed on master)
Lemma 4 (asymptotics), sorry-free, axioms `[propext, Classical.choice, Quot.sound]`.
Public API (all in `namespace Zeta5Odd`, parametrized by `q`, with `s = 2q-1`, `q ≥ 4`):
- `c q n k = R_n(n+1+k)`, `chat q n k = R_n(n+1/2+k)`, `r q n = ∑' k, c q n k`, `rhat q n = ∑' k, chat q n k`.
- `f q x`, `g q x`; `existsUnique_x0 q hq : ∃! x, 0 < x ∧ f q x = 1`.
- `tendsto_root_r`, `tendsto_root_rhat : (r/rhat q n)^(1/n) → g q x₀`.
- `tendsto_ratio : r q n / rhat q n → 1`.
- (private, in Ratio.lean) `seven_r_sub_rhat_pos_eventually : ∀ᶠ n, 0 < 7·r q n − rhat q n`.

## STRATEGIC DECISION: s = 33 (q = 17), not s = 25
- s=25 needs full PNT (`d_n^{1/n} → e`). **This Mathlib has NO PNT.** Best available is
  Chebyshev `psi_le : ψ x ≤ log4·x + o(x)` ⇒ limsup d_n^{1/n} ≤ 4 = e^{1.386}. That is too weak
  for EVERY s (asymptotic requirement → log 4 from below, never reached).
- External `PrimeNumberTheoremAnd` would pin a different Mathlib commit ⇒ forbidden `lake update`. Not viable.
- **s=33 works with Hanson `d_n ≤ 3^n`** (elementary). Verified numerically: `lcm(1..n) ≤ 3^n` for all n
  (max rate log d_n/n = 1.0388 < log 3 = 1.0986). Margins (need `s·logC + log g(x₀,s) < 0`):
  - s=33: log g(x₀,33) = −36.3834, x₀ = 2.289e-5. Hanson(3^33): `3^33·g(x₀) = e^{-0.129} < 1` ✓ (tight).
  - (s=25 reference: log g = −25.2924, x₀ = 3.671e-4, needs e, margin 0.292.)
- **Deviation from paper flagged:** final theorem is about ζ(5),…,ζ(33) (paper's own stated fallback,
  §4 last paragraph: "d_n < 3^n from [Ha72] and s=33").

## MODULE MAP (remaining work)
| module | target | status |
|---|---|---|
| `ZetaValues.lean` | `zetaVal`, `oddIdx = {5,7,…,33}`, `exists_common_denom` | **DONE (sorry-free)** |
| `Main.lean` | `zeta_odd_irrational : ∃ j ∈ oddIdx, Irrational (zetaVal j)`; root-test endgame; `tendsto_seven_root` | **DONE (sorry-free)** — reduces to the 3 lemmas below |
| `Forms.lean` | `elim_integer n : ∃ A A0:ℤ, d_n^33·(7r−r̂) = Σ_{j∈oddIdx} A_j ζ(j) + A0` (Lemmas 1–3 + ζ(3)-elim) | sorry — worker running |
| `DnBound.lean` | `lcmUpto_le_three_pow n : (lcmUpto n : ℝ) ≤ 3^n` (Hanson) | sorry — worker running |
| `Numeric.lean` | `g_small : ∀ x, 0<x → f 17 x = 1 → 3^33·g 17 x < 1` | sorry — worker running |

Full build GREEN. Glue lemmas `tendsto_seven_root` (Main) and `exists_common_denom` (ZetaValues) proven.

### Detailed sub-lemma status (6 real sorries)
**Forms.lean** — `elim_integer` PROVED from `repr_combined`; `dvd_lcmUpto`, `harmonic_integrality`, `oddIdx3` bookkeeping PROVED. Remaining:
  - `Rn_eq_c`, `Rn_eq_chat` (bridge R_n↔c/chat, factorial algebra) — **worker running (round 2)**
  - `partialFraction_exists` (e04 + Lemma 1 integrality + Lemma 2 symmetry) — NOT yet assigned (hardest)
  - `repr_combined` (e07/e08 Lemma-3 assembly; consumes the two above) — NOT yet assigned
**DnBound.lean** — Hanson divisibility half FULLY PROVED sorry-free (`lcmUpto_dvd_hansonC` via Sylvester seq + `core_sum_le` + Legendre). Remaining:
  - `hansonC_le_three_pow` (size bound `C n ≤ 3^n`, `Σ(log aᵢ)/aᵢ=1.083<log3`) — **worker running (round 2)**
**Numeric.lean** — `g_small` (`3^33·g(x₀)<1`) — **DONE (sorry-free)**, bracket b=1/40, quadratic-Bernoulli + log-g monotonicity + exact rational `64·121⁶·41³⁴·40²⁸ < 3²³⁹`.

Workers auto-merge to master on completion (harness handles worktree→master).

## Key interface identity (why `elim_integer` is exactly right)
ζ(j)-coeff of `r` is `a_j`; of `rhat` is `a_j(2^j−1)`. So `7r−r̂` has ζ(j)-coeff `a_j(8−2^j)`.
At j=3: `8−2^3 = 0` ⇒ ζ(3) eliminated (this is the "7 = 2^3−1" trick).
For odd j∈[5,33]: `d_n^{33−j} a_j ∈ ℤ` (Lemma 1) ⇒ `d_n^33·a_j(8−2^j) ∈ ℤ`. Constant: `d_n^33(7a_0−â_0) ∈ ℤ`.

## Root-test endgame (Main)
`b_n := d_n^33·(7r−r̂) ≥ 0`. `b_n^{1/n} ≤ 3^33·(7r−r̂)^{1/n} → 3^33 g(x₀) < 1` ⇒ `b_n → 0`.
`a·b_n` is a positive integer (elim_integer + common denom + `seven_r_sub_rhat_pos_eventually`) → 0: contradiction.
