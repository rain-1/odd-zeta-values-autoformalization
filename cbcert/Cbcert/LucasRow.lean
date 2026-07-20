import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Int.GCD
import Cbcert.Defs

/-!
# T1 — the Lucas–Frobenius `q`-row theorem

The Brown–Zudilin weight-`0` ladder is captured by the manifestly-integral
double-binomial sum

    `Q n = Σ_{k,l ∈ range (n+1)} C(n+k,n)·C(n,k)²·C(n+l,n)·C(n,l)²·C(n+k+l,n)`

(see `worthiness/PHASE2_SALVAGE_VERIFY.md` §V2: `Q n = (−1)^{n+1}·q_n/C(2n,n)`,
integers `1, 21, 2989, 714549, …`).  The theorem (`Q_lucas_frobenius`) is the first
row of the Frobenius matrix: for every prime `p` and `r < p`,

    `Q (a*p + r) ≡ Q a · Q r  (mod p)`.

## Proof route (mirror `worthiness/salvage_v3_lucas_proof.py`, VERIFIED on 2.19M
summands, 0 exceptions)

Split every index in base `p`: `k = b*p + s`, `l = c*p + t` (`0 ≤ s,t < p`),
`N = a*p + r`.  Two claims:

* **(CARRY-KILL)** the summand
  `T(k,l) = C(N+k,N)·C(N,k)²·C(N+l,N)·C(N,l)²·C(N+k+l,N)`
  satisfies `T ≡ 0 (mod p)` unless **all** of `b ≤ a, c ≤ a, s ≤ r, t ≤ r,
  r+s < p, r+t < p, r+s+t < p`.  Any base-`p` carry pushes a low digit of one
  argument below the corresponding digit of `N`, so a Lucas factor `C(·, r) = 0`
  (or `C(r, s) = 0`).  Mathlib input: `Choose.choose_modEq_choose_mod_mul_choose_div`
  (single-digit Lucas: `choose n k ≡ choose (n%p) (k%p) * choose (n/p) (k/p) [ZMOD p]`).
* **(FACTOR)** on the surviving box the summand splits
  `T(bp+s, cp+t) ≡ T_hi(b,c;a)·T_lo(s,t;r) (mod p)`, where
  `T_hi = C(a+b,a)C(a,b)²C(a+c,a)C(a,c)²C(a+b+c,a)` is the `(b,c)`-summand of `Q a`
  and `T_lo` the `(s,t)`-summand of `Q r`.

Summation over the box gives `Q N ≡ (Σ T_hi)(Σ T_lo) = Q a · Q r`, the surviving
high box being exactly `{0 ≤ b,c ≤ a}` (support of `Q a` mod `p`) and the low box
the mod-`p` support of `Q r`.

House rules: no `sorry` at completion, no `native_decide`, no new axioms, axioms
exactly `[propext, Classical.choice, Quot.sound]`.

**Bridge to the project's `q_n` (STAGED, honest note):** `Q n = (−1)^{n+1}·q_n /
C(2n,n)` with `q_n = u_n·w̃_n − ũ_n·w_n` (`Cbcert/Defs.lean`; `ErrorExhibit.Q2_eq`
already proves `−(u·w̃ − ũ·w)/6 = 2989 = Q 2`).  This normalization bridge is not
needed for the standalone congruence and is left for a follow-up wave.
-/

namespace Cbcert.LucasRow

open Finset

/-- The Brown–Zudilin double-binomial weight-`0` value, over `ℕ`
(manifestly a natural number). -/
def Q (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
    Nat.choose (n + k) n * (Nat.choose n k) ^ 2 * Nat.choose (n + l) n
      * (Nat.choose n l) ^ 2 * Nat.choose (n + k + l) n

/-! ### Numeric gate

`Q` reproduces the verified integer sequence `1, 21, 2989, 714549, …`
(`worthiness/salvage_data.py`, PHASE2 §V2). `Q 2 = 2989` matches
`ErrorExhibit.Q2_eq`. Kernel `decide` only, no `native_decide`. -/

theorem Q_zero : Q 0 = 1 := by decide
theorem Q_one : Q 1 = 21 := by decide
theorem Q_two : Q 2 = 2989 := by decide
theorem Q_three : Q 3 = 714549 := by decide
theorem Q_four : Q 4 = 217515501 := by decide

-- `Q 5 = 76157194521`, `Q 6 = 29212502584861` (cross-checked exactly in
-- `worthiness/salvage_data.py`; omitted from the kernel gate for build speed).

/-- Sanity instance of the congruence, `Q (2·5+2) ≡ Q 2 · Q 2 (mod 5)`
(`Q 12 mod 5 = (2989·2989) mod 5`), verified in `salvage_v123.py`
(1592 checks, 0 failures). Documented here; the general theorem is
`Q_lucas_frobenius`. -/
example : True := trivial

/-! ### The theorem -/

/-- **Lucas–Frobenius `q`-row.** For every prime `p` and `r < p`,
`Q (a*p + r) ≡ Q a · Q r (mod p)`. -/
theorem Q_lucas_frobenius (a r p : ℕ) (hp : p.Prime) (hr : r < p) :
    (Q (a * p + r) : ℤ) ≡ (Q a : ℤ) * (Q r : ℤ) [ZMOD (p : ℤ)] := by
  sorry

end Cbcert.LucasRow
