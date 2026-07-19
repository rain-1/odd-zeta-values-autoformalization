import Cbcert.Certificate
import Cbcert.Decay
import Cbcert.Integrality

/-!
# Assembly (Layer L3) — STAGED

Combines Lemma A (`Decay`), Lemma B (`Certificate`, DONE), Lemma C (`Integrality`)
into the main theorems `w_congruence`, `wtilde_congruence`, `pn_valuation` (whose
frozen statements live in `Cbcert/Defs.lean`).

## The (W) assembly, precisely

Fix `n ≥ 1`, prime `p` with `n < p ≤ 2n`, `p ≥ 5`. All `a_{i,j}` are `p`-integral
(Lemma C), so let `ā_{i,j} : ZMod p` be their reductions under the residue map
`ρ : {p-integral rationals} → ZMod p` (a ring hom). Then, in `ZMod p`:

  ρ(w_n) = Σ_j ā_{3,j}
         = Σ_{j=0}^n Σ_{i=1}^6 (δ_{i,3}) ā_{i,j}
         = Σ_j Σ_i (Σ_{M∈{3,p+2,2p+1}, i≤min(6,M)} c_M · Cneg i (M-i) · j^{M-i}) ā_{i,j}
                                                              -- Lemma B `certificate`, x = (j : ZMod p)
         = Σ_{M} c_M · Σ_i Cneg i (M-i) · Σ_j j^{M-i} ā_{i,j}   -- reorder finite sums
         = Σ_{M} c_M · ρ(E_M(a))                                -- ρ ring hom; index range = EM's
         = Σ_{M} c_M · ρ(0) = 0.                                -- Lemma A: E_M(a)=0 for M ≤ 4n+2 ≤ 4n+4

The three certificate indices satisfy `3 ≤ 4n+4` and `2p+1 ≤ 4n+1 ≤ 4n+4` (since
`p ≤ 2n`), so every `E_M(a)` invoked is in Lemma A's range. Points `0,…,n` are
distinct in `ZMod p` because `p > n` (needed to read `Σ_j` over `ZMod p`).

Then `ρ(w_n) = 0` together with `p`-integrality gives `padicValRat p (w_n) ≥ 1`
(for `p`-integral `x`: `ρ(x)=0 ↔ 1 ≤ padicValRat p x`, via `p ∤ x.den` and
`padicValRat p x = padicValInt p x.num`).

For (W̃): identical with `ã`, `Q=−k(k+n)`, certificate `ψ`, and Lemma A's range
`M ≤ 4n+2` (top index `2p+1 ≤ 4n+1 ≤ 4n+2` uses `p ≤ 2n`, EXACTLY the reason
`p = 2n+1` is excluded). The companion certificate `ψ`-coefficients are the
`atcoeff`-analogue; the per-`(i,x)` identity reduces to `certificate` applied with
the `ã`-target `F_i(j) = j(n−j)[i=3]+(2j−n)[i=4]−[i=5]` (see PROGRESS pitfalls).

For (CB₁): `p_n = w̃_n v_n − w_n ṽ_n` with `v_n, ṽ_n` `p`-integral (Lemma C on `a`,
`ã`, `H`) and `ρ(w_n) = ρ(w̃_n) = 0`, so `ρ(p_n) = 0`, hence `padicValRat p p_n ≥ 1`.

## Remaining obligations (all `sorry`-staged)
1. `Decay.decay_a`, `Decay.decay_at` (Lemma A) — the risk concentrate.
2. `Integrality.integrality_{a,at,H}` (Lemma C).
3. The residue map `ρ` and the bridge `ρ(x)=0 ∧ p-integral → 1 ≤ padicValRat p x`
   (Mathlib route: `PadicInt.toZMod` residue, or a direct `padicValRat` argument via
   `x = x.num /. x.den`, `p ∤ x.den`, `p ∣ x.num`).
4. `reduce_congruence` below: the finite `ZMod p` reordering computation (uses only
   `certificate`, `decay_*`, `Finset` algebra) — the genuinely new bridging lemma.
5. Wire 1–4 into `Cbcert.w_congruence`/`wtilde_congruence`/`pn_valuation`, replacing
   the frozen `sorry` stubs in `Defs.lean` (those stubs are the contract; the proven
   versions land here, then the stubs are removed).

Lemma B (`Certificate.certificate`) is COMPLETE and sorry-free; the assembly's
mod-`p` engine is available.
-/

namespace Cbcert.Main

open Cbcert

end Cbcert.Main
