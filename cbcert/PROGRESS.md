# cbcert — formalization progress

Target: `worthiness/cb_certificate.tex` (Frobenius certificate for central-binomial
cancellation). Contract: `cbcert/SPEC.md`. Template: `zeta5odd/`.

## Status: SCAFFOLD GREEN (statement freeze not yet begun)

- Lake project scaffolded. Toolchain `leanprover/lean4:v4.33.0-rc1`, Mathlib pinned
  to `cd580e54f1a6b46063824e80cec92f64692cbe78` (same commit as zeta5odd → cache hit).
- `lake exe cache get` + `lake build` GREEN on hello-world (`Cbcert/Defs.lean` currently
  holds only a placeholder `1+1=2` example). 8662 jobs.

## Module plan (owner-file-per-worker; integration through manager)

| module | content | worker | status |
|---|---|---|---|
| `Cbcert/Defs.lean` | R_n, a_{i,j}, ã, w/w̃/v/ṽ/p_n, H, E_M, 2 main thm statements | manager | placeholder only |
| `Cbcert/Certificate.lean` | Lemma B (binomial cert, mod p) — land FIRST | — | not started |
| `Cbcert/Integrality.lean` | Lemma C (p-integrality, p>n) | — | not started |
| `Cbcert/Decay.lean` | Lemma A (E_M=0 via LaurentSeries) — hardest | — | not started |
| `Cbcert/PartialFraction.lean` | PF existence/uniqueness + Taylor formula for a_{i,j} | — | not started |
| `Cbcert/Main.lean` (+ `Numeric.lean`) | assembly `w_congruence`, `wtilde_congruence`, `pn_valuation` | — | not started |

## Next action (manager)
Write & freeze `Cbcert/Defs.lean` (statement-first). Open design question being
resolved: concrete vs abstract definition of a_{i,j} (Taylor formula is computable but
heavy; abstract-via-PF is clean for statements but blocks numeric sanity). Reference
ground-truth for closed forms: `worthiness/lemma_cb_explore.py` (`all_data(n)`),
`worthiness/cb_certificate_check.py` (E_M / three-term certificate check, 420 pairs pass).

Conventions confirmed from reference code:
- C(−i, r) = (−1)^r · C(i+r−1, r) (integer).
- Certificate (w):   c_3=1, c_{p+2}=−2, c_{2p+1}=1  [φ=(k^p−k)^2].
- Certificate (w̃):  ψ = −k(k+n)(k^p−k)^2 (six terms).
- ã target: F_i(j) = j(n−j)·[i=3] + (2j−n)·[i=4] + (−1)·[i=5].
- Exact layer sums S_i = Σ_j a_{i,j} = 0 for i ∈ {1,2,4,6} (over ℚ, all n).
