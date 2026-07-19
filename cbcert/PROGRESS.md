# cbcert — formalization progress

Target: `worthiness/cb_certificate.tex` (Frobenius certificate for central-binomial
cancellation). Contract: `cbcert/SPEC.md`. Template: `zeta5odd/`.

## Status: DEFS FROZEN + NUMERIC GATE GREEN

- Lake project: toolchain `leanprover/lean4:v4.33.0-rc1`, Mathlib pinned to
  `cd580e54f1a6b46063824e80cec92f64692cbe78` (cache hit).
- `Cbcert/Defs.lean` — all definitions + the 3 main theorem STATEMENTS (sorry bodies).
  Concrete/computable `a_{i,j}` via truncated local Taylor series (`Bseries`, List-based
  `tsMul` chosen for cheap kernel reduction). Compiles.
- `Cbcert/Numeric.lean` — statement-freeze gate, GREEN (2m23s build). Cross-checks the
  Lean definitions against `worthiness/lemma_cb_explore.py` ground truth:
  n=2 full chain `w,wt,u,ut,vv,vt,pn` (also matches `ErrorExhibit`'s independently
  hardcoded PF data) + n=3 `w,wt,u,ut`. No sorry, no native_decide.

## Confirmed conventions (from reference code, locked into Defs)
- `Cneg i r = (-1)^r · C(i+r-1, r)` (integer), `i ≥ 1`.
- Certificate (w):   c_3=1, c_{p+2}=−2, c_{2p+1}=1  [φ=(k^p−k)^2].
- Certificate (w̃):  ψ = −k(k+n)(k^p−k)^2 (six terms).
- `ã_{i,j} = j(n−j)a_{i,j} + (2j−n)a_{i+1,j} − a_{i+2,j}` (idx>6 → 0 via `acoeff`).
- `EM n M b` sums `i ∈ Icc 1 (min 6 M)` — the range handles the "M−i<0 omitted" convention.
- n=2 anchors: w=6125/4, w̃=1764, u=469, ũ=552, v=74463/32, ṽ=43085/16, p₂=−1190161/64.
- No w_n/w̃_n zeros on the theorem domain n≤60 → bare `padicValRat ≥ 1` statements are sound.

## Module plan (owner-file-per-worker; integration through manager)

| module | content | status |
|---|---|---|
| `Cbcert/Defs.lean` | R_n data, a/ã, w/w̃/u/ũ/v/ṽ/p_n, H, Cneg, E_M, 3 thm stmts | FROZEN (3 sorry: the 3 main thms) |
| `Cbcert/Numeric.lean` | n=2,3 sanity gate | GREEN, no sorry |
| `Cbcert/Certificate.lean` | Lemma B (binomial cert, mod p) | in progress (manager) |
| `Cbcert/Integrality.lean` | Lemma C (p-integrality, p>n) | not started |
| `Cbcert/Decay.lean` | Lemma A (E_M=0 via PF identity + decay) | not started (risk concentrate) |
| `Cbcert/Main.lean` | assembly `w_congruence`, `wtilde_congruence`, `pn_valuation` | not started |

## Sorry inventory
- `Defs.lean`: `w_congruence`, `wtilde_congruence`, `pn_valuation` (the 3 main theorems;
  to be re-proved in `Main.lean` and the Defs stubs deleted, or Main proves standalone).

## Lemma B proof plan (derived, for Certificate.lean)
Target (matches assembly): for p prime ≥5, i ∈ {1..6}, x : ZMod p,
`(if i ≤ 3 then c_3·Cneg i (3−i)·x^(3−i) else 0) + c_{p+2}·Cneg i (p+2−i)·x^(p+2−i)
 + c_{2p+1}·Cneg i (2p+1−i)·x^(2p+1−i) = if i=3 then 1 else 0`.
Route: `F_i(x) = coeff_{i-1}(φ(U − C x))` where `φ(k)=Σ c_M k^{M−1}`; and in char p
`(U − C x)^p = U^p − C x` (`sub_pow_char` + `ZMod.pow_card`), so
`φ(U − C x) = (U^p − U)^2 = U^{2p} − 2U^{p+1} + U^2`, whose coeff_{i-1} is δ_{i,3}
for i−1 ≤ 5 < 6 ≤ p+1. Bridge uses `Cneg i (M−i) = (-1)^{M-i} C(M−1,i−1)` and
`coeff_{i-1}((U − C x)^{M−1}) = C(M−1,i−1)(−x)^{M−i}`.
NOTE: naive per-term binomial-vanishing FAILS at p=5 (e.g. C(6,5)≡1); the Frobenius
collapse (x^p=x) is essential and uniform — do NOT split into "each binomial ≡0".

## Next actions
1. Land `Certificate.lean` (Lemma B).
2. `Integrality.lean` (Lemma C) + `Decay.lean` (Lemma A) — the general-n partial-fraction
   layer; risk concentrate is Lemma A. Consider elementary route: prove the cleared PF
   polynomial identity `N_n = Σ a_{i,j}(k+j)^{6-i}∏_{m≠j}(k+m)^6`, then
   `E_M(a) = [x^M] R_n(1/x)` with `R_n(1/x) = x^{4n+5}·Ñ(x)/D̃(x)` (D̃(0)=1) ⇒ vanish.
3. `Main.lean` assembly.

Ground truth: `worthiness/lemma_cb_explore.py` (`all_data`), `cb_certificate_check.py`.
