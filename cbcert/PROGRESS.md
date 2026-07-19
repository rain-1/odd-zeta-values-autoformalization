# cbcert — formalization progress

Target: `worthiness/cb_certificate.tex` (Frobenius certificate for central-binomial
cancellation). Contract: `cbcert/SPEC.md`. Template: `zeta5odd/`.

## Status: L0 FROZEN + NUMERIC GATE GREEN + L2 (Lemma B) DONE sorry-free.
L1 (Lemma A) and L3 (Lemma C + assembly) STAGED with precise statements + `sorry`.

Toolchain `leanprover/lean4:v4.33.0-rc1`, Mathlib `cd580e54…` (cache hit).
Whole project builds green (sorries tracked below; build must stay green).

## Module table

| module | content | status |
|---|---|---|
| `Cbcert/Defs.lean` | R_n data, a/ã, w/w̃/u/ũ/v/ṽ/p_n, H, Cneg, E_M, 3 thm stmts | FROZEN; 3 sorry (main thm stubs) |
| `Cbcert/Numeric.lean` | n=2 (full chain, matches ErrorExhibit) + n=3 sanity gate | GREEN, no sorry (~2.4min build) |
| `Cbcert/Certificate.lean` | **Lemma B** (Frobenius certificate, mod p) | **DONE, no sorry**, axioms std |
| `Cbcert/Decay.lean` | Lemma A: `decay_a` (M≤4n+4), `decay_at` (M≤4n+2) | STATED; 2 sorry (risk concentrate) |
| `Cbcert/Integrality.lean` | Lemma C: `integrality_a/at/H` (p-integral, p>n) | STATED; 3 sorry |
| `Cbcert/Main.lean` | assembly plan (full docstring); no code yet | scaffold, no sorry (docstring only) |

## Sorry inventory (8 total; ZERO required at completion)
- `Defs.lean`: `w_congruence`, `wtilde_congruence`, `pn_valuation` (frozen statement
  stubs; the proven versions land in `Main.lean`, then these stubs are removed — they
  cannot be proved in Defs due to the import cycle with the lemma modules).
- `Decay.lean`: `decay_a`, `decay_at` (Lemma A).
- `Integrality.lean`: `integrality_a`, `integrality_at`, `integrality_H` (Lemma C).

## What is DONE and verified
- **L0**: concrete/computable definitions; `a_{i,j} = [t^{6-i}]B_j` via truncated local
  Taylor series (`Bseries`; List-based `tsMul` for cheap kernel reduction). Numeric gate
  reproduces `lemma_cb_explore.py` at n=2 (w,wt,u,ut,vv,vt,pn — also matches the
  independently hardcoded `ErrorExhibit` data) and n=3 (w,wt,u,ut). No native_decide.
- **L2 / Lemma B** (`Certificate.certificate`): for p prime ≥5, i∈{1..6}, x:ZMod p, the
  guarded three-term `(1,-2,1)` certificate equals `δ_{i,3}`.
  `#print axioms = [propext, Classical.choice, Quot.sound]`. Proof = polynomial-coeff
  bridge: LHS `= [X^{i-1}]((X−C x)^p−(X−C x))^2`, which in char p collapses (sub_pow_char
  + ZMod.pow_card) to `(X^p−X)^2 = X^{2p}−2X^{p+1}+X^2`, coeff `δ_{i,3}` since `i−1≤5<6≤p+1`.
  KEY: the Frobenius collapse is uniform; do NOT split per-term (C(6,5)≡1 at p=5).

## Remaining work (for the successor), in dependency order
1. **Lemma A** (`Decay.lean`): elementary power-series route (docstring in file). Needs the
   PF identity `R_n = Σ a_{i,j}(k+j)^{-i}` for the concrete `acoeff` (a `PartialFraction.lean`
   deliverable: the cleared polynomial identity `N_n = Σ a_{i,j}(k+j)^{6-i}∏_{m≠j}(k+m)^6`,
   provable by the Taylor-coefficient characterization), then `E_M(a)=[x^M]R_n(1/x)` and
   `R_n(1/x)=x^{4n+5}·Ñ/D̃`, D̃(0)=1 ⇒ vanish. `PowerSeries` bookkeeping.
2. **Lemma C** (`Integrality.lean`): denominators of `acoeff` come only from `tsInv6 (m−j)`,
   `1≤|m−j|≤n<p` ⇒ p-integral. `H_j^{(i)}` denominators `≤ n < p`. `padicValRat`/`padicValNat`
   bounds on `tsMul/tsLin/tsInv6`.
3. **Assembly** (`Main.lean`): reduction ring hom `ρ: p-integral ℚ → ZMod p`; the finite
   `ZMod p` reordering `ρ(w_n)=Σ_M c_M ρ(E_M(a))=0` (uses `certificate` + `decay_*`); and the
   bridge `ρ(x)=0 ∧ p-integral → 1 ≤ padicValRat p x`. Then discharge the 3 main theorems and
   delete the Defs stubs. Useful Mathlib: `padicValRat.min_le_padicValRat_add`,
   `lt_sum_of_lt`, `PadicInt.toZMod`; or the direct `x = x.num /. x.den` route
   (`padicValRat_le_padicValRat_iff`, `p ∤ den`, `p ∣ num`).
   For (W̃): companion certificate `ψ = −k(k+n)(k^p−k)^2`; per-(i,x) identity reduces to a
   variant of `certificate` with target `F_i(j)=j(n−j)[i=3]+(2j−n)[i=4]−[i=5]`; Lemma A range
   `M≤4n+2` (top index `2p+1≤4n+1` needs `p≤2n`, why `p=2n+1` is excluded).

## Confirmed conventions (locked into Defs)
- `Cneg i r = (-1)^r·C(i+r-1,r)`; certificate (w) `(c_3,c_{p+2},c_{2p+1})=(1,-2,1)`.
- `ã_{i,j}=j(n-j)a_{i,j}+(2j-n)a_{i+1,j}-a_{i+2,j}` (idx>6→0 via `acoeff`).
- `EM n M b` sums `i∈Icc 1 (min 6 M)` — the range encodes the "M−i<0 omitted" convention,
  and matches the `if i≤3` guard in `Certificate.certificate`.
- n=2 anchors: w=6125/4, w̃=1764, u=469, ũ=552, v=74463/32, ṽ=43085/16, p₂=−1190161/64.
- No w_n/w̃_n zeros on domain n≤60 ⇒ bare `padicValRat ≥ 1` statements are sound.

## Commits
- adf2be9 L0: freeze Defs + green numeric gate
- 34dc374 L2: land Lemma B (Frobenius certificate), sorry-free
- (this) L1/L3 skeleton: Decay/Integrality precise statements + Main assembly plan

Ground truth: `worthiness/lemma_cb_explore.py` (`all_data`), `cb_certificate_check.py`.
