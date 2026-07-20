# cbcert — formalization progress

Target: `worthiness/cb_certificate.tex` (Frobenius certificate for central-binomial
cancellation). Contract: `cbcert/SPEC.md`. Template: `zeta5odd/`.

## Status: COMPLETE — ZERO sorries project-wide. Frobenius-certificate theorem PROVEN.

The central-binomial cancellation of `cb_certificate.tex` is formalized and kernel-verified,
for every `n` and every prime `n < p ≤ 2n`, `p ≥ 5`. Canonical theorems (`Cbcert/Main.lean`),
all with axioms exactly `[propext, Classical.choice, Quot.sound]`:
- `res_congruence_w`  : `res p (w n)  = 0`   (`p ∣ w_n`)
- `res_congruence_wt` : `res p (wt n) = 0`   (`p ∣ w̃_n`)
- `res_congruence_pn` : `res p (pn n) = 0`   (`p ∣ p_n`, = CB₁ on the clean interval)
- `w_congruence` / `wtilde_congruence` / `pn_valuation` : the faithful `padicValRat` form,
  `· = 0 ∨ 1 ≤ padicValRat p (·)` (honest disjunct — see the statement-fix note below).

Lemma A (`pf_cleared`, `decay_a`, `decay_at`), Lemma B (`certificate`), Lemma C
(`integrality_a_core`, `integrality_at_core`, `integrality_H`), and the ZMod-p assembly
(residue map + reordering) are ALL sorry-free. `Numeric.lean` gate green (n=2,3 vs ground
truth, + n=3 nonvanishing sanity). Toolchain `v4.33.0-rc1`, Mathlib `cd580e54…`.

### Two statement fixes discovered by formalization (publishable nuggets)
1. **Main theorems** (`Defs.lean` docstring): the intended `1 ≤ padicValRat p (·)` is unsound
   under Mathlib's `padicValRat p 0 = 0` — it is FALSE at `· = 0`, and the certificate gives
   `p ∣ ·` without `· ≠ 0`. Fixed to the disjunctive form; the residue form is the complete
   result.
2. **Lemma C** (`Integrality.lean` docstring): the naive `integrality_a/at` are FALSE without
   `j ≤ n` and `p ≠ 2` — e.g. `acoeff 1 5 2 = 9/128` (`padicVal₂ = −7`), `acoeff 1 5 0 = 9/2`.
   Removed; the proven `_core` lemmas carry those hypotheses.

### The ONE explicitly-OPEN mini-campaign (NOT a sorry — a scope boundary)
General nonvanishing `w_n, w̃_n, p_n ≠ 0` (all `n` on domain) is unproved (numerically true
`n ≤ 60`; relates to the linear forms being nontrivial). It is NOT needed for the canonical
theorems above. If closed, the disjuncts collapse to the sharp `1 ≤ padicValRat`. A finite
witness (`n = 3`) is in `Numeric.lean`.

## L6-staging wave 1 — two theorems (Goal 2) — COMPLETE, sorry-free

Two new modules. Full build green; axioms of all three theorems exactly
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `native_decide`).

- **T1 `Cbcert/LucasRow.lean`** — Lucas–Frobenius `q`-row, **DONE, sorry-free**:
  `Q_lucas_frobenius : (Q (a*p+r):ℤ) ≡ Q a · Q r [ZMOD p]` for prime `p`, `r < p`,
  where `Q n = ∑_{k,l∈range(n+1)} C(n+k,n)C(n,k)²C(n+l,n)C(n,l)²C(n+k+l,n)` (ℕ).
  Mathlib HAS Lucas (`Choose.choose_modEq_choose_mod_mul_choose_div_nat`) — used, not
  reproven. Proof mirrors `salvage_v3_lucas_proof.py`: base-`p` reindex
  (`Finset.sum_bij'` over `range((a+1)*p) → range(a+1)×range p`, out-of-range terms
  vanish via `Nat.choose_eq_zero_of_lt`), per-summand factorization `POINT`
  (`S(ap+r)(bp+s)(cp+t) ≡ S a b c · S r s t`, cased on `s+t<p` survivor vs carry-kill),
  then `Finset.sum_mul_sum`. Numeric gate `Q 0..4 = 1,21,2989,714549,217515501`
  (`decide`; `Q 2 = 2989` matches `ErrorExhibit.Q2_eq`).
  Bridge `Q n = (−1)^{n+1} q_n/C(2n,n)` STAGED (honest note in docstring; not needed
  for the congruence).
- **T2 `Cbcert/Assembly.lean`** — conditional assembly of Sol's master reduction,
  **DONE, sorry-free**. `descent_law (hD : DescentHyp) : ∀ n≥1, ∀ p prime ≥5,
  −5·(Nat.log p n) ≤ v_p(P n)`, `P := BZP`. `hD` (open, NEVER proven here;
  `sorryAx`-free because it is a *hypothesis*) = the verified descent
  `v_p(P (m/p)) − 5 ≤ v_p(P m)` for `p ≤ m` (`salvage_v7.py`, 332 descents /
  0 violations). Faithfulness + `padicValRat`-at-zero trap-freeness argued in the
  docstring (the `v_p(0)=0` convention makes the induction close with NO nonvanishing
  hypothesis). Terminal `P_pIntegral_terminal` proven from the PROVEN cbcert lemmas
  (`Main.pn_pInt` for `p>2n`; band `Main.pn_valuation` + one-digit Kummer
  `padicValNat_choose'` for `n<p≤2n`); induction via `Nat.strong_induction_on` +
  `Nat.log_div_base`. **The full `p ≥ 5` corrected law is now exactly one hypothesis
  (`hD`) away.**

## L5 — finite-range corrected law (`12·d_n⁵·P_n ∈ ℤ`)

Kernel-verified per `n`, one file per `n` (`Cbcert/FiniteLaw/N⟨n⟩.lean`) so lake
parallelizes and ranges split across machines. `P_n = (−1)^{n+1}·p_n/C(2n,n)` off
the **canonical** `pn` (`Defs.lean`) and `d_n` (`ErrorExhibit.lean`). Each file:
`pn_val_⟨n⟩` (the expensive canonical `norm_num` reduction), `pn_ne_zero_⟨n⟩` (free
byproduct — sharpens `Main.pn_valuation`'s disjunct on the range), `law_⟨n⟩ :
CorrectedLaw n` (witness `m` inlined; kernel only CHECKS). Aggregate
`Cbcert/FiniteLaw/All.lean`: `law_upto`, `pn_ne_zero_upto`. No native_decide, no
sorry, axioms `[propext, Classical.choice, Quot.sound]`.

- **Ground-truth gate** (`scripts/l5_gate.py`, exact Fractions, adapts
  `lemma_cb_explore.py`): `12·d_n⁵·P_n ∈ ℤ` verified for `n = 2..24` — the corrected
  law is NOT falsified anywhere in range (any failure would be a headline).
- **Scaling** (this box, `native_decide` banned ⇒ `norm_num` kernel reduction):
  `n=3`≈90 s, `n=4`≈204 s, `n=5`≈354 s; growth ≈1.8×/step; ~7 GB RSS peak (1 job at
  a time under the shared-mem cap). Verified range **n=2..8** (see the per-n log).
- **Extend:** `scripts/l5_gen.py NSTART NEND` (generator, exact witnesses) +
  `scripts/l5_remote.sh HOST NSTART NEND [JOBS]` (remote driver; point at `kbld`
  once SSH exists). Then add imports to `All.lean` + bump the `Icc` bound.

## Module table

| module | content | status |
|---|---|---|
| `Cbcert/Defs.lean` | R_n data, a/ã, w/w̃/u/ũ/v/ṽ/p_n, H, Cneg, E_M, 3 thm stmts | FROZEN; 3 sorry (main thm stubs) |
| `Cbcert/Numeric.lean` | n=2 (full chain, matches ErrorExhibit) + n=3 sanity gate | GREEN, no sorry (~2.4min build) |
| `Cbcert/Certificate.lean` | **Lemma B** (Frobenius certificate, mod p) | **DONE, no sorry**, axioms std |
| `Cbcert/Decay.lean` | Lemma A: `decay_a` (M≤4n+4), `decay_at` (M≤4n+2) | STATED; 2 sorry (risk concentrate) |
| `Cbcert/Integrality.lean` | Lemma C: `integrality_a/at/H` (p-integral, p>n) | STATED; 3 sorry |
| `Cbcert/Main.lean` | assembly BUILT: 3 main thms proven modulo named lemmas | 3 main thms proven; 8 staged sorry |
| `Cbcert/PartialFraction.lean` | pf_cleared (load-bearing PF identity) | STATED; 1 sorry [Worker A1] |

## Round-2 state
- Workers spawned (Opus): A1=`PartialFraction.pf_cleared`, C=`Integrality.*`, A2=`Decay.*`.
- **Assembly BUILT** in `Main.lean`: `w_congruence'`, `wtilde_congruence'`, `pn_valuation'`
  are PROVEN modulo: `res_eq_zero_iff`, `res_add`, `res_mul` (residue-hom infra),
  `res_congruence_w/wt` (the ZMod-p reordering, uses `certificate`+`decay_*`), and
  `w/wt/pn_ne_zero` (nonvanishing). `pInt` closure + `res_sum`/`res_sub`/`res_neg` +
  all `pInt` facts of w/wt/vv/vt/pn are PROVEN (from `Integrality.*`).
- **SOUNDNESS NOTE (flag for coordinator):** `padicValRat p 0 = 0` in Mathlib, so the
  frozen `1 ≤ padicValRat` statements are FALSE where the quantity is 0. The true,
  always-valid content is `res_congruence_w/wt : res p (w n) = 0` (no nonvanishing
  needed). The `padicValRat` form additionally needs `w_n,w̃_n,p_n ≠ 0` — numerically
  true for n≤60, general proof OPEN. Handled via `w/wt/pn_ne_zero` (sorry). Options for
  a clean final: (a) prove nonvanishing, (b) restate main thms as
  `x=0 ∨ 1≤padicValRat`, or (c) keep the residue-congruence form as canonical.

## Round-2 FINAL state (assembly reordering DONE)
- **The entire `ZMod p` reordering is PROVEN sorry-free in `Main`**: `res_natCast`,
  `res_EM_gen`, `cert_sum_j`, `res_congruence_of` (coefficient-agnostic). `res_congruence_w`
  and `res_congruence_wt` are proven via it; their ONLY remaining sorries are the 6 decay
  facts `EM n M (acoeff/atcoeff n) = 0` = `Decay.decay_a`/`decay_at` (Lemma A).
- **To finish the (W) congruences (once A2's `Decay` + A1's `PartialFraction` land):**
  in `Main`, add `import Cbcert.Decay`, and replace the 6 `sorry`s in `res_congruence_w/wt`
  with the commented `Decay.decay_a n M (by omega) (by omega)` / `Decay.decay_at …` calls
  (already written as comments next to each sorry). That closes (W)/(W̃) and hence
  `pn_valuation'` modulo ONLY nonvanishing.
- Remaining after that: `w/wt/pn_ne_zero` (nonvanishing — separate obligation, see SOUNDNESS
  NOTE) and Lemma A itself (`Decay`, `PartialFraction`).

## Round-2 integration update
- **Worker C (Lemma C) DONE.** FINDING: `integrality_a`/`integrality_at` are FALSE as
  originally stated — need `j ≤ n` (else a pole diff `m−j` can be `≡0 mod p`) and `p ≠ 2`
  (else the `n/2−j` factor gives a `1/2`). Worker proved the TRUE `integrality_a_core`,
  `integrality_at_core` (extra hyps `j ≤ n`, `p ≠ 2`) and `integrality_H` fully, sorry-free.
  The public `integrality_a/at` retain 1 sorry each (impossible branch) — REMOVE them once
  callers use the cores. `Main` now uses the cores (both hyps hold: `j∈range(n+1)⇒j≤n`,
  `5≤p⇒p≠2`).
- **Residue infra in `Main` NOW PROVEN sorry-free**: `res_divInt`, `pInt_den`, `res_add`,
  `res_mul`, `res_eq_zero_iff`, `res_neg/sub/sum`, all `pInt` closure + `pInt` of
  w/wt/vv/vt/pn. The 3 main theorems reduce to ONLY: `res_congruence_w/wt` (reordering,
  needs `Decay`) + `w/wt/pn_ne_zero` (nonvanishing).
- Workers A1 (`pf_cleared`, building PowerSeries foundations) and A2 (`Decay`) still running.

## Sorry inventory (updated; ZERO required at completion)
- `Defs.lean` (3): `w_congruence`, `wtilde_congruence`, `pn_valuation` (frozen stubs;
  proven as `Main.*'`; remove once Main is fully closed — import cycle prevents proving
  in Defs).
- `PartialFraction.lean` (1): `pf_cleared` [Worker A1].
- `Decay.lean` (2): `decay_a`, `decay_at` [Worker A2].
- `Integrality.lean` (3): `integrality_a/at/H` [Worker C].
- `Main.lean` (5): `res_eq_zero_iff`, `res_add`, `res_mul` (residue-hom infra, self-
  contained — no worker dep), `res_congruence_w`, `res_congruence_wt` (the reordering).
- `Main.lean` nonvanishing (3): `w_ne_zero`, `wt_ne_zero`, `pn_ne_zero` (separate
  obligation; see SOUNDNESS NOTE).

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

## Reordering recipe for `res_congruence_w` (the last new content; needs `Decay`)
Goal: `res p (w n) = 0`. Add small helpers to `Main` first:
- `res_intCast (m:ℤ) : res p ((m:ℚ)) = (m:ZMod p)` — via `res_divInt m 1` (`(m:ℚ)=Rat.divInt m 1`
  by `Rat.intCast_eq_divInt`; `¬(p:ℤ)∣1`).
- `res_one : res p 1 = 1`; `res_pow (hx:pInt p x)(k) : res p (x^k) = (res p x)^k` — induction via
  `res_mul` + `pInt_pow`.
Then:
1. `res p (w n) = ∑_j res (acoeff n 3 j)`  [`res_sum`, `acoeff_pInt`].
2. Show `∑_j res(acoeff n 3 j) = ∑_{M∈{3,p+2,2p+1}} c_M · res (EM n M (acoeff n))` where
   `c_3=1,c_{p+2}=-2,c_{2p+1}=1`. Route: push `res` through `EM` (res_sum/res_mul/res_intCast/
   res_pow), giving `res(EM n M a) = ∑_{i∈Icc 1(min6M)} (Cneg i (M-i):ZMod p) ∑_j (j:ZMod p)^(M-i) res(a_{i,j})`.
   Reorder `∑_M c_M ∑_i ∑_j → ∑_j ∑_{i∈Icc 1 6} (∑_{M:i≤min6M} c_M·Cneg·j^(M-i)) res(a_{i,j})`;
   the inner `∑_M` bracket is EXACTLY `Certificate.certificate`'s LHS with `x=(j:ZMod p)`, `=δ_{i,3}`;
   collapse `∑_i δ_{i,3} res(a) = res(a_{3,j})`. (Care: match `Icc 1 (min 6 M)` to the certificate's
   `if i≤3` guard — for `M=3`, `min 6 3 = 3`.)
3. `res (EM n M (acoeff n)) = res 0 = 0` by `Decay.decay_a` (each M in range: `3,2p+1≤4n+1≤4n+4`),
   so the whole sum is `0`. `wt` identical with `atcoeff`/`decay_at` (range `≤4n+2`, `2p+1≤4n+1`).

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
