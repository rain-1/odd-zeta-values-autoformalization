# cbcert — Lean 4 formalizations around the Brown–Zudilin ζ(5) work

Lake project (Lean `v4.33.0-rc1`, Mathlib pinned). Three strands live here:

- **Frobenius-certificate theorem** (Tier 1, **complete** — zero sorries) —
  `Cbcert/Main.lean`, documented below; see also `SPEC.md`, `PROGRAM.md`, `PROGRESS.md`.
- **Error exhibit** (complete) — `Cbcert/ErrorExhibit.lean`, documented below.
- **Finite-range corrected law** (`12·d_n⁵·P_n ∈ ℤ`, kernel-verified `n = 2 … 8`,
  extensible across machines) — `Cbcert/FiniteLaw/`, documented below.

Build everything and run the axiom audit:

```bash
cd cbcert
lake build            # green; prints the #print axioms lines
```

---

## Frobenius-certificate theorem — central-binomial cancellation on `n < p ≤ 2n`

**Modules:** `Cbcert/{Defs,Certificate,PartialFraction,Decay,Integrality,Main}.lean`
(sorry-free, no `native_decide`; every canonical theorem uses only
`[propext, Classical.choice, Quot.sound]`). Paper: `worthiness/cb_certificate.tex`.

### What it proves

For every `n ≥ 1` and every prime `p` with `n < p ≤ 2n` and `p ≥ 5`, the ζ(3)-coefficients
`w_n, w̃_n` of Zudilin's two symmetric ζ(5) forms — and hence the eliminated numerator
`p_n = w̃_n v_n − w_n ṽ_n` — vanish mod `p`. This is the large-prime (Phase-1) cancellation
that no `d_n`-denominator estimate can see; it was previously known only experimentally.

The mechanism is the **Frobenius certificate** `φ = (k^p − k)²`: since `k^p − k = (k+j)^p −
(k+j)` in `𝔽_p`, `φ ≡ (k+j)² (mod (k+j)⁶)` at every pole `−j` simultaneously, while
`deg φ = 2p ≤ 4n+2` keeps `φ R_n` decaying at ∞, so a residue-sum argument on `ℙ¹` forces
`w_n ≡ 0`.

### Canonical theorems (`Cbcert.Main`)

| Lean name | statement | meaning |
|---|---|---|
| `res_congruence_w` | `res p (w n) = 0` | `p ∣ w_n` |
| `res_congruence_wt` | `res p (wt n) = 0` | `p ∣ w̃_n` |
| `res_congruence_pn` | `res p (pn n) = 0` | `p ∣ p_n` (**CB₁**) |
| `w_congruence` | `w n = 0 ∨ 1 ≤ padicValRat p (w n)` | faithful `padicValRat` form |
| `wtilde_congruence` | `wt n = 0 ∨ 1 ≤ padicValRat p (wt n)` | " |
| `pn_valuation` | `pn n = 0 ∨ 1 ≤ padicValRat p (pn n)` | " |

`res p x := (x.num : ZMod p) * (x.den : ZMod p)⁻¹` is the residue of a `p`-integral rational;
`res p x = 0` is exactly "`p` divides `x`". The disjunctive `padicValRat` form is honest about
Mathlib's `padicValRat p 0 = 0` convention (see `Defs.lean` — the original non-disjunctive
phrasing was subtly unsound, a statement error caught by formalization).

### Proof architecture (one file per layer)

| module | role |
|---|---|
| `Defs.lean` | concrete computable `a_{i,j}`, `ã`, `w/w̃/u/ũ/v/ṽ/p_n`, `H`, `E_M` |
| `Certificate.lean` | **Lemma B** — the three-term certificate `= δ_{i,3}` over `ZMod p` |
| `PartialFraction.lean` | the cleared PF identity `pf_cleared` for all `n` (the `a_{i,j}` are the PF coefficients) |
| `Decay.lean` | **Lemma A** — `E_M(a) = E_M(ã) = 0` (Laurent decay of `R_n`, over `ℚ⟦X⟧`) |
| `Integrality.lean` | **Lemma C** — `p`-integrality of `a, ã, H` (cores need `j ≤ n`, `p ≠ 2`) |
| `Main.lean` | residue map + `ZMod p` reordering ⇒ the canonical theorems |

### Human-verification recipe

1. **Match to the paper.** In `worthiness/cb_certificate.tex`: Theorem (main result) ↔
   `res_congruence_w`/`res_congruence_wt` (and Prop. 1 ↔ `res_congruence_pn`); the certificate
   `φ = (k^p−k)²` ↔ `Certificate.certificate`; the decay relations `E_M = 0` ↔ `Decay.decay_a`;
   `R_n = Σ a_{i,j}/(k+j)^i` ↔ `PartialFraction.pf_cleared`.
2. **Build and audit axioms:**
   ```bash
   cd cbcert
   lake build
   lake env lean -c /dev/stdin <<< 'import Cbcert.Main
   open Cbcert
   #print axioms Main.res_congruence_w
   #print axioms Main.res_congruence_wt
   #print axioms Main.res_congruence_pn
   #print axioms Main.w_congruence
   #print axioms Main.pn_valuation'
   ```
   Each must read `[propext, Classical.choice, Quot.sound]`.
3. **Confirm zero sorries / no `native_decide`:**
   ```bash
   grep -rnE '\bsorry\b|native_decide|admit' Cbcert/*.lean | grep -v '/-'   # (only prose in docstrings)
   ```
4. **Numeric cross-check** (optional): `Cbcert/Numeric.lean` reproduces the closed forms at
   `n = 2, 3` against `worthiness/lemma_cb_explore.py` (`all_data`), and exhibits nonvanishing
   at `n = 3`. The scope note: general nonvanishing of `w_n, w̃_n, p_n` is an explicitly-open
   mini-campaign (see `PROGRESS.md`).

---

## Finite-range corrected law — `12·d_n⁵·P_n ∈ ℤ`, kernel-verified per `n`

**Modules:** `Cbcert/FiniteLaw.lean` (definitions + reduction tactic),
`Cbcert/FiniteLaw/N⟨n⟩.lean` (**one file per `n`**), `Cbcert/FiniteLaw/All.lean`
(aggregate). Sorry-free, **no `native_decide`** (pure kernel reduction via
`norm_num`); axioms `[propext, Classical.choice, Quot.sound]`. Generator +
ground-truth gate + remote driver in `scripts/`.

### What it proves

The Brown–Zudilin paper's experimental `d_n⁵·P_n ∈ ℤ` is false at `n = 2` (see the
Error exhibit below); the **corrected law** is `12·d_n⁵·P_n ∈ ℤ`, where
`P_n = (−1)^{n+1}·p_n/C(2n,n)` is built from the project's **canonical** `pn`
(`Cbcert/Defs.lean`, reduced through `Bseries`/`acoeff`) and `d_n = lcm(1,…,n)`
(`Cbcert/ErrorExhibit.lean`). Each `Cbcert/FiniteLaw/N⟨n⟩.lean` proves, for its `n`:

| Lean name | statement |
|---|---|
| `pn_val_⟨n⟩` | `pn n = ⟨exact rational⟩` (the expensive canonical kernel reduction) |
| `pn_ne_zero_⟨n⟩` | `pn n ≠ 0` (free byproduct; sharpens `Main.pn_valuation`'s disjunct at `n`) |
| `law_⟨n⟩` | `CorrectedLaw n` := `∃ m : ℤ, 12·d_n⁵·P_n = m` (integer witness `m` supplied literally) |

The aggregate (`Cbcert/FiniteLaw/All.lean`):

| Lean name | statement |
|---|---|
| `law_upto` | `∀ n ∈ Finset.Icc 2 8, CorrectedLaw n` (**verified range `n = 2 … 8`**) |
| `pn_ne_zero_upto` | `∀ n ∈ Finset.Icc 2 8, pn n ≠ 0` |

The witnesses `m` are computed in exact `Fraction` arithmetic by `scripts/l5_gen.py`
and inlined, so the kernel only *checks* the equation (checking ≪ deciding). The
`12` is sharp (the `{2,3}`-ceilings; `worthiness/CONJECTURE.md`).

### Extending the range (more `n`, more machines)

The per-`n` files are independent leaves, so a range splits trivially across cores
or hosts. **Locally:**

```bash
cd cbcert
python3 scripts/l5_gate.py 2 30          # exact-arithmetic gate: is 12·d_n⁵·P_n ∈ ℤ? (must PASS)
python3 scripts/l5_gen.py 9 12           # emit Cbcert/FiniteLaw/N9..N12.lean (witnesses inlined)
# add `import Cbcert.FiniteLaw.N9 … N12` to All.lean and bump the `Icc 2 8` bound in law_upto
lake build Cbcert.FiniteLaw.All          # -j1 recommended: each heavy n peaks ~7 GB RSS
```

Cost is compute-bound by the `native_decide` ban: `norm_num` kernel reduction of
`pn n` grows ≈ 1.8×/step (`n=3` ≈ 90 s, `n=5` ≈ 6 min, `n=8` ≈ 35 min on this box).
Pick `N` so the sequential build fits your budget; `n=2..8` is ≈ 75 min.

**On another machine** (remote driver — installs elan + toolchain, gets the Mathlib
cache, generates + builds the assigned range, rsyncs results back):

```bash
cd cbcert
scripts/l5_remote.sh HOST NSTART NEND [JOBS]     # e.g. scripts/l5_remote.sh kbld 9 16 4
```

Point `HOST` at `kbld` once its SSH credentials exist (until then the script simply
fails to connect — it does not assume kbld is reachable). After it rsyncs the
`N⟨n⟩.lean` back, wire the new imports into `All.lean` and `git add` the range.

### Human-verification recipe

1. **Gate independently:** `python3 scripts/l5_gate.py 2 24` — reproduces `12·d_n⁵·P_n`
   in exact arithmetic and asserts it is an integer for every `n` (adapts
   `worthiness/lemma_cb_explore.py`'s `all_data`). Any non-integer would falsify the
   corrected law.
2. **Build + audit axioms:**
   ```bash
   lake build Cbcert.FiniteLaw.All
   lake env lean -c /dev/stdin <<< 'import Cbcert.FiniteLaw.All
   open Cbcert.FiniteLaw
   #print axioms law_upto
   #print axioms law_8'
   ```
   Each must read `[propext, Classical.choice, Quot.sound]`.
3. **No `sorry` / `native_decide`:** `grep -rnE 'sorry|native_decide|admit' Cbcert/FiniteLaw*` (docstring hits only).

---

## Error exhibit — a construction-derived integrality error in arXiv:2210.03391

**Module:** `Cbcert/ErrorExhibit.lean` (self-contained, `n = 2` only, sorry-free,
no `native_decide`; every main theorem uses only `[propext, Classical.choice, Quot.sound]`).

### What it exhibits

F. Brown and W. Zudilin, *On cellular rational approximations to ζ(5)*, arXiv:2210.03391
(17 Oct 2022, **revised 26 Jan 2026**), state an **experimental** inclusion (eq. `dn-totsym`):

> Based on an extensive computation … we observe experimentally that
> `Qₙ, dₙ² d₂ₙ P̂ₙ, dₙ⁵ Pₙ ∈ ℤ` for `n = 0,1,2,…`, where `dₙ = lcm(1,…,n)`.

and, right after eq. `I_n`, they **display** the exact value `P₂ = 1190161/384` (and the
companion `P̂₂ = 344923/96`, `Q₂ = 2989`).

But `d₂ = lcm(1,2) = 2`, so `d₂⁵ = 32` and

```
32 · 1190161/384 = 1190161/12 ∉ ℤ.
```

The paper's own displayed value violates its own displayed inclusion at `n = 2`. The
failure factor is exactly `12 = 2²·3`, and `12` is the sharp fix (repo audit,
`worthiness/CONJECTURE.md`). The ζ(3)-companion fails by exactly `2`:
`d₂² d₄ · P̂₂ = 48 · 344923/96 = 344923/2 ∉ ℤ`.

### Derived, not hardcoded

`P₂` and `P̂₂` are **not** set equal to the printed rationals. They are built through the
construction and only then *proved* equal to the displayed values:

1. `ac i j` — candidate partial-fraction coefficients `a_{i,j}` of the paper's rational
   function `R₂(k) = 16(k+1)(k−1)(k−2)(k+3)(k+4)/(k(k+1)(k+2))⁶`.
2. `pf_cert` — a cleared-denominator **polynomial identity** (proved by `ring`) certifying
   that `ac` really are the partial-fraction coefficients of `R₂`.
3. `atc, Hh, w, wt, u, ut, vv, vt` — the companion coefficients `ã_{i,j}`, harmonic sums,
   and the linear-form building blocks (all per `SPEC.md`).
4. `pc = wt·vv − w·vt` (Zudilin `p₂`), `phc = u·vt − ut·vv` (companion `p̂₂`).
5. `P₂ = −pc/6`, `Phat₂ = −phc/6` (the identity `Pₙ = (−1)ⁿ⁺¹ pₙ / binom(2n,n)` from the
   Zu02 correspondence displayed just after eq. `dn-totsym`).

### Theorems

| Lean name | statement |
|---|---|
| `pf_cert` | `R₂ = Σ a_{i,j}/(k+j)^i` (cleared, certifies `ac`) |
| `P2_eq` | `P₂ = 1190161/384` (**derived**) |
| `Phat2_eq` | `Phat₂ = 344923/96` (**derived**) |
| `Q2_eq` | `−(u·wt − ut·w)/6 = 2989` (sanity anchor) |
| `bz_inclusion_fails` | `¬ ∃ m : ℤ, (d 2)⁵ · P₂ = m` |
| `clearing_iff` | `∀ c, (∃ m : ℤ, c · (d 2)⁵ · P₂ = m) ↔ 12 ∣ c` |
| `companion_inclusion_fails` | `¬ ∃ m : ℤ, (d 2)² · (d 4) · Phat₂ = m` |
| `companion_clearing_iff` | `∀ c, (∃ m : ℤ, c · (d 2)² (d 4) · Phat₂ = m) ↔ 2 ∣ c` |

### Human-verification recipe

1. **Open the PDF next to the Lean file.** In arXiv:2210.03391 (rev. 26 Jan 2026): check
   eq. `dn-totsym` (the `dₙ⁵ Pₙ ∈ ℤ` inclusion, stated experimentally) and the displayed
   values just after eq. `I_n` (`P₂ = 1190161/384`, `P̂₂ = 344923/96`, `Q₂ = 2989`).
2. **Match them to the Lean.** Displays ↔ `P2_eq`, `Phat2_eq`, `Q2_eq`; inclusion ↔
   `bz_inclusion_fails` / `companion_inclusion_fails`; the sharp correction ↔ `clearing_iff`
   / `companion_clearing_iff`. Every definition/theorem carries a docstring with the paper's
   equation label.
3. **Build and audit axioms:**
   ```bash
   cd cbcert
   lake build Cbcert.ErrorExhibit
   ```
   The build prints `#print axioms` for all seven theorems; each must read
   `[propext, Classical.choice, Quot.sound]`. Confirm no `sorry`/`native_decide`:
   ```bash
   grep -nE 'sorry|native_decide|admit' Cbcert/ErrorExhibit.lean   # only docstring hits
   ```
4. **Reproduce the arithmetic independently** (optional): the exact construction chain is in
   `worthiness/lemma_cb_explore.py` (`all_data(2)`); the error finding is in
   `worthiness/CONJECTURE.md`.
