# cbcert — Lean 4 formalizations around the Brown–Zudilin ζ(5) work

Lake project (Lean `v4.33.0-rc1`, Mathlib pinned). Two strands live here:

- **Frobenius-certificate theorem** (Tier 1, in progress) — see `SPEC.md`, `PROGRAM.md`,
  `PROGRESS.md`.
- **Error exhibit** (complete) — `Cbcert/ErrorExhibit.lean`, documented below.

Build everything and run the axiom audit:

```bash
cd cbcert
lake build            # green; prints the #print axioms lines for the exhibit
```

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
