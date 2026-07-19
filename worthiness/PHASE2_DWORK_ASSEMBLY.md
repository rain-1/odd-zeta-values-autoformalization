# Phase-2 (DWORK): the Φ/Bell symbolic assembly, GATE, and relation-level P6

Worker note, 2026-07-19 (Opus, continuation of `PHASE2_DWORK_HW.md`).
Executes the coordinator's task: build Sol's eq 3–13 into one togglable expansion
of `Q_HW`, GATE it, run P6 at relation level, attempt the symbolic-in-r
cancellation, and reconcile with Sol's revised memo `PHASE2_HW_FROM_SOL.txt`.

Exact `Fraction` arithmetic. **HONESTY: finite exact checks on stated grids.**
Script: `dwork_assembly.py` (`python3 dwork_assembly.py {gate|p6|shift|p4|all} 13,17`).

---

## 0. The assembly (Sol eq 1, 9, 10 — exact, no truncation)

    a_{6,j} = B_j(0),  B_j(y)=y^6 R_n(y-j),
    D_t(j)  = (-1)^{t-1}(t-1)! [ (n/2-j)^{-t} + Σ_{m=1}^n(-j-m)^{-t}
                + Σ_{m=1}^n(n+m-j)^{-t} - 6 Σ_{m≠j}(m-j)^{-t} ],       (eq 9)
    a_{6-m,j} = a_{6,j}·Y_m(D_1..D_m)/m!,   Y_m = complete Bell poly.    (eq 10)

**Atom form.** The (m−j)-block splits (eq A) as `Σ_{m≠j}(m-j)^{-t} = H_{n-j}^{(t)}
+ (-1)^t H_j^{(t)}`, and for `n=p+r`, `j≤r`, every harmonic `H_M^{(t)}` with `M≥p`
exposes the **full-block atom** `H_{p-1}^{(t)}` via the block decomposition
(`dwork_assembly.harm_atom`, an exact mod-`p^N` reconstruction, mini-gated to
ord ≥ 9). The `H_{p-1}^{(t)}` are the objects the reversal identity (eq 13) /
Wolstenholme inputs (eq 12) govern; the assembly exposes them as **individually
substitutable symbols**.

---

## 1. GATE — the assembly reproduces the oracle (PASS)

| GATE | Result |
|---|---|
| Bell/D_t `a_{i,j}` (eq 9–10) == exact `base_coefficients` | **PASS** (1026 (i,j), 0 mismatch; central-zero branch handled by exact `B_j(0)`) |
| assembled `Q_HW` (Bell head-window Sing + exact u,w) == oracle | **PASS** exactly (through ord 6) |
| atom assembly (`Hp`=true `H_{p-1}`) == oracle `Q_HW` | **PASS mod p^6** (min ord(diff) = 9–10, band, p=13,17) |

The GATE is Sol's stage-3 invariant "exact agreement of direct `a_{i,j}` with
Φ/Bell reconstruction, including the central-zero branch." Everything below is
built on this verified model.

---

## 2. The weight-shift law (VERIFIED, 0 violations, full band p=13..29)

Perturbing a single full-block atom `H_{p-1}^{(t)} → H_{p-1}^{(t)} + p^s`
(injecting a unit error at p-adic digit `s`) changes the assembled `Q_HW` from its
true `ord 5` to **exactly `ord = s + t`**. Verified with **0 violations** for
`t=1,2,3`, `s=0,1`, every band `r`, `p ∈ {13,17,23,29}`.

> **WEIGHT-SHIFT LAW.** The weight-`t` full-block atom `H_{p-1}^{(t)}` enters
> `Q_HW` shifted by `t`: its digit at position `s` controls `Q_HW`'s digit at
> position `s+t` (unit coefficient). Hence `Q_HW`'s digit `c_k` depends on the
> atoms only through `{ [H_{p-1}^{(t)}]_{k-t} : 1 ≤ t ≤ k }`.

Consequences for the digit-ownership map (which drives P6):
- `c_0`: no `t≥1` reaches it → **atom-independent** (this is the E_M-forced digit, consistent with `lemma_cb_band_v4` C).
- `c_1`: only `[H_{p-1}^{(1)}]_0`.
- `c_2`: only `[H_{p-1}^{(1)}]_1` and `[H_{p-1}^{(2)}]_0`.
- higher weights `H_{p-1}^{(3,4,5)}` enter only `c_3, c_4, c_5, …` — **inert for the two "missing digits."**

---

## 3. P6 at relation level (Sol's prescribed protocol) — VERDICT

P6 run as Sol's revised memo prescribes: replace each full-block relation by an
independent symbol retaining/violating its valuation bound, and measure the
coefficientwise effect. Perturbing `H_{p-1}^{(t)}` from digit `s=0` upward
(`*` = below the eq-12 Wolstenholme valuation floor), uniform across p=13,17,23:

```
Hp[1] (floor e=2): *p^0:ord1  *p^1:ord2   p^2:ord3   p^3:ord4   p^4:ord5
Hp[2] (floor e=1): *p^0:ord2   p^1:ord3   p^2:ord4   p^3:ord5
Hp[3] (floor e=2): *p^0:ord3  *p^1:ord4   p^2:ord5   ...
Hp[4] (floor e=1): *p^0:ord4   p^1:ord5   ...
Hp[5] (floor e=2): *p^0:ord5   ...(inert for c_0..c_4)
```

> **P6 VERDICT (which ingredient owns which digit).**
> - `c_1 = 0` ⟺ `[H_{p-1}^{(1)}]_0 = 0`, i.e. **`H_{p-1}^{(1)} ≡ 0 (mod p)`**
>   (Fermat / weak Wolstenholme). Deleting it (`Hp[1]@p^0`) breaks `c_1` (ord→1).
> - `c_2 = 0` ⟺ `[H_{p-1}^{(1)}]_1 = 0` and `[H_{p-1}^{(2)}]_0 = 0`, i.e.
>   **`H_{p-1}^{(1)} ≡ 0 (mod p^2)`** (full Wolstenholme) **and
>   `H_{p-1}^{(2)} ≡ 0 (mod p)`**. Deleting either breaks `c_2`.
> - Weights `t=3,4,5` and the **reversal identity (13) are NOT involved** in the
>   two missing digits — they enter `c_3, c_4, …`.

**This corrects Sol's original (July-19) mechanism** (`ZETA7_DWORK_FROM_SOL.txt`
§1.7): the p¹ digit does **not** vanish "via the reversal identity coupling
`H_1/H_2` and `H_3/H_4`"; it vanishes by plain **weight-1 Wolstenholme**, with no
reversal relation and no `H_3/H_4`. The p² digit uses weight-1 (mod p²) and
weight-2 (mod p) Wolstenholme — again no reversal. Sol's revised memo
`PHASE2_HW_FROM_SOL.txt` independently retracts the two-digit picture in favour of
one weight-5 identity; the P6 map here is the exact relation-level confirmation
he requested and pins the per-digit ownership he left open.

### 3.1 The non-atom residue (the honest gap)

P6 isolates the **necessity** of the Wolstenholme valuations, not full
**sufficiency**. `Q_HW`'s digits also depend on parts NOT among the full-block
atoms:
- the **r-dependent weight-2 interval sum** `H_r^{(2)}`: perturbing it moves `c_2`
  (ord→2) — so `c_2 = 0` also needs a genuine cancellation of this interval sum
  against the `a_6`/`u`/`w`/constant terms (`C_residue` test; weight-1 interval
  sums are inert for `c_1,c_2`).
- the fixed `u, w` full sums and the `a_6` block-binomials.

So the precise reduction is: `c_1 = 0` needs `H_{p-1}^{(1)}≡0 (mod p)` **plus** a
residual `C_1 = 0` (the `u,w↔Sing` digit-1 balance; `c_1` has no interval-sum
dependence, so `C_1` is the `a_6`/`u`/`w`/E_M part); `c_2 = 0` needs the two
Wolstenholme congruences **plus** the weight-2 interval-sum cancellation
`C_2 = 0`. `C_1, C_2` are measured 0 for all band `r` but are **not** closed
symbolically here — they are the residual open content (Sol's "block-binomial +
Bell + r-dependent chamber summation" work, his three named hard points).

---

## 4. Symbolic proof status, per digit

| digit | status |
|---|---|
| `c_0` | forced by the E_M window relations (prior work `lemma_cb_band_v4` C) |
| `c_1` | **reduced** to `H_{p-1}^{(1)} ≡ 0 (mod p)` (Wolstenholme) **+ residual `C_1=0`** (the u,w↔Sing balance; measured 0, not closed) |
| `c_2` | **reduced** to `H_{p-1}^{(1)}≡0 (mod p^2)`, `H_{p-1}^{(2)}≡0 (mod p)` **+ residual `C_2=0`** (weight-2 interval-sum cancellation; measured 0, not closed) |
| `c_3, c_4` | analogous, additionally invoking `H_{p-1}^{(3,4)}` (weight-shift law) — not analysed in detail |
| `c_5` | first genuinely non-vanishing coefficient (the occasional ord-6 rows are extra roots of `c_5`; Sol's revised max-order claim) |

**No digit is fully closed symbolically.** The Wolstenholme half of `c_1,c_2` is
proved (classical); the residual chamber/interval cancellation is not. This is
the honest boundary — the same one Sol's revised memo names as open.

---

## 5. P4-revised (Sol `PHASE2_HW_FROM_SOL` T2) — tested

Sol's corrected P4: only the reflection-centre boost survives; proposal
`c(r) ∈ ideal (x, h_2, h_4)`, `x=2r+1−p`, `h_t = H_r^{(t)} mod p`.

Tested exact, p=13..41:
- **`c(centre r=(p−1)/2) = 0`: CONFIRMED** every prime (the surviving boost).
- **Old antisymmetry DEAD: CONFIRMED** — `c(r)+c(p−1−r) ≠ 0` generically
  (e.g. 36/41 residues at p=41, matching Sol's "40 of 41" up to the r-range
  convention).
- **True variety** `{x=h_2=h_4=0}` = `{centre}` only, no violations.
- **Ideal form NOT verified / NOT falsified.** As functions over `F_p`, `c ∈ (x)`
  is trivial (x has a simple zero at the centre where `c` vanishes), so
  membership carries no content; the content is Sol's *weight-bounded harmonic*
  `A,B,C`. My polynomial-in-r fit `c = xA+h_2B+h_4C` (deg A,B,C ≤ 2) is
  **not solvable** — consistent with `A,B,C` being harmonic expressions in
  `h_1,h_3,h_5` (Sol's alphabet), which my basis cannot represent. A proper test
  needs the symbolic harmonic-alphabet reduction (Gröbner in the harmonic
  generators), which the current assembly does not produce.

VERDICT P4-revised: centre-vanishing confirmed; the ideal-membership structural
claim is untested (needs the harmonic-symbol assembly, not numeric interpolation).

---

## 6. Reconciliation with Sol's revised memo `PHASE2_HW_FROM_SOL.txt`

Sol's memo (written in parallel, responding to my ord≥5 and P4 findings) and this
assembly **converge**:
- **mod p⁵, not mod p³.** Sol retracts the two-missing-digit picture: `Q_HW` is
  one weight-5 identity `C_0=…=C_4=0`, `ord_p(Q_HW)=5` generic. This is exactly my
  measured ord≥5 (`dwork_hw.py`). AGREE fully; I discovered it, he revised to it.
- **P4.** Sol kills the linear factor and (in his convention) global antisymmetry,
  keeping only the centre boost in a "centre-ideal" form. My tests confirm both
  the death and the surviving centre-vanishing.
- **P6 protocol.** Sol prescribes "delete reversal = replace by independent
  full-block symbols retaining valuation bounds." My atom-perturbation is exactly
  that, and returns the per-digit ownership he left open.
- **Refinement/correction I add:** the reversal identity (13) is **not** the
  mechanism for `c_1,c_2`; the **weight-shift law** shows each `c_k` is owned by
  the weight-≤k Wolstenholme *valuations*, and reversal (a cross-weight relation)
  only matters once weights 3–5 enter `c_3,c_4`. So "impose reversal through
  weight 5" is right for the *full* jet but overstated for the two low digits.
- **Open, both agree:** a symbolic-in-r proof of `Q_HW ≡ 0 (mod p^5)` (the
  residual `C_k=0` chamber/interval cancellations), and the regular-residual +
  companion + q-coordinate + general-a steps needed to turn the head-window
  statement into the full denominator-free descent (Sol T1 last paragraph — the
  mod-p⁵ head-window result is a *shadow* of, not equivalent to,
  `ord_p(Δ_5) ≥ ord_p(q_1)+2`).

---

## 7. Bottom line

- **GATE: PASS.** The Φ/Bell atom assembly reproduces the oracle `Q_HW` exactly
  (mod p⁶); the model is faithful, with the full-block atoms `H_{p-1}^{(t)}`
  individually togglable.
- **Weight-shift law: VERIFIED** (0 violations) — `H_{p-1}^{(t)}` digit `s`
  ↦ `Q_HW` digit `s+t`. This is the clean structural spine of the cancellation.
- **P6: EXECUTED at relation level.** `c_1` owned by `H_{p-1}^{(1)} mod p`; `c_2`
  by `H_{p-1}^{(1)} mod p²` and `H_{p-1}^{(2)} mod p`. **The reversal identity and
  weights ≥3 are not involved in the two low digits** — a correction to Sol's
  original mechanism, matching his revised memo's spirit.
- **Symbolic proof: partial.** The Wolstenholme half of `c_1, c_2` is reduced to
  classical congruences; the residual non-atom cancellation `C_1=C_2=0` (u,w↔Sing
  balance and the weight-2 interval sum) is measured 0 but **not closed** — the
  honest residue, coinciding with Sol's stated open points.
- **P4-revised:** centre-vanishing confirmed; the `(x,h_2,h_4)` ideal form
  untested (needs symbolic harmonic reduction).
