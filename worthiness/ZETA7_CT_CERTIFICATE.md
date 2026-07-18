# ζ(7) recurrence — creative-telescoping certificate: outcome

**Date:** 2026-07-17/18 (overnight run). **Status:** IN PROGRESS — updated on completion.

## Two routes run

1. **Period-level multi-sum CT (PRIMARY)** — discrete creative telescoping on the
   all-positive 6-fold Barnes series for the period I_n. Annihilates I_n itself
   (more valuable: it is the linear form Q_n·ζ(7)−P_n, so its recurrence is the
   Apéry-type operator directly). See "Barnes route" below.
2. **Diagonal continuous CT (FALLBACK)** — 8-variable CT on the W_lc window
   diagonal for the leading coefficient q_n. Paused after 2 of 8 eliminations
   (checkpoint at x8 preserved). See "Diagonal route" below.

## Objective

Upgrade the discovered ζ(7) leading-coefficient recurrence from *"certified
empirically against 70 exact terms"* to a **proven all-n theorem** by producing a
creative-telescoping (CT) certificate: a proven annihilating operator for the
diagonal q_n, obtained by integrating out all 8 integration variables of a
faithful window representation.

- **Target operator** (`worthiness/zeta7_q_recurrence.json`): order 4, degree 19,
  leading (characteristic) coefficients `[7381728, -46800155520, 501765579072,
  -46800155520, 7381728]` (palindromic). Empirically certified against 70 of the
  74 exact terms q_0…q_73. This operator was found by **guessing** (modular
  linear algebra + rational reconstruction), NOT yet proven.
- **A CT certificate proves the recurrence for all n.** Anything short of
  completing all 8 eliminations is progress data, labelled as such below.

## Representation

The unique **pure bandwidth-4** window representation of the ζ(7) diagonal among
the 41 low-coupling reps found (verified to reproduce all 31 known q_n, and here
against all 74 exact terms via the guessed operator):

    W_lc = {1,2}, {1,2,3,4}, {2,3,4,5}, {3,4,5}, {4,5,6}, {4,5,6,7}, {5,6,7,8}, {7,8}

Variable incidence: x4,x5 appear in 5 windows each (hot center); x1,x8 in 2;
x2,x3,x6,x7 in 3. No full-width coupler (unlike the MOS representation, whose
`{1..8}` window forced a 2nd-elimination blowup). This is the best available
model for CT — every other low-coupling rep contains a size-5 window.

## Method (validated in ZETA7_CT_COUPLING_REPORT.md)

Iterated `CreativeTelescoping` (one variable at a time), NOT monolithic Takayama.
Integrand `H = Exp[n·(Σ log W_i − Σ log x_j)] / ∏ x_j`; `ann = Annihilator[H, …]`
(instant); then eliminate x_1,…,x_8 in the order **x1, x8, x2, x6, x3, x7, x4, x5**
(low-incidence boundary first, hot center last). Checkpoint (DumpSave) after every
elimination. Licensed RISC/HolonomicFunctions 1.7.3 in a bash stdin kernel.

## Elimination tower (timings)

| step | var | time | #tele ops | ByteCount | note |
|---|---|---|---|---|---|
| 1 | x1 | 25 s | 8 | — | prior run |
| 2 | x8 | 931 s | 10 | 13.7 MB | prior run |
| 3 | x2 | _running_ | | | this run |
| 4 | x6 | | | | |
| 5 | x3 | | | | |
| 6 | x7 | | | | |
| 7 | x4 | | | | |
| 8 | x5 | | | | (hot center, last) |

_(table updated as the run progresses)_

## Barnes route (PRIMARY) — period-level multi-sum CT

The period admits an **all-positive 6-fold hypergeometric sum** (ZETA7_BARNES.md
§5f, `zeta7_barnes_num1.py`, verified to reproduce I₀,I₁,I₂):

    I_n = Σ_{a,b,c,d≥0} Σ_k Σ_j F(n; a,b,c,d,k,j)

with the inner indices k (from G₂) and j (from H₂) unfolded. Every factor of the
summand F is a Γ-ratio / binomial of an **integer-linear** form in the 7 variables
(n,a,b,c,d,k,j) ⇒ F is a **proper hypergeometric term in all 7 variables**. The
inner sums have natural boundaries (C(a+b,k), C(b+c,j) vanish outside range).

- **Transcription verified**: my Mathematica summand matches the validated Python
  summand exactly on 6 index tuples (exact rationals). (`ct_run/tcheck.wl`.)
- **Annihilator instant**: `Annihilator[F, {S[a],S[b],S[c],S[d],S[k],S[j],S[nn]}]`
  = 7 ops, 32 MB, 0 s. (Contrast: the continuous diagonal needed a 9-op start and
  a 931 s 2nd elimination.)
- **Iterated discrete CT**, elimination order k, j, d, c, b, a (inner indices
  first). Checkpoint after each. Script `ct_run/barnes_ct.wl`.

Tower timings (updated live):

| step | var | time | #tele | ByteCount |
|---|---|---|---|---|
| 1 | k | _running_ (>50 min, RSS ~2 GB) | | |
| 2 | j | | | |
| 3 | d | | | |
| 4 | c | | | |
| 5 | b | | | |
| 6 | a | | | |

If it completes, the telescoper is a **proven** recurrence for I_n; comparison
with the guessed q_n operator (`ct_run/compare_op.py`) then confirms the Apéry
operator and hence proves it for all n.

## Diagonal route (FALLBACK) — outcome

_(paused after x1, x8; see tower above; resume from ckpt at x8 if Barnes stalls)_
