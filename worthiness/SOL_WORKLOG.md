# SOL_WORKLOG — Phase 2 continuation (append-only)

## 2026-07-20 — session start

- Read, in required order, `SOL_RESUME_BRIEF.md`, `PHASE2_SALVAGE_VERIFY.md`, and
  `PHASE2_SOL_SALVAGE.md`.
- Accepted corrected conventions: the normalized recurrence is
  `c0(n)Y_n+c1(n)Y_{n+1}+c2(n)Y_{n+2}+c3(n)Y_{n+3}=0`, with
  `c3(n)=2(n+3)^5(2n+5)a0(n)` and
  `a0(n)=41218n^3+198849n^2+320790n+173057`; the corrected Casoratian is the
  formula in `PHASE2_SALVAGE_VERIFY.md` V5.
- The generic operator-desingularization route is refuted by the `Ph` ladder.
  The sole target retained is solution-specific regularity of `P` (and, as a
  companion diagnostic, `Q`) at the factors `(2n+5)a0(n)`, equivalently the
  descent (D).
- Verification status at entry: all cited grids are exact finite evidence, not
  proofs. No new theorem is claimed yet.
- Immediate program: inspect the existing Phase-1/Dwork machinery and exact
  formulas; search for a local rank-2 quotient or wedge identity at the linear
  and cubic singular factors; falsify candidate identities in exact arithmetic
  before attempting a proof or certificate statement.

## 2026-07-20 — first structural reduction and midpoint residue

- Inspected `dwork_vecform.py`, `dwork_hw.py`, `lemma_cb_band_v4.py`,
  `lemma_cb_band_v5.py`, `zeta7_dwork.tex`, and the negative `PHASE2_L2SPAN.md`
  result. The live cancellation is bilinear/projective; the old iterated linear
  `E_M` span is known not to force it.
- Derived the division-free last-row candidate, for `n=ap+r`, `0<=r<p`:

      p^5 P_{ap+r} = P_a (Q_r + E_{n,p}),   E_{n,p} in Z_p.

  This is certificate-shaped: the per-`(n,p)` witness is
  `E_{n,p}=p^5 P_n/P_a-Q_r` (when `P_a != 0`), and the small uniform input is
  `Q_r in Z`. It immediately implies (D). Conversely, (D) implies this witness
  is integral, so this is a structured restatement, not yet a proof.
- Exact finite evidence (ad hoc checker, to be made durable in `sol_*.py`): for
  every prime `5<=p<=29` and every `p<=n<=60`,
  `v_p(p^5 P_n-P_floor(n/p) Q_(n mod p)) >= v_p(P_floor(n/p))`; zero failures.
  On the single-digit subgrid `floor(n/p)<p`, the unrelative difference itself
  always had valuation at least 1. **Status: exact finite verification only.**
- Computed the recurrence row modulo the midpoint factor. Exact polynomial
  division gives

      128(c0,c1,c2) mod (2n+5)
        = 7 (11907, -334374, -19292).

  Hence at a simple midpoint prime `p | 2m+5`, after scaling
  `P_{m+i}=p^e x_i`, `e=min_i v_p(P_{m+i})`, solution-specific regularity is
  the fixed three-term residue identity

      11907 x0 - 334374 x1 - 19292 x2 = 0  in F_p

  for `p != 7` (for `p=7` the unreduced row has an automatic extra factor 7
  and must be treated at the next digit). This is a genuinely small uniform
  identity and the right certificate shape for the midpoint component.
- For the cubic component, reduction of `(c0,c1,c2)` modulo `a0(n)` produces a
  degree-at-most-2 row; its common denominator is
  `688444586089376 = 2^5*37^5*557^2`. Thus it is a valid uniform residue row
  for primes other than `37,557`; `p=37` has no root of `a0` modulo 37, while
  `p=557` has the root 49 and needs a separate direct row. Full coefficients
  will be recorded by the durable checker. No regularity claim is proved yet.

