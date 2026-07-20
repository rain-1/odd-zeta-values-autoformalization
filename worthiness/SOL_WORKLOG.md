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

## 2026-07-20 — durable local checker and quotient test

- Added `worthiness/sol_local_regular.py`. It asserts the polynomial remainder
  identities exactly and runs all valuation tests with `Fraction`/integer
  arithmetic. Run at cache limit `N=60`: all assertions passed.
- Full local inequality (LR), over every prime `p>=5` dividing
  `(2m+5)a0(m)` for `0<=m<=57`: 202 `(m,p)` rows. `Q`: 0 violations; `P`: 0
  violations; `Ph`: 28 violations. There are 14 rows with total singular
  multiplicity >1, and the full required multiplicity was used. **Finite exact
  evidence, not proof.**
- Small residue rows: midpoint fixed row, 56 tested rows: `P,Q` 0 violations,
  `Ph` 26; cubic degree-2 row (excluding denominator primes 37,557), 137 tested
  rows: `P,Q` 0 violations, `Ph` 1. **Finite exact evidence, not proof.**
- Division-free Frobenius last row, all primes `5<=p<=59` and `p<=n<=60`:
  480 rows, 0 violations of
  `v_p(p^5 P_n-P_a Q_r)>=v_p(P_a)`; minimum relative slack 0. **Finite exact
  evidence, not proof.** The implication of this witness-integrality statement
  to (D) is elementary and rigorous.
- Tested the proposed mod-`p` regular two-plane by independently primitive-
  scaling the three consecutive `Q` and `P` vectors. They are independent in
  140/202 singular rows but proportional in 62/202. Therefore a naive
  `F_p` rank-2 quotient is **not** uniform; the weight-filtered regular lattice
  can collapse to rank 1 on reduction. Any quotient proof must retain higher
  `p`-adic jets / saturation. This falsifies the simplest reading of suggested
  route (a), but not a filtered-lattice version.
- Extended the existing `dwork_hw.py` head-window expression experimentally
  from its upper half-band to all residues `0<=r<p`: for
  `p=5,7,11,13,17,19,23,29`, its valuation is uniformly at least 4 (at least 5
  for every `p>=11`), with no failures. **Finite exact evidence only.** This
  puts the midpoint residues (which lie just below the reflection centre) inside
  the same a=1 block identity; proving that uniform head-window identity remains
  a plausible concrete route to the last-row witness.

## 2026-07-20 — filtered Frobenius row and finite singular-gate reduction

- Extended the exact cache from `n=60` to `n=75` (cache file is gitignored) and
  reran `sol_local_regular.py 75`:
  - full (LR): 261 singular `(m,p)` rows; `P,Q` 0 violations, `Ph` 33;
  - MID1: 72 rows, `P,Q` 0 violations; CUB1: 179 rows, `P,Q` 0 violations;
  - weak last-row witness for `P`: 737 rows, 0 violations, minimum relative
    slack 0. **All are finite exact evidence only.**
- Tested the stronger filtered diagonal congruences

      p^w Y_{ap+r} / Y_a = Q_r (mod p),
      (Y,w)=(P,5),(Ph,3),

  in division-free valuation form. For `Ph`: 737/737 pass. For `P`: 736/737
  pass; the sole defect is `(n,p,a,r)=(19,7,2,5)`, where the error divided by
  `P_a` is a 7-adic unit (residue 4). The weaker integral-witness form still
  passes exactly and proves (D). Extending from 60 to 75 introduced no further
  defects. **Finite exact evidence only.**
- The defect has a precise recurrence explanation. Since every `c_i(n)` is an
  integer polynomial, `c_i(ap+r) == c_i(r) (mod p)`. Therefore inside a digit
  block the scaled `P` row and the `Q` row obey the same recurrence modulo `p`
  at every ordinary residue `r` with `c3(r)` a unit. Congruence propagates from
  three initial values until a residue root of
  `c3(r)/(2(r+3)^5)= (2r+5)a0(r)` is crossed. There are at most four such gates
  per prime (one midpoint plus at most three cubic roots). For `p=7` the gate
  residues are `{1,2,6}`; the exceptional `P` defect at output `r=5` is injected
  exactly by the cubic gate at recurrence index `r=2`.
- **Rigorous conditional gate lemma (elementary recurrence algebra):** over a
  DVR of residue characteristic `p>=5`, once the first three scaled block values
  are integral, ordinary recurrence steps preserve integrality; once they are
  congruent to a comparison solution, ordinary steps preserve congruence.
  Hence only residues satisfying `(2r+5)a0(r)=0 mod p` require witnesses. This
  is not a proof of those witnesses, but it reduces each `(a,p)` block to at
  most four solution-specific gates plus three initial values. The gate rows
  are exactly MID1 and CUB1 recorded above, so the reduction has the requested
  per-`(n,p)` witness + small-uniform-identity shape.
- Important exceptional-lattice lesson: the clean diagonal congruence is
  stronger than (D) and can fail when `P_a` is highly p-divisible (the `p=7`
  row), while the integral regular-lattice condition survives. A proof must
  formulate the gate in saturated valuation form, not divide by `P_a` or insist
  on a globally diagonal mod-p row.

## 2026-07-20 — exact classification of singular residue gates

- Factored the exact cubic discriminant:

      disc(a0) = -178513008142644
               = -2^2 * 3^3 * 7^2 * 29^2 * 107 * 557 * 673.

  Thus for `p>=5` the cubic roots are simple outside the finite set
  `{7,29,107,557,673}` (with the leading coefficient also nonunit at 557).
- Computed the exact resultant with the midpoint factor:

      Res_n(a0(n),2n+5) = 241144 = 2^3 * 43 * 701

  up to the harmless orientation sign (`a0(-5/2)=-30143`). Hence midpoint and
  cubic gates are disjoint modulo every `p>=5` except `p=43,701`.
- The polynomial remainder identities work at full prime-power depth, not only
  mod `p`: writing `t=v_p(2m+5)`, the midpoint certificate for `p!=7` is exactly

      v_p(11907 P_m - 334374 P_{m+1} - 19292 P_{m+2}) >= e+t,
      e=min_i v_p(P_{m+i}),

  because the difference between `128(c0,c1,c2)` and seven times this fixed row
  is coefficientwise divisible by the *integer polynomial* `2m+5`. Likewise,
  away from `p=557` the cleared degree-2 cubic row is a uniform prime-power
  certificate with required depth `v_p(a0(m))` (the clearing denominator is a
  unit). These are exact equivalences/reductions once the other singular factor
  is a unit. At overlap primes `43,701`, depths must be added, so separate
  certificates are not by themselves enough; a combined gate is required.
- This isolates a finite exceptional-prime list for special local algebra:
  `{7,29,43,107,557,673,701}`. Prime 37 appears in the chosen cubic remainder
  denominator but has no root of `a0 mod 37`, so it creates no cubic gate.
  **These factorization and polynomial-remainder facts are rigorous exact
  algebra. The certificate divisibilities themselves remain unproved.**

## 2026-07-20 — session close

- Wrote signed `worthiness/PHASE2_FROM_SOL_2.txt` with the exact identities,
  conditional gate lemma, finite-evidence counts, honest open frontier, and the
  next-session first task.
- Final verification reran successfully:
  `python3 -m py_compile worthiness/sol_local_regular.py worthiness/sol_hw_allr.py`,
  `PYTHONPATH=worthiness python3 worthiness/sol_local_regular.py 75`,
  `PYTHONPATH=worthiness python3 worthiness/sol_hw_allr.py`, and
  `git diff --check`.
- The worktree also contains concurrent changes in `cbcert/Cbcert/Assembly.lean`
  and the pre-existing modified `worthiness/ct_run/barnes_long.log`; neither was
  touched or incorporated in this work.

