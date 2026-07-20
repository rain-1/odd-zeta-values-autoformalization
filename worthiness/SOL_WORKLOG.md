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

## 2026-07-20 — session 3 start: a=1 midpoint gate only

- Accepted the session-2 handoff and the independent falsification extension:
  the cached exact ladders now run through `n=360`; the law and (D) have zero
  violations on the stated grid, including both accessible `k=3` bands.  This
  is exact finite evidence, not proof, and the cache will be loaded rather than
  regenerated.
- Incorporated the refinement at `(n,p)=(306,7)`: `a0`-apparency is a target
  specific observation for `P` only.  `Q` loses one 7-adic order there and is
  used below only through its already established integer/Lucas role.
- Fixed the sole task to the generic a=1 midpoint row.  For odd prime `p`, set
  `r=(p-5)/2`, `N=p+r=(3p-5)/2`; then `2N+5=3p`, so the desired simple-gate
  certificate (outside the stated exceptional set) is

      v_p(11907 P_N-334374 P_{N+1}-19292 P_{N+2}) >= e+1,
      e=min_{0<=s<=2} v_p(P_{N+s}).

- Recovered the exact determinant bookkeeping omitted by the old scalar
  head-window test.  If `v=Sing+R`, `vt=Singt+Rt` and
  `E=p^5 Sing-rho_1 u-sigma_1 p^2 w` (with tilded analogue), then exactly

      p^5 p_N-rho_1 q_N = wt_N E_N-w_N Et_N
                             +p^5(wt_N R_N-w_N Rt_N).

  Thus both regular residuals must remain separate until the determinant is
  formed; proving the scalar head errors alone cannot prove the midpoint row.

## 2026-07-20 — midpoint determinant assembly and chamber split

- Added `worthiness/sol_midpoint_gate.py`.  Its `cache` mode loads (and never
  regenerates) `falsify_data/ladder_P.json`.  Its `assembly` mode extends the
  Bell reconstruction to all pole positions, derives the companion array,
  emits both regular residuals, and retains the chambers
  `[0,r_s]`, `[r_s+1,p-1]`, `[p,p+r_s]` separately at each of the three levels
  `N+s` (`r_s=(N+s)-p`) until the determinant is formed.
- The even-level central-zero branch cannot use `a_6 Y_m`: its logarithmic
  derivatives have a pole although `B_j` is regular.  The checker therefore
  uses the direct Taylor coefficient at exactly that one index and asserts
  Bell=direct at every noncentral index.  This is an exact handling of the
  branch, not a cancellation of zero times infinity.
- Proved the bookkeeping identity (pure algebra) and asserted it exactly in the
  checker.  With `alpha_s=R_s(-1)^(N+s+1)/C(2(N+s),N+s)` and
  `(R_0,R_1,R_2)=(11907,-334374,-19292)`, one has

      p^5 M = rho_1 sum_s alpha_s q_(N+s)
              + sum_s alpha_s(wt E-w Et)_(N+s)
              + sum_C sum_s alpha_s p^5(wt R_C-w Rt_C)_(N+s),

  where `M=sum_s R_s P_(N+s)` and `C=head,middle,tail`.  Every equality is
  over `Q`, before taking valuations.
- Also reduced the tail chamber exactly by `j=N+s-b` using the proved
  reflection laws for both arrays,

      a[i,N+s-b]=(-1)^(i+1)a[i,b],
      at[i,N+s-b]=(-1)^(i+1)at[i,b].

  Consequently `R_head+R_tail` is the explicit single head sum with kernel
  `H_b^(i)+(-1)^(i+1)(H_(N+s-b)^(i)-p^(-i))`; the checker asserts this for the
  untilded and tilded residuals separately before taking their determinant.
- Exact assembly at `p=11,13,17,19,23,31,37` passed every gate: Bell coefficients,
  central branch, direct residual decomposition, scalar `E,E~` agreement with
  `sol_hw_allr.error`, determinant identity, normalization, and equality with
  the committed ladder.  Here `e=-5` and the target scale in `p^5 M` is `p^1`.
  Relative valuations `v_p(piece)-1` were:

      q: 0; head determinant: 2 (3 at p=11);
      regular head/tail individually: -3 or -2;
      regular middle: 6 or 7;
      regular head+tail after reflection/determinant/three-level assembly: 5.

  Thus the dangerous regular chambers cancel by eight p-orders in the generic
  samples.  This cancellation is exact finite evidence; no uniform symbolic
  proof of its divisibility has yet been obtained.
- Cache-only midpoint sweep through `N+2<=360`, excluding the declared finite
  exceptional primes, tested 45 generic primes (`11<=p<=239`): zero witness
  violations, 44 exactly tight; `p=131` has one extra order.  In all 45 rows
  `e=-5`.  This extends beyond the falsification campaign's stated `p<=73`
  solely because the committed ladder itself contains every level through 360;
  it remains finite evidence.

## 2026-07-20 — session 3 verification and close

- Wrote `worthiness/PHASE2_MIDPOINT_GATE.md`, separating the rigorous algebraic
  reduction, the Q/Lucas component, exact finite evidence, and the four explicit
  remaining proof obligations.  In particular it does not infer Q-apparency
  from the Lucas row and does not advertise the observed chamber jump as a
  symbolic proof.
- Final cross-checks passed:
  `python3 -m py_compile worthiness/sol_midpoint_gate.py`;
  `PYTHONPATH=worthiness python3 worthiness/sol_local_regular.py 75`;
  `PYTHONPATH=worthiness python3 worthiness/sol_hw_allr.py`;
  and `PYTHONPATH=worthiness python3 worthiness/sol_midpoint_gate.py all
  --primes 11,13,17,19,23,31,37`.  The inherited checkers reproduced their
  session-2 counts exactly, and all new exact assertions passed.
- `git diff --check` passed.  Concurrent modified files
  `cbcert/Cbcert/Assembly.lean` and `cbcert/Cbcert/LucasRow.lean` were not touched
  or incorporated.

## 2026-07-20 — session 4 start: reflected midpoint determinant

- Resumed exactly from commit `fd94414` and accepted session 3 section 6 as the
  binding task.  Scope is the generic `a=1` midpoint only: prove `(RT)` first,
  then `(RM)`, `(H)`, and `(U)` if `(RT)` closes; no `p^t` or cubic-gate work.
- Preserved the pre-existing modified Lean files
  `cbcert/Cbcert/Assembly.lean` and `cbcert/Cbcert/LucasRow.lean`; session-4 work
  is confined to `worthiness/`.
- Re-ran the exact assembly oracle at `p=11,13,17` before symbolic changes.
  Every rational identity passed.  Relative to the required `p^1` scale in
  `p^5 M_p`, the reflected head+tail determinant has offset `5` at all three
  primes (absolute valuation `6`), while head and tail separately have offsets
  `-2,-3,-2`.  This reproduces the eight-order alarm and fixes the oracle
  baseline against which every subsequent symbolic layer will be checked.

## 2026-07-20 — exact Phi substitution and the local reflected-pair lemma

- Extended `sol_midpoint_gate.py` with an exact fixed-block factorial function
  `Phi(A,b)=(Ap+b)!` and the closed factorial form of `a_(6,b)`.  For
  `m=p+r_s`, `r_s=(p-5)/2+s`, `s=0,1,2`, every reflected-head term uses the
  carry-free blocks

      m!       = Phi(1,r_s),       (m+b)! = Phi(1,r_s+b),
      (2m-b)!  = Phi(2,2r_s-b),    (m-b)! = Phi(1,r_s-b),
      b!       = Phi(0,b).

  The checker asserts this exact `a_6` formula against both Bell and direct
  coefficients for every `0<=b<=r_s`, including `b=0,r_s`.
- Added `symbolic-rt` mode.  It forms the reflected kernel, both residuals,
  their determinant, and only then the coefficient row, and asserts exact
  equality with the chamber oracle.  At `p=11,13,17`, the assembled `(RT)` row
  has valuation `6`, exactly reproducing the session-3 alarm.  The raw Bell
  layers and raw endpoint pieces remain nonintegral, so no premature modular
  cancellation has been introduced.
- A second reflection inside the head, `b <-> r_s-b`, isolates the useful
  local bound.  For both `a` and `at`, and for every local pair (the endpoint
  pair `{0,r_s}` and a central singleton included), the exact floors at all
  three offsets are

      (layers 1+2, layer 3, layer 4, layer 5, layer 6)
        >= (-2, -2, -2, -1, 0).

  On the oracle primes the last two actual floors are `0,0`.  The same ledger
  passed at `p=19,23,31,37` without changing the proof target.
- The normalized algebra behind the only nontrivial local floors is now
  isolated.  Put `A_i(b)=p^(6-i)a_(i,b)` (and similarly `At_i`) and let `K_i(b)`
  be the reflected kernel.  For `c=r_s-b`, the needed jet identities are

      A_1(b)K_1(b)+A_1(c)K_1(c)
        +p[A_2(b)K_2(b)+A_2(c)K_2(c)] = 0 mod p^3,
      A_3(b)K_3(b)+A_3(c)K_3(c) = 0 mod p,

  with a singleton convention at `b=c`; identical identities hold for `At`.
  The second identity follows transparently from the Phi unit
  `a_6(c)=-a_6(b) mod p`, symmetry of the leading Bell collision jet, and
  `K_3(c)=K_3(b) mod p` (the singleton has `p|a_6`).  The first is the remaining
  three-digit Phi/Bell collection; the exact checker verifies its valuation at
  every local pair but a prime-independent written collection of its three
  coefficients is still required before `(RT)` can honestly be marked proved.

## 2026-07-20 — downstream RM/H/U oracle audit

- Added `rm-h-u` mode and ran it at `p=11,13,17`.  The middle residuals have
  valuations at least `4`, their level determinants after `p^5` have valuations
  `8,7,7`, and the three-level `(RM)` rows have valuations `8,7,7`.  This comes
  from the easy middle Phi count and is far above the needed floor.
- The head errors `E,Et` have valuation at least `5`; with `w,wt>=-2`, the
  head determinants have valuation at least `3`, and the `(H)` rows have
  valuations `4,3,3`.  This exactly matches `sol_hw_allr.py`; however the
  prime-independent weight-five Phi/Bell proof of `E,Et in p^5 Z_p` is the
  previously documented head-window identity and is not silently promoted
  from exact samples to a theorem.
- The exact leading-digit identity is

      p^5 P_(p+t) = (29/28) Q_(p+t) mod p

  in all nine audited levels.  The digit triples are respectively
  `[0,7,8]`, `[5,8,2]`, `[7,5,8]`, so at least one is a unit and `(U)` follows
  conditionally once `(RT),(RM),(H)` are theorems and the standard primitive
  `Q`-triple lemma is supplied.  No `p^t` or cubic-gate work was started.

## 2026-07-20 — session 4 verification and close

- Wrote signed `worthiness/PHASE2_FROM_SOL_4.txt`.  It records the exact Phi
  blocks, the local reflected-pair reduction, `(RM)`'s uniform valuation proof,
  and the honest open status of `J12`, `(H)`, and conditional `(U)`.
- Final verification passed:
  `python3 -m py_compile worthiness/sol_midpoint_gate.py`;
  `PYTHONPATH=worthiness python3 worthiness/sol_midpoint_gate.py all --primes
  11,13,17`; `PYTHONPATH=worthiness python3 worthiness/sol_local_regular.py 75`;
  `PYTHONPATH=worthiness python3 worthiness/sol_hw_allr.py`; and
  `git diff --check`.
- The midpoint cache still has 45/45 generic witnesses and 44 tight rows.  All
  new exact gates reproduced the assembly oracle.  The inherited checkers
  reproduced their session-3 counts exactly.
- The unrelated modified Lean files `cbcert/Cbcert/Assembly.lean` and
  `cbcert/Cbcert/LucasRow.lean` remain untouched and unincorporated.
