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

## 2026-07-20 — session 5 start: J12

- Accepted the machine-verified `Q_lucas_frobenius` and conditional
  `descent_law` in commit `64ea13a`; the worktree was clean at entry.
- Kept the binding order from session 4: close J12 and hence `(RT)` before
  touching `(H)`, `(U)`, or assembly.
- Added `sol_j12.py`, a valuation-aware truncated Phi/Bell checker.  It uses
  `z` for the collision prime, keeps the kernel full-block quotients as
  independent symbols, and separately retains the endpoint and central
  branches.

## 2026-07-20 — J12 and RT closed

- With `delta_t=p^tD_t`, extracted the universal collision row

      (-13/2, 19/4, -55/4, 237/8, -669/4).

  The Bell values are `Y_5/5!=-287`, `Y_4/4!=287/2`, and the derivatives
  needed through degree two are recorded in `PHASE2_J12_CERTIFICATE.md`.
- Substitution of the required
  `E_d(x)=1+xpH_d+(x^2p^2/2)(H_d^2-H_d^(2)) mod p^3` gives, for `c=r-b`,

      A_1(c)=-A_1(b) mod p^3,
      A_2(b)-A_2(c)=-A_1(b) mod p^2,
      A_2(b)+A_2(c)=0 mod p.

  These are verified after denominator clearing in an independent symbolic
  harmonic alphabet, rather than inferred by interpolation.
- Collecting the reflected kernels makes all three J12 coefficients zero.
  The full-block kernel quotients cancel symbolically.  The exact companion
  formula reduces its coefficient row to zero as well.
- Kept `{0,r}` as a named endpoint branch.  For `b=c`, used the uncancelled
  factor `(m/2-b)=p/2`: the central collision row has `Y_5/5!=0`, so
  `A_1=0 mod p^3`, while `A_2` and `K_2` each gain the required factor.
- Required gates passed at `p=11,13,17`, all three offsets, all pairs, both
  arrays: coefficient triples `(0,0,0)` and exact-oracle valuation at least
  three in every row.
- Wrote `PHASE2_J12_CERTIFICATE.md`.  Together with the previously proved J3
  and elementary layers 4--6, J12 puts both reflected residuals in
  `p^-2 Z_p`.  Since `w,wtilde in p^-2 Z_p`, `(RT)` follows and is now proved.

## 2026-07-20 — five-digit H normal-form candidate isolated

- Reflected the full `u,w` corrections before expansion.  Uniformly, the
  middle corrections have valuation at least five.  On every audited row, each
  head pair `{b,r-b}` has valuation at least four; this isolates the candidate
  normal form in which digits `C_0,...,C_3` vanish locally and only the
  finite-field sum `sum_b C_4(b)=0` remains.
- Added `sol_h5.py`.  At `p=11,13,17`, all three offsets and both arrays, it
  asserts the exact reflected decomposition, the local `p^4` floor, the
  middle `p^5` floor, and prints the `C_4` residue list.  Every printed list
  sums to zero and the exact errors have valuation at least five.
- The prime-independent Phi/Bell proof of the local `p^4` floor and the
  summation certificate for `sum C_4=0` are not yet written.  Therefore `(H)`,
  `(U)`, and the complete a=1 midpoint theorem remain open and are not claimed.

## 2026-07-20 — session 6: weight-five reflection jet and H closed

- Resumed from `fc2a8d7` with the exact Session-5 frontier.  Rewrote the local
  head term using `A_i=p^(6-i)a_i` as the single Bell functional

      pT=A_1-A_2-(59/42)A_3-A_4-(15/14)A_5-A_6.

  This fixed row was asserted exactly in `sol_h5.py` before extracting digits.
- Expanded the fixed-block `Phi` products through weight five in the harmonic
  alphabet, retained the full-block quotients through pair collection, and
  obtained the prime-independent reflection jet

      T(b)+T(r-b) = -(p^4/84)
          (a^[r]_(1,b)+a^[r]_(1,r-b)) mod p^5,

  with the same formula for the companion.  Hence the five local coefficients
  are `(0,0,0,0,-a^[r]_1/84)` after pairing.
- Kept `{0,r}` explicit.  At `b=r/2`, used the uncancelled `p/2` factor and the
  direct central Taylor row; the same coefficient table holds with singleton
  convention.
- Summing the surviving coefficient gives `-E_1(a^[r])/84`.  The exact
  infinity relations `sum_b a^[r]_(1,b)=0` and
  `sum_b at^[r]_(1,b)=0` therefore prove `(H-NF)`.  Together with Session 5's
  exact reflected decomposition and proved middle `p^5` floor, this proves
  `E,Et in p^5 Z_p`, i.e. `(H)`.
- Strengthened the required gate.  At `p=11,13,17`, all offsets, pairs, and both
  arrays, `sol_h5.py` now asserts the full congruence against the small-index
  `a_1` row modulo `p^5`.  Its arrays are independently imported from
  `sol_j12.exact_arrays`, so both named Session-5 oracles are crossed.  Endpoint
  and central digits print separately.  Diagnostic primes `19` through `43`
  also passed; these remain regression evidence.
- Wrote `PHASE2_H5_CERTIFICATE.md` with the Bell row, five-coefficient table,
  endpoint/central branches, and the `E_1` finite-field certificate.

## 2026-07-20 — session 6: LEAD proved; primitive-Q audit

- With `(H)`, `(RT)`, and `(RM)` now theorems, the exact level determinant
  identity reduces modulo `p` to

      p^5 P_(p+t) = (29/28) Q_(p+t) mod p.

  The head determinant is in `p^3`, the reflected head+tail regular determinant
  is in `p`, and the middle determinant is in `p^4`; the binomial normalizer is
  a unit.  Thus `(LEAD)` is proved levelwise for the three offsets.
- Audited the requested primitive-Q-triple step rather than importing it as a
  theorem.  The exact double-binomial formula has no all-zero midpoint triple
  for any of the 48 primes `11<=p<240`; required digits are
  `[0,5,1]`, `[8,5,11]`, `[14,10,16]`.  This is exact finite evidence.
- A uniform proof was not found in the repository.  Back-propagating three
  zeros through the order-three recurrence stops at roots of the cubic leading
  factor `a0`; crossing those roots requires precisely a saturated Q-gate
  lemma, so treating “primitive-Q-triple” as automatic would hide a real
  obligation.  Consequently `(U)` and the complete midpoint assembly remain
  conditional on that one explicit lemma and are not promoted from samples.

## 2026-07-20 -- session 7: Q3 and the a=1 midpoint closed

- Replaced the failed recurrence back-propagation with the fundamental
  Casoratian of `(Q,P,Phat)`.  From the exact base determinant and the
  companion-matrix quotient, proved uniformly

      C_n=(-1)^(n-1)a0(n)/
          [16(n+1)^4(n+2)^5(2n+1)(2n+3)C(2n,n)].

- At `r=(p-5)/2`, all determinant denominator factors are p-units.  Lemma C
  makes the P/Phat defining minors p-integral, and `C(2m,m)` is a p-unit for
  the three rows; this does not use the global denominator law.  Thus a zero
  Q-triple forces `p|a0(r)`.  The exact
  specialization

      8a0(r)=41218p^3-220572p^2+397530p-241144,
      241144=8*43*701

  reduces the uniform statement to two primes.
- Evaluated the manifest double-binomial directly at the exceptional rows:
  `p=43 -> [33,0,26]`, `p=701 -> [472,350,182]`.  The required gates are
  `p=11 [0,5,1]`, `13 [8,5,11]`, `17 [14,10,16]`, `19 [15,2,0]`, and
  `23 [6,22,13]`.  Hence `(Q3)` is proved for every `p>=11`.
- Audited MOS 1705.05586 and Zudilin math/0206178.  MOS's half-period modular
  coefficient is not uniformly nonzero (`p=19` is already zero); Zudilin's
  recurrence is useful through its Casoratian instead.
- Combined `(Q3)` with the proved Lucas row and `(LEAD)` to obtain `(U)` and
  `e_p=-5`.  In `(DET-MID)`, the Q row, `(H)`, `(RT)`, and `(RM)` then give
  `p^5M_p in pZ_p`, or `v_p(M_p)>=-4=e_p+1`.
- Issued the complete certificate-shaped theorem for the **a=1 midpoint band
  only**.  General `a`, prime-power midpoint depth, and cubic gates remain open.

## 2026-07-20 -- session 8: cubic self-reference characterized

- Rechecked the Session-2 quadratic CUB remainder exactly and enumerated every
  root of `a0` for primes below 50:

      7:{2,6}, 11:{5,6,9}, 13:{7}, 17:{8}, 23:{17},
      29:{27}, 41:{10}, 43:{19}.

- Found the structural reason the midpoint Casoratian proof cannot be mirrored.
  At `a0(r)=0 mod p`, the CUB recurrence row is a common left annihilator of
  all three primitively scaled solution columns.  Their saturated Casoratian
  therefore has the expected rank drop; at upper roots, raw denominator factors
  can cancel the visible `a0(r)` valuation.  Dividing `a0` away gives a first
  jet but does not prove the Q column primitive and does not select P.
- Exact cached gates at every listed root with `p>=11` show: the small Q triple
  is nonzero; normalized Q, P, and Phat all satisfy the CUB row; at `N=p+r`,
  `e=-5`, the P row gains at least one order, and at internal gates `r<=p-4`
  the observed leading digits obey `p^5P=(29/28)Q mod p`.  Roots in the final
  three residues meet the digit-boundary factor and are diagnostics only.
- The missing uniform input is now explicit: either prove LEAD in every cubic
  chamber plus primitive-Q at roots of `a0`, or compute an adjugate/connection
  first jet selecting P.  The midpoint Phi formula assumes `2r<p`; upper roots
  have an additional factorial block, so the existing proof does not cover it.
- Flagged the combined gate `p=43,r=19`: midpoint and cubic depth add, requiring
  `e+2`.  The cached full recurrence numerator passes.  At `p=701,r=348` the
  cached small-root Q/P/Phat structure passes, but the a=1 lift `N=1049` is
  unavailable.  Also proved the scope observation that midpoint depth greater
  than one cannot occur in an `a=1` block for `p>=5`; that problem necessarily
  belongs to later-digit transport.

## 2026-07-20 -- session 9: adjugate first jet computed; route walls

- Derived the exact companion-adjugate recurrence

      c3(n) adj(Y_(n+1)) = adj(Y_n)
        [[c1,c2,c3],[-c0,0,0],[0,-c0,0]].

  At an `a0` root it reduces to the rank-two regular plane cut out by the CUB
  row.  Expanded `Y adj(Y)=det(Y)I` to first order after primitive column
  saturation and gated the complete first-jet identity at every requested
  small root.
- The rank-one adjugate does not select the named `P` column.  Its row span is
  the CUB left annihilator; its column span is a mixed relation among the
  `(Q,P,Phat)` columns.  Every simple internal oracle direction is mixed; at
  `(43,19)` it is `(30,9,30)`, not the pure `Phat` axis.
- Proved the basis-invariance obstruction: the constant `SL3` change
  `(Q,P,Phat)->(Q,P+Phat,Phat)` preserves both the scalar recurrence and its
  Casoratian but changes named-column regularity.  Therefore recurrence plus
  Casoratian cannot prove that P, rather than P plus a singular solution, is
  ordinary.
- Isolated the exact missing input as the P column of the one-digit Frobenius
  connection matrix: for `N=p+r`, one must independently prove that the
  normalized lifted P vector belongs to the CUB plane.  This is equivalently
  the desired CUB-row divisibility and cannot be obtained by recycling the
  adjugate identity.
- Handled the upper-root chamber explicitly in the oracle.  The internal upper
  roots `(11,6),(13,7),(23,17)` have central-binomial carry vector `(1,1,1)`;
  their P floor, CUB gain, and LEAD digits all pass exactly.  This confirms the
  missing theorem must include a carry-sensitive factorial connection term.
  `(29,27)` is additionally a multiple root modulo 29 and lies at the digit
  boundary.
- Stopped at the requested wall.  The cubic gate and complete `a=1` descent
  remain open; the Session-7 midpoint theorem is retained as the standalone
  proved result.
