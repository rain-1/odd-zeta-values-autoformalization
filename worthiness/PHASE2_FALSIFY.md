# PHASE2_FALSIFY — maximally adversarial test of the corrected denominator law and the descent (D)

Worker campaign 2026-07-20 (Opus). Mission (River): *"maybe the p ≤ n conjecture
is literally false"* — try to **falsify** the law and (D) in the cells no one has
ever tested, above all the never-touched **k=3** band. All arithmetic exact
(`fractions.Fraction`/`int`). **Honesty standard:** every check below is an exact
finite computation over a *stated* grid — this is **evidence, not proof**. Any
claimed violation is independently re-derived by **direct** `salvage_data.triple`
(the partial-fraction ground truth), never trusted from recurrence propagation.

**Objects.** `P_n = (−1)^{n+1} p_n / C(2n,n)` (weight-5 ladder), `Q_n` (weight-0),
`P̂_n` (weight-3 companion), `d_n = lcm(1..n)`.
**LAW:** `12 · d_n⁵ · P_n ∈ ℤ` for all n.
**(D):** `v_p(P_n) ≥ v_p(P_{⌊n/p⌋}) − 5` for p ≥ 5.

Scripts (new, `worthiness/`): `falsify_data.py` (T1 exact recurrence extension +
cross-validation + `falsify_data/` store), `falsify_tests.py` (T2–T5 + direct
reconfirmation). Data: `falsify_data/ladder_{Q,P,Ph}.json` (n=0..360).

---

## HEADLINE

> **NO violation of the law and NO violation of (D) was found anywhere in the
> tested grid — n ≤ 360, p ∈ {5,…,73}.** In particular the **k=3 band is CLEAN**
> for **both** accessible primes: p=5 (n∈[63,124], 62 cells) *and* p=7
> (n∈[172,342], 171 cells). The law holds at all 360 levels; (D) holds over
> **5 989** descents. The corrected law and (D) **survive** the adversarial test.

This is an all-clear, reported as evidence over the exact grid below — not a proof.
The single new *nuance* (a harmless numerator-side order drop in **Q**, direct-
confirmed) is recorded in T4; it does **not** touch the law or (D).

---

## T1 — data extension (the enabling step)

Forward-recursed the exact **normalized order-3 recurrence** (V6b) in `Fraction`:

```
c0(n)Y_n + c1(n)Y_{n+1} + c2(n)Y_{n+2} + c3(n)Y_{n+3} = 0,   Y ∈ {Q,P,P̂}
c0=(n+1)^5(n+2)a0(n+1)   c3=2(n+3)^5(2n+5)a0(n)   a0=41218n³+198849n²+320790n+173057
Y_{n+3} = −(c0 Y_n + c1 Y_{n+1} + c2 Y_{n+2}) / c3(n).
```

- **No division-by-zero / integrality corruption:** `c3(n)=2(n+3)⁵(2n+5)a0(n) > 0`
  for every n ≥ 0 (a0 is an irreducible cubic, all positive-n values > 0), so the
  step is always well-defined in ℚ; everything stays exact.
- **Cross-validation vs DIRECT computation: 0 mismatches.** The recurrence
  propagation was checked against `salvage_data.triple` for **all** n=3..150 (148
  points, far beyond the requested n=25,30) **and** direct spot points n=200, 275,
  350. Every Q,P,P̂ value matched exactly. Data saved to `falsify_data/` for reuse.

Coverage delivered: **exact (Q,P,P̂) for n = 0..360** (target was ≥130).

## T2 — the LAW at every new n  → 0 violations

`12 · d_n⁵ · P_n ∈ ℤ` for **all n = 1..360**: **0 violations.**

Tightness (how close to failure the law sails):
- **Overall min-slack = 0 at all 360 levels, always at p=2.** The constant
  `12 = 4·3` makes the law **exactly tight 2-adically**: `12 d_n⁵ P_n` is **odd**
  for every n. So the "12" cannot be shrunk — its factor 4 (and the 3) are forced.
- **p ≥ 5 restricted min-slack histogram: {0: 356, (>0): 4}.** The law is tight at
  some p ≥ 5 for **356 / 360** levels (first tight at n=5, p=5; also p=17,… ). The
  law is *not* generically slack — it rides the boundary almost everywhere at p≥5.

All-clear reported over the exact grid n=1..360.

## T3 — descent (D), including the virgin k=3 cells  → 0 violations

(D) checked for p ∈ {5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73},
all n ≤ 360 with ⌊n/p⌋ ≥ 1: **5 989 descents, 0 violations.** Overwhelmingly
tight (slack 0); worst observed slack = 3 (a single p=7 case). Per-prime tallies
in the script output.

**The k=3 verdict (the headline target).** k=3 means `p^k ∈ (n, 2n]`, the cells
where the crude `d_{2n}⁵` tier cannot help. The two primes with a k=3 band inside
n ≤ 360:

| p | k=3 band `p³ ∈ (n,2n]` | cells | violations | slacks |
|---|---|---|---|---|
| **5** (p³=125) | n ∈ [63, 124] | 62 | **0** | all 0 (fully tight) |
| **7** (p³=343) | n ∈ [172, 342] | 171 | **0** | 0/1/2/3 mix, all ≥ 0 |

Both **completely clean.** (p=11 needs n up to 1331/2≈665, p=13 up to 1099 — above
range; see "untested" below.) The **iterated three-digit assembly**
`v_p(P_n) ≥ −5⌊log_p n⌋` also holds with **0 bound-failures and 0 non-integral
terminals** — including **236** genuine 3-digit levels at p=5 (⌊log₅n⌋≥3, i.e.
n∈[125,360]) and **18** at p=7 (⌊log₇n⌋≥3, i.e. n∈[343,360], since 7³=343).

## T4 — singularity-prime stress test  (P vs P̂)

Operator leading coefficient `c3(n)=2(n+3)⁵·(2n+5)·a0(n)`: the true-singularity
primes are `p|(2n+5)` (midpoint) and `p|a0(n)` (cubic). Solving the recurrence
divides by c3, so such a p is *injected* into `Y_{n+3}`.

**Part A — per-step holonomic control** (strict "only (n+3)⁵ loss" bound
`v_p(Y_{n+3}) ≥ min(v_p Y_{n..n+2}) − 5 v_p(n+3)`), 6 479 steps × 19 primes, split
by danger source:

| ladder | a0-danger | midpoint-danger | non-danger |
|---|---|---|---|
| Q (wt 0) | **1/346** | 0/325 | 0/6123 |
| **P (wt 5)** | **0/346** | **0/325** | **0/6123** |
| P̂ (wt 3) | 1/346 | 17/325 | 0/6123 |

- **P (the law's target): 0 leaks in every category over 6 479 steps.** The
  midpoint and a0 factors behave apparently for P; the induction loses exactly the
  built-in 5 orders per step, never more.
- **P̂ leaks systematically**, precisely at the midpoint (17 cases) plus a0 — the
  operator's true singularities, exactly the salvage V6c positive control, now
  **extended to n=357** and still holding.
- **NEW nuance (Q):** one a0-injection into Q at **n=306, p=7** (7 | a0(303),
  v₇=1): `v₇(Q_306)=2` while `v₇(Q_303,304,305)=3`. **Directly confirmed** (not a
  recurrence artifact): Q_306 is a positive integer, one 7-order lighter than its
  neighbors. This does **not** break anything (Q stays in ℤ; the same n has
  `v₇(P_306)=−7`, law slack `5·2−7 = 3 ≥ 0`). It merely refines the salvage claim
  "a0 apparent for **Q**,P" — that was an artifact of the old n≤44 range; at n=306
  a0 *does* inject one order into Q, absorbed by Q's numerator reserve. **P is
  strictly cleaner: 0 injections in 6 479 steps.**

**Part B — does the target P ever break the LAW at a singularity prime?** P carries
a singularity prime in its denominator in **739** (n,p) cases (n≤360); of these
**0** exceed the `d_n⁵` allowance (law-slack `5⌊log_p n⌋+v_p(P_n) ≥ 0` always).
**P stays within the law at every singularity prime.**

**Part C — midpoint positive-control table.** At index n the injected midpoint
prime is `p = 2(n−3)+5 = 2n−1`. Over the 125 n≤360 with `2n−1` prime and ≤ 2n:
**P̂ leaks (v_p < 0) at 124 of 125; P leaks at 0 of 125.** The one non-leak
(n=4, p=7) is the boundary case. This is the cleanest statement of the P̂-leak /
P-clean dichotomy.

## T5 — exceptional-chain stress test

Descents (n,p) where the target `P_{⌊n/p⌋}` is itself p-nonzero (v_p ≠ 0) — the
`7 | q₁=42` class (confirmed: raw `q_1 = 42`, 7 | 42) generalized to any p-content
at the descent target. **1 357** exceptional descents, **0** violate (D). Of these,
**1 152** have p in the **denominator** of the target (the hardest class, e.g.
p=5,n=25,a=5: `v_5(P_5)=−5`, `v_5(P_25)=−10`, slack 0) — **0 violations, and these
are exactly tight (slack 0)**: (D) is *saturated* precisely where the target
already carries `p^{−5}`. The descent has no room to spare there, yet never fails.

---

## Scope statement (evidence, not proof) & what remains untested

**Exact grid covered:** law at n=1..360; (D) at p∈{5..73}, all n≤360 with
⌊n/p⌋≥1 (5 989 descents); k=3 fully covered for the only two accessible primes
p=5 (n∈[63,124]) and p=7 (n∈[172,342]); singularity primes and exceptional chains
as above. Recurrence data exact and cross-validated against direct at 151 points.

**Untested above this range, and the marginal cost:**
- **k=3 for p=11** needs n up to `11³/2 = 665`, **p=13** up to `1099`, etc. Not
  reached. Recurrence extension is essentially free (seconds to n≈700); the binding
  cost is *direct* cross-validation — direct `triple(n)` grows ≈ cubically: ~9 s at
  n=200, ~21 s at n=275, ~42 s at n=350, so validating a handful of spot points up
  to n≈700 costs a few minutes each. Worthwhile if the k=3 story is wanted for a
  third prime; the recurrence is already validated exactly at 151 points, so its
  propagation to n≈700 is high-confidence even without new direct checks.
- **k≥4** (p=5: p⁴=625, band n∈[313,624]) is partially entered (n≤360 covers
  n∈[313,360] of it) and clean there; the rest needs n up to 624.
- Larger primes p>73 at their k=1 band are covered by the proven band certificate;
  not re-tested here.

**Bottom line.** The maximally adversarial sweep found **no counterexample**. The
corrected law and (D) hold, tightly, in every previously-untested cell reached —
decisively including the k=3 band for both p=5 and p=7. The only new structural
observation (Q taking a single a0-order at n=306) *sharpens* the salvage picture
without threatening the theorem: it shows a0 is not perfectly apparent even for Q,
yet P — the actual target — is strictly apparent (0 injections, 6 479 steps) and
never leaves the `d_n⁵` law.
