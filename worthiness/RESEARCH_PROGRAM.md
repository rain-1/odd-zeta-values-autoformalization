# The arithmetic screening instrument, and the divisible-class program

Written down at River's request, 2026-07-16. These are the two
forward-looking implications of the denominator audit for the (currently
walled-off) irrationality problem for ζ(5). Companion documents:
`CONJECTURE.md` (the 12·D_ν law), `PROOF_MECHANISM.md` (lattice mechanism),
`PROOF_SYMMETRIC.md` (concrete sine-kernel derivation).

---

## Part I — The instrument: arithmetic screening of candidate constructions

**The problem it solves.** Every expert assessment of the odd-zeta
irrationality program (Fischler, Zudilin, Brown–Zudilin, CDT — surveyed in
the repo README) converges on "a new construction is needed", and that
search has no reward signal: historically, evaluating a candidate integral
family's arithmetic meant months of expert work proving (or guessing)
inclusion lemmas, because the true denominators of the linear-form
coefficients were not directly observable.

**What exists now.** The audit pipeline makes true denominators
*measurable*: given any family whose linear forms can be evaluated to a few
hundred digits (one 1-dim integral of hypergeometric factors sufficed for
the BZ family; the method is generic), PSLQ recovery + exact Q-side
formulas yield the exact rational coefficients, hence exact denominators,
in ~seconds-to-minutes per (parameter, n) cell. The per-prime ledger
(requirement vs. lcm-payment vs. group saving) then localizes the
family's arithmetic exactly.

**Why this changes the search economics.** A proposed "new representation
with its own arithmetic" (BZ's closing question) can be *screened before
anyone proves anything*: compute 20 cells, read off the true C₂-relevant
denominator growth, and compare against the asymptotic budget. Candidates
that don't beat the known constructions die in an afternoon instead of
occupying a person-year. Candidates that show anomalous savings get
flagged for theory. The γ-evaluator (this repo) prices the analytic side;
the audit prices the arithmetic side; together they form a complete scorer
for effective-linear-form constructions — the missing half of the
"search-shaped" approach that our original survey identified as the
binding constraint.

**Literature positioning (verified 2026-07-16).** The measured object is
new: the classical literature states denominator laws as provable upper
bounds and, in every case checked (Apéry ζ(3), ζ(2), Krattenthaler–Rivoal
/ Vasilyev, ζ(4)), the constant-term correction factors quoted in print
(e.g. "2dₙ³") turn out to be *slack* — the sharp constant-term law is the
bare lcm-power (verified computationally to n = 50 for Apéry ζ(3);
Rhin–Viola Thm 2.1 confirms). Nobody appears to have systematically
*measured* denominators as an experimental object before, which is exactly
why the BZ family's genuinely-sharp correction (below) went unnoticed.

## Part II — The divisible-class program

**The reformulation.** The mechanism work (PROOF_MECHANISM.md, Lemma 1 +
the sine-kernel derivation in PROOF_SYMMETRIC.md) says: denominators of
these linear forms are *lattice phenomena*. The linear form is the pairing
of a de Rham class ω against a Betti homology class; its true denominator
is governed by (a) the de Rham denominators of ω and (b) the *index of the
pairing class in the integral Betti lattice*. The BZ family pays a factor
(the measured 12) because its ζ(2)-elimination class is non-primitive by
exactly that much — the first documented case where such a constant-term
correction is *sharp* rather than slack, and (per the literature agents)
the classical corpus contains no example, no measurement, and no
mechanism for one. Fischler's survey explicitly wishes for a
geometric/motivic interpretation of the small constants in this subject;
for this family, the lattice mechanism is a candidate answer.

**The flip — where the upside lives.** If elimination classes can be
non-primitive in the *costly* direction, integral classes can in principle
be non-primitive in the *favorable* direction: a homology class computing
the ζ(5)-form that is divisible by N in the integral lattice yields
denominators smaller than every cocycle-level prediction by the factor N.
The audit data proves sub-prediction arithmetic exists in the wild
("slack": 14/19 first-map points, one case by 2⁶). BZ's closing question
— "what are those other representations?" — becomes, in this language:

> **For the motive M(a) of the family, compute the maximal divisibility,
> in the integral Betti lattice, of classes γ whose pairing computes the
> ζ(5)-form — as a function of a and n. Equivalently: characterize the
> true lattice index behind the measured slack.**

**Why this is a genuinely different question from the ones that died.**
The survey's dead directions all foundered on "search a space with no
scorer". Here: (i) the slack is *pointwise measurable* (the audit),
(ii) the question is *structural* (one lattice per point, computable in
principle by Keel-torsion-free cohomology of M̄₀,₈ + integral de Rham of
the stable model), and (iii) there is a concrete falsifiable growth
question — is slack ever exponential in n along a ray? — which is exactly
what would resurrect the γ program, and which no theory currently
predicts either way.

**What is known so far (honest state).**
* Slack exists, is common at small heights, and is small (bits, not
  exponents) at every measured cell; the 2⁶ outlier a = (4,3,4,4,3,2,4,2)
  is the largest observed.
* Growth data is thin: at the outlier, slack₂ moved −6 → −5 from n = 1 to
  2; at the slack control point −2 → −3; at one violator the n = 3 cell
  flipped from binding (+2, +2) to slack (−4) — so *neither* excess nor
  slack is constant in n in general; only the ceiling law (≤ +2 at 2,
  ≤ +1 at 3, ≤ 0 at p ≥ 5) has survived every cell. The conjecture is a
  divisibility bound, not a formula; the pointwise structure of slack is
  precisely the unexplored object.
* No cell has ever shown slack growing like c·n (which is what a γ-moving
  reservoir would require). Finding one, or proving none exists, is the
  program.

**Concrete next experiments (ordered by information per CPU-hour).**
1. Slack-growth series n = 1…6 at the 2⁶ outlier and the two biggest
   slack points (needs the analytic-tail upgrade to `fast_eval` for the
   deepest cells).
2. Slack map over a *ray*: fix the outlier's direction, scale a → t·a,
   audit t = 1, 2, 3 — does the anomaly scale with height?
3. The lattice computation (H2 of PROOF_MECHANISM.md) at ONE point, e.g.
   the symmetric point: integral Betti lattice of the rank-3 motive via
   Keel + stable-model de Rham. Would convert the mechanism from
   conditional to proven at that point, and calibrate the whole program.
4. Cross-family: run the audit on the classical ζ(3) Rhin–Viola family
   (trivial to wire: same pipeline) to verify the instrument reproduces
   the known exact laws there — a control experiment for methodology
   credibility.

## Part III — Relation to the irrationality of ζ(5) (calibration)

Nothing here claims a path to γ > 1. The honest chain is: the wall is
real and exactly surveyed (C₀+C₂ = +18.05 with arithmetic now understood
to bounded factors); the only untracked upside inside *any* effective
construction is unbounded lattice divisibility; no evidence of exponential
slack exists; but for the first time the question is measurable, and the
instrument is built. If the slack-growth experiments stay bounded, this
program's output is a theorem-shaped negative ("the BZ family's
arithmetic is exactly D_ν up to 12 and bounded slack") plus the
conjecture and mechanism — a solid paper. If they don't stay bounded,
everything changes.
