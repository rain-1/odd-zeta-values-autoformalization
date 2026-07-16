# Odd zeta irrationality as an AI-mathematician research direction

**Survey date:** 2026-07-16 · **Method:** nine research agents against primary sources · **Verdict:** eight directions dead, one live.

---

## The question

Is the irrationality of odd zeta values — ζ(3), ζ(5), the Ball–Rivoal/Zudilin/Fischler set results — a productive research area **for an AI mathematician**? Not for a human with a Lean background; for an agent with cheap parallel search, no fatigue, weak taste, and a hard need for verifiable ground truth.

## The answer

**One direction survives:** formalize Zudilin's elementary route ([arXiv:1801.09895](https://arxiv.org/abs/1801.09895)) in Lean 4. See [§Recommendation](#recommendation).

Everything else fails, and they fail for the *same reason*, which is the real result of this survey.

---

## The two central findings

### 1. Verifiability and headroom are anti-correlated

| Direction | Tractability | Novelty | **Verifiability** |
|---|---|---|---|
| Sharpening constants | 2 | 2 | **8** |
| Nesterenko in Lean | 7 | 3 | **9** |
| Beukers tweaking | 5 | 3 | **8.5** |
| p-adic analogues | 3 | 2 | **2** |
| Arithmetic holonomicity | 2 | 8→3 | **1** |

The three directions with crisp automatic reward signals are the three that are exhausted. The one with genuine ICM-level value has verifiability 1. A crisp reward signal does not rescue a problem with nothing left to find — **verifiability without headroom is a well-lit empty room**.

Worse: a *working* scorer is not protection against a picked-over space. It is what let the experts pick it over faster. Zudilin's GP-PARI sweep of the Rhin–Viola space is the proof — the scorer was real, was built, was run, and returned the incumbent.

### 2. Every direction dies on "you need a new construction"

Four of the field's leading people, in their own words, all pointing at the same place:

- **Fischler** — *"il faudrait probablement chercher du côté de la **transformation hypergéométrique**"* (and he *proves* the group can't get richer)
- **Zudilin** — *"investigate the other classical hypergeometric instances from **Bailey's and Slater's books**"*
- **Brown–Zudilin** — *"But **what are those other representations**?"*
- **CDT** — *"**unless some completely new idea is discovered**"*

This is the binding constraint, unanimously. It is also precisely the thing with no scorer, no enumeration handle, and no search surface. **Every search-shaped direction optimizes the non-binding constraint.**

The field's last real win — Calegari–Dimitrov–Tang — was **new theory applied to an old Zagier construction**. The constraint was never "too few constructions enumerated." It was "too little theory to exploit the constructions we already had."

**The survivor survives because it is the only direction that doesn't need a new construction.** The mathematics is finished and published; only the encoding remains — and encoding a known proof is the one thing here an agent is good at, with a compiler that grades it.

### The base rate

Two well-resourced automated attacks, both measured, both null:

- **The Ramanujan Machine** — 7 years, BOINC-scale compute, *Nature* 2021: **zero new irrationality proofs**. Authors' own admission: *"it is not known which polynomial recursions create useful DAs."* Andrews called the branding over the top; the real output was irrationality *measures*.
- **Dougherty-Bliss–Koutschan–Zeilberger** ([2101.08308](https://arxiv.org/abs/2101.08308)) — swept Beukers-integral parameters at denominators 2–7, hundreds of δ>0 hits. **Zudilin identified essentially the entire list within seven months** ([2108.06586](https://arxiv.org/abs/2108.06586)) as known Γ(1/3)³/π-type constants, logs, or in one case plainly algebraic. Net yield: **zero**.

Both converged on the same consolation prize. DKZ's headline claims failed *specifically because a weak CAS couldn't identify a constant and they read that as novelty* — **"Maple couldn't identify it" is near-zero evidence.**

---

## Recommendation

**Formalize Zudilin's elementary route in Lean 4** — [arXiv:1801.09895](https://arxiv.org/abs/1801.09895), "One of the Odd Zeta Values from ζ(5) to ζ(25) Is Irrational. By Elementary Means."

*(Note: the companion [arXiv:1802.09410](https://arxiv.org/abs/1802.09410) is **Johannes Sprang solo**, not Zudilin.)*

### Why it works

- **No hypergeometric gap.** The feared blocker does not exist. **Zero named hypergeometric transformations** in either paper — no Whipple, Bailey, Dougall, ₇F₆, contiguous relations. "Well-poised" has content in exactly one lemma (R(−t−n) = −R(t), direct algebra). Mathlib's bare pFq support is irrelevant.
- **No irrationality criterion at all** — not Nesterenko, not even Dirichlet. The finish is *"a positive integer cannot tend to 0."*
- **No integrals.** Series and partial fractions over ℚ. Over half of the ζ(3) repo's 4157 lines is integral machinery (Integral 1136, plus ENNReal/Fubini plumbing). That entire cost category vanishes.
- **The API already exists**: `Algebra/Polynomial/PartialFractions.lean` (521 lines, **including uniqueness** — exactly what Lemma 2 needs), `NumberTheory/Chebyshev.lean` (`Nat.lcmUpto`, `psi_eq_log_lcmUpto`), `Stirling.lean`. Needs only **plain** PNT (`WeakPNT''`, sorry-free in PrimeNumberTheoremAnd) — *not* the effective version the ζ(3) proof required.
- **Nobody is doing it.** One Zulip thread, **March 2018** — Buzzard posted Sprang; Mahboubi (who led the Coq ζ(3) work) noted it needs only lcm = O(3ⁿ), matching Zudilin's own §4 remark. Dormant eight years. The ζ(3) team stated no next steps.

### The sharp near-miss

Mathlib's existing dₙ bound gives constant **4** — and the D=2 construction saturates *exactly* at 4, so with Mathlib alone it **never works, for any s**. Any constant strictly below 4 suffices:

| dₙ bound | constant | min odd s |
|---|---|---|
| PNT (dₙ^(1/n) → e) — sorry-free in PNT+ | 2.7183 | **25** (= Zudilin's) |
| Hanson 1972, dₙ < 3ⁿ — not formalized | 3.0000 | **33** (= Sprang's) |
| Mathlib's θ ≤ log4·x → 4ⁿ | 4.0000 | **never** |

The entire arithmetic gap is one Chebyshev constant under log 4.

### The one real risk

**Lemma 4's asymptotics are not in the paper.** Zudilin delegates to de Bruijn, *Asymptotic methods in analysis* §3.4; Sprang does the same. An agent must invent the max-term argument — the classic formalization pit.

*Mitigation:* everything sits under an nth root, so any subexponential factor is free. You need `limsup rₙ^(1/n) ≤ g(x₀)`, **not** de Bruijn's sharp γ√n localization.

### Why the "Sorries" critique doesn't bite

[arXiv:2606.13925](https://arxiv.org/abs/2606.13925) ("Sorries Are Not the Hard Part") found agents formalize Grothendieck vanishing with **zero sorries** while expert review still finds serious problems in *definitions, generality, and API design*. Agents "adapted well to local, mechanically checkable feedback, but remained weak at choosing definitions and designing APIs."

**This route needs almost no reusable API.** It is a self-contained result, not infrastructure — little surface for that failure mode to attack. Note the inversion: the originally-proposed task (build hypergeometric theory, formalize Nesterenko) is *exactly* the generality-critical, agent-hostile one. This route dodges it.

### Cost and first move

**6–12 person-months, central 8–10** — same order as ζ(3), arguably less.

> **Formalize Lemma 4 first, not Lemma 1.** ~2–4 weeks; it isolates essentially all the risk. Starting with the arithmetic gives a **false green light** — it compiles beautifully and tests nothing that can fail.

A one-week warm-up (`(lcmUpto n)^(1/n) → e` from `WeakPNT''` + `psi_eq_log_lcmUpto`) confirms the s=25 dependency is cheap.

---

## The dead directions

### Sharpening constants — DEAD (search space was never big enough to mine)

An agent reconstructed and re-ran Fischler's §4.6 optimization ([2109.10136](https://arxiv.org/abs/2109.10136)). He picks r=3.9, κ=10.58, h=0.36a by hand and writes *"0.21 is the rounded value of a real number that we did not try to compute exactly"* — an engraved invitation.

| | r | κ | h/a | constant |
|---|---|---|---|---|
| Fischler, by hand | 3.9 | 10.58 | 0.36 | 0.217456 |
| True optimum | 3.932 | 10.662 | 0.3575 | 0.217488 |

**0.015% gain.** Once ω drops out asymptotically and the constraint binds, it's a smooth 2-parameter problem he solved in his head. No CPU-shaped hole. Fischler's own Remark 2 names his bottleneck: past a certain constraint, Siegel's lemma gives non-explicit coefficients and he *"cannot hope to reach any contradiction."* Idea-shaped, not parameter-shaped.

**Frozen records:** Zudilin 2001 (one of ζ(5),ζ(7),ζ(9),ζ(11)) and μ(ζ(3)) < 5.513891 (Rhin–Viola 2001) — both **unimproved for 25 years**. Apéry (~13.4, 1978) → Hata (8.83, 1990) → Rhin–Viola (5.5139, 2001) → nothing. Progress didn't decay; it stopped.

### Nesterenko in Lean — DEAD (small, and aimed at a bypassed target)

Not a keystone. Fischler–Zudilin reprove it in **~1.5 pages** from ingredients Mathlib already has; **1–3 person-months**. And it's now *avoidable*: Zudilin's 2018 papers explicitly name Nesterenko's criterion as a thing to **eliminate**, replacing it and the saddle-point method with "twists by half." True of the 1979–2010 literature; false as of 2018. Formalizing it would be building a bridge next to a ford.

### Beukers tweaking — DEAD (measured zero payout, already scratched)

See [base rate](#the-base-rate). The method is *structurally* incapable of reaching ζ(5): second-order recurrences give linear forms in **two** constants; ζ(5) needs order ≥ 3. DKZ even *retreat* to a hand-picked 5-parameter subfamily specifically to keep the recurrence second-order — the one decisive move in the paper, and it's taste, not search.

### p-adic analogues — DEAD (mechanical *or* publishable, never both)

The premise "p-adic is where obstructions relax" is **wrong**. Derived from Lai–Lupu–Sprang's Eq. (8.1): a race between a p-adic gain of (p/(p−1))·log p and an unchanged archimedean cost of 1+log 2 ≈ 1.693. p=2 → 1.386 (fails); p=3 → 1.648 (fails narrowly); p=5 → 2.01 (works).

- **What relaxes:** smallness — you can literally *buy* it by multiplying by p^{pn}.
- **What tightens:** **non-vanishing**. ℚ_p has no positivity, and the archimedean proof gets non-vanishing *free* from an integral being positive. So the template you'd pattern-match from **contains no argument at the exact step where the work is.** Close to a worst case for transfer-style generation.

Also: Lai's [2407.14236](https://arxiv.org/abs/2407.14236) v2 comment reads *"added p-adic analogue"* — experts bundle the mechanical cases into revisions of their archimedean papers. The publishable-unit assumption is false. And Lai/Sprang have left for other problems entirely.

### Arithmetic holonomicity — DEAD as a target (real math, unreachable frontier)

CDT stated the obstructions **in print**:

- **ζ(5)** is blocked **upstream of the criterion entirely** — in constructing a motivic local system isolating the period. Periods *"get mixed together and it is hard to separate the period one is particularly interested in"*; they *"know of no simple analogous construction"* for real ζ(2k+1). A better bound doesn't touch it.
- **Catalan:** *"this definitely precludes an approach ... unless some completely new idea is discovered."*

Numerology clears by 5–8% (ζ₂(5): 5.52667 < 6; one L(2,χ₋₃) attempt gives 9.5234 < 10 and is *"not enough"*). No formalization path under 220 pages of Bost slope method.

**The barrier is length, not depth** — Calegari: the background *"doesn't involve much beyond the complex theory of modular forms as well as some complex analysis."* People were enthusiastic *until learning the paper was 220 pages*. So "thin literature = less competition" is dead: an **Oberwolfach Arbeitsgemeinschaft ran March 2026**, organized by CDT, in the format explicitly designed to train non-specialists.

### CDT §15.5 denominator types — DEAD (the one salvaged niche, downgraded)

§15.5 is **one page**, no questions, no conjectures — a caveat explaining why the authors stopped. Their own verdict, immediately after the Cooper anomaly:

> *"it also means that the irrationality of the Apéry limit associated to Cooper's sequence is amenable to our methods; **however, since the corresponding constant appears to be π²/42, we have not pursued this!**"*

They found the anomaly, checked whether it bought a theorem, and the prize was already on the shelf.

**The certifiability asymmetry** (this is what kills verifiability 8 → 4): a denominator type is a claim about *all* n with a `C^{n+1}` slack term. **Refuting** one is machine-checkable (a single bad n). **Discovering a drop** — the hunt's actual output — is *not* certifiable from finite data. The direction targets the uncertifiable side.

Also: the niche is **occupied**. Bönisch–Duhr–Maggio ([2404.04085](https://arxiv.org/pdf/2404.04085)) already publish magnetic candidates verified by checking *"several hundred first coefficients"* — the exact deliverable. The family is **15 sporadic sequences**, exhaustively mined by Gorodetsky. **No database has τ** (the CY Operators DB stores instanton numbers and Yukawa couplings, not denominator types).

### Rhin–Viola group actions — DEAD, on RV's own testimony

The premise was false: **the group is not a search space.** ϕ(x) = **max** over the orbit, so a bigger orbit is always better and you always use all of it. No choosing. The real freedom is 7 integer parameters where only the *direction* matters — the same continuous shape that killed Fischler.

Group orders (verified against the [primary PDF](https://www.math.ru.nl/~zudilin/zw/Rhin-Viola_AA_2001.pdf)): **ζ(2) = 120, ζ(3) = 1920** (= |K|·|S5| = 16·120). 1920 is the *largest* of the family. (Bonus: *"Although 1920 divides 8!, one can prove that no subgroup of the symmetric group S8 has order 1920"* — Dvornicich — hence the embedding in A₁₀.)

RV themselves, in the founding paper, say the group saturates:

> *"this arithmetic information turns out to be **redundant**, in the sense that for any numerical choice of h, j, k, l, m, q, r, s one can find a suitable subset of the set of the 120 transformation formulae which suffices to eliminate the divisors of Aₙ"*

Their published parameters (h=16, j=17, k=19, l=15, m=12, q=11, r=9, s=13) were chosen for **expository simplicity** — only 15 of 120 formulae needed, all at level 4, so "the resulting arithmetic discussion turns out to be quite simple." All 1920 Φ-equivalent choices give the *same* measure.

**Zudilin already ran the exhaustive search** ([math/0206176](https://arxiv.org/pdf/math/0206176) §5): *"Looking over all integral directions (α, β) satisfying α1+α2+α3+α4 = β1+β2+β3+β4 ≤ 200 by means of a program for the calculator GP-PARI we have discovered that the best estimate for µ(ζ(3)) is given by Rhin and Viola."*

**Slack lives in the construction, not the group.** μ(ζ(2)) moved 5.441 → 5.095 (Zudilin 2014) via a new Barnes–Mellin construction. Marcovecchio ([2512.12890](https://arxiv.org/abs/2512.12890), Dec 2025) builds a fresh construction for log 2 and **re-derives μ = 3.574553902525 without beating it**.

### Brown–Zudilin worthiness γ — DEAD, closed by experiment (2026-07-16)

> **Update:** the 1–3 day experiment proposed below was run; see
> [`worthiness/RESULTS.md`](worthiness/RESULTS.md). The γ implementation
> validates to 8 decimals against all three published values, and the search
> confirms the expectation: BZ's "concrete example" is
> s = (20.5; 3.5, 4.5, …, 9.5) — a perfect arithmetic progression in the
> symmetric coordinates — and is a strict local maximum, the unique global
> maximum of the AP family (31,710 projective points to height 160), and
> unbeaten by 120 random multi-start hill-climbs (best 0.86522) and 60
> basin hops. **sup γ = 0.86597135… for this construction.** The prior from
> the Rhin–Viola precedent below is now a measurement.

[arXiv:2210.03391](https://arxiv.org/abs/2210.03391). γ > 1 ⟹ ζ(5) irrational; record γ = 0.866.

**γ compresses the scale.** γ > 1 ⟺ C₀ + C₂ < 0, and BZ compute the actual value at **+18.05** (with C₁ ≈ 85, C₂ ≈ 49.6) — the denominator cost must be cut ~36%. The map 0.866 → 1.0 *reads* as a 15% push; the underlying quantity must move 18 units. **Any evaluation anchored on "0.866, need 1.0" is anchored on an illusion.**

**Nothing has moved in 3.3 years.** Every γ value is identical across v1 (2022) and v3 (2026). The v2 revision only inserted the word "effective" (1 → 11 occurrences) and a Nesterenko framing — because with 0.86 < 1 the approximation is *trivially* satisfiable by non-effective p/q, so the entire content of the theorem is the word "effective." That's a referee pushing. The Jan 2026 date is journal processing, not research.

**What's genuinely unclaimed:** BZ's exhaustiveness theorem is about the **group**, not the parameters — their only optimality claim is "best possible *when compared to any other known constructions*", a benchmark, not a supremum. **a** = (8,16,10,15,12,16,18,13) is introduced as *"let us look at a concrete example"*; the search is never described. So sup γ over the 7-dim projective rational cone has never been claimed.

**But** Rhin–Viola show the identical authorial habit — optimum stated as "a suitable numerical choice," search never described — and Zudilin's later exhaustive sweep proved RV's undescribed choice **was** optimal. The prior that BZ silently optimized is empirically supported by precedent in the same literature, from one of the same authors.

**Still worth 1–3 days**, because it's decisive either way: implement γ (~200 lines, no HyperInt needed), **validate against the two published values 0.77795976 and 0.86597135** (hard pass/fail), hill-climb over the cone. If sup γ ≈ 0.866 → closed. If sup γ > 0.866 → you found something two experts missed. Expected: closed.

---

## Corrections — claims that failed against primary sources

Recorded because the failure mode is the point.

| Claim | Status |
|---|---|
| "No homogeneous polynomials of degree > 3 satisfy Apéry's conditions" | **No such theorem exists.** Folklore, asserted twice from a search snippet. What's real: an *expectation* that three-term Apéry-like recursions don't exist for ζ(5), and Zagier's search, exhaustive only *relative to its ansatz* (6 sequences). |
| "Siegel's lemma isn't in Mathlib" | **False.** `Mathlib/NumberTheory/SiegelsLemma.lean` since 2024, used downstream by `NumberField/House.lean`. Minkowski's convex body theorem is present too. |
| "Nesterenko's criterion is the keystone everything routes through" | **False as of 2018.** See above. |
| "Fischler's 0.21 and Lai–Yu's 1.19 are the same quantity" | **False.** Fischler counts **linearly independent** values; Lai–Yu 1.1925 → Lai 1.284 count merely **irrational** ones. Conflating them makes the field look ~6× faster than it is. |
| "Rhin–Viola group is 1920 for ζ(2), larger for ζ(3)" | **Inverted.** ζ(2) = 120, ζ(3) = 1920. |
| "Lai–Sprang–Zudilin's ζ₂(5) uses a Calabi–Yau 3-fold local system, which CDT concede is genuinely different" | **Fabricated.** LSZ is about **ζ₂(5)** (2-adic), uses *"exclusively the so-called totally symmetric hypergeometric approximations"*, and the CY content is a **speculative aside in the Final Remarks**. The attribution is also reversed: it is *LSZ* describing *CDT* as using "a different method." |
| arXiv:2101.08308 is Zeilberger's | **Dougherty-Bliss, Koutschan & Zeilberger**, Ramanujan J. 58 (2022). |
| arXiv:1802.09410 is Zudilin's | **Johannes Sprang solo.** |

**Verified true:** shifted Legendre polynomials *did* merge upstream (`Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean`, authored by the ζ(3) team). The ζ(3) *result* did not — only its lemmas.

### The confabulation risk is demonstrated, not hypothetical

During this survey a sub-model reported that Calegari proved ζ_p(3) irrational *"for small primes p (such as p = 2, 3, 5, 7)"*, with fluent supporting prose about why large p fails. The paper ([math/0408214](https://arxiv.org/abs/math/0408214)) says **p = 2 and 3**. The fabrication invented a specific false fact **at the boundary of what's known** — where it does maximum damage — and was more plausible-sounding than the truth. Caught only by pulling the PDF.

The Calabi–Yau claim in the table above is the *same failure mode, committed by the orchestrator*, after warning every agent about it. It was caught only because that warning was in the agent's prompt.

This matters for the verdict, not just hygiene: in a field with **no oracle**, where CDT's numerology clears by 5%, an agent's output is unverifiable prose in exactly the regime where confabulation is undetectable. The human failure mode is endemic too — Sprang needed a colleague to catch an error in a *Duke* paper; Suman iterated a wrong ζ(5) proof through **seven versions over ten months** ([2407.07121](https://arxiv.org/abs/2407.07121), withdrawn *"Found incorrect"*), and it took [ten mathematicians](https://arxiv.org/pdf/2411.16774) to collectively refute it.

**Treat math.GM as a red flag in this area. Never attack ζ(5) directly** — the productive framing is always "what does this *machinery* also prove."

---

## Adjacent question: does James Maynard's work help?

**No.** The real analogy is Maynard–Tao, not Duffin–Schaeffer: replace a 1-dim Selberg weight with a multidimensional F, let the support extend further, reduce to a variational problem, optimize numerically (Polymath8b did exactly this). Structurally similar to choosing R_n(t) and optimizing decay against growth.

It fails because **F is *free*** — constrained only by smoothness and support, which is what makes enlarging the space pay. Here R_n is **not** free: denominators must be controlled, and that arithmetic constraint forces the rigid well-poised/Pochhammer shapes. The space is small because arithmetic makes it small.

And **the move has already been made**: Fischler's Siegel's-lemma approach *is* "stop restricting to a hand-picked family, take the whole space, get existence by pigeonhole." It worked (log s → √(s/log s)), then hit non-vanishing and the multiplicity estimate. Not analysis.

Also worth heading off: **Guth–Maynard is about *zeros* of ζ(s); this field is about *values* ζ(3), ζ(5).** Unrelated questions sharing a letter. The prime-distribution input this field does need is *classical* (PNT with error term, sometimes only Chebyshev) — nobody's bound is limited by ignorance about primes.

---

## Sources

**Survivor:** [1801.09895](https://arxiv.org/abs/1801.09895) · [1802.09410](https://arxiv.org/abs/1802.09410) · [2503.07625](https://arxiv.org/abs/2503.07625) · [zeta_3_irrational](https://github.com/ahhwuhu/zeta_3_irrational) · [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) · [Zulip, Mar 2018](https://leanprover-community.github.io/archive/stream/113488-general/topic/odd.20zeta.20values.20irrational.html)

**Constructions & records:** [math/0206176](https://arxiv.org/pdf/math/0206176) · [Rhin–Viola AA 2001](https://www.math.ru.nl/~zudilin/zw/Rhin-Viola_AA_2001.pdf) · [1310.1526](https://arxiv.org/pdf/1310.1526) · [2512.12890](https://arxiv.org/abs/2512.12890) · [2109.10136](https://arxiv.org/abs/2109.10136) · [1412.6508](https://www.ihes.fr/~brown/IrratModuliMotivesv8.pdf) · [2210.03391](https://arxiv.org/abs/2210.03391) · [2601.00346](https://arxiv.org/abs/2601.00346)

**Holonomicity:** [2408.15403](https://arxiv.org/abs/2408.15403) / [PDF](http://www.math.uchicago.edu/~fcale/papers/L2chi.pdf) · [2510.04156](https://arxiv.org/abs/2510.04156) · [Dimitrov notes](https://people.maths.ox.ac.uk/newton/lnts/VDimitrov-LNT.pdf) · [Arbeitsgemeinschaft 2026](https://galoisrepresentations.org/2025/06/04/arbeitsgemeinschaft-2026/) *(use `.org` — the `.com` domain is hijacked)*

**p-adic:** [1809.07714](https://arxiv.org/abs/1809.07714) · [2306.10393](https://arxiv.org/abs/2306.10393) · [2505.05005](https://arxiv.org/abs/2505.05005) · [2505.23088](https://arxiv.org/abs/2505.23088) · [math/0408214](https://arxiv.org/abs/math/0408214)

**Search attempts:** [2101.08308](https://arxiv.org/abs/2101.08308) · [2108.06586](https://arxiv.org/abs/2108.06586) · [2404.04085](https://arxiv.org/pdf/2404.04085) · [Ramanujan Machine](https://arxiv.org/abs/1907.00205)

**Agents & formalization:** [2606.13925](https://arxiv.org/abs/2606.13925) · [1912.06611](https://arxiv.org/abs/1912.06611) (Coq) · [Tragicus/apery](https://github.com/Tragicus/apery)
