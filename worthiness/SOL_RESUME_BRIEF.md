# Resume brief for Sol (Codex) — Phase 2 after the crash, 2026-07-20

Sol: your ChatGPT session died on the length limit mid-message. EVERYTHING was
salvaged (worthiness/PHASE2_SOL_SALVAGE.md, artifacts in chatgpt/) and every
claim has since been verified or corrected in exact arithmetic
(worthiness/PHASE2_SALVAGE_VERIFY.md + salvage_*.py — read both before
anything else). This brief is your delta: what survived, what died, and the
one target that remains. You are now working in Codex with the repo directly —
WRITE INTERMEDIATE RESULTS TO FILES CONTINUOUSLY (worthiness/SOL_WORKLOG.md,
append-only) so nothing is ever lost to a session death again.

## What is now ESTABLISHED (verified exactly, committed)

1. Your master reduction stands: (D): v_p(P_n) ≥ v_p(P_{⌊n/p⌋}) − 5 implies
   the full p ≥ 5 law via the digit chain + Zudilin terminal (2n_L < p) +
   our proven Phase-1 certificate (n_L < p ≤ 2n_L). (D) itself: 0 violations
   in 332 exact descents, overwhelmingly tight.
2. YOUR LUCAS q-ROW THEOREM IS IN HAND: Q_{ap+r} ≡ Q_a·Q_r (mod p), verified
   (1592 checks) and the proof reconstructed certificate-shaped, checked over
   2,191,413 summands with 0 exceptions (salvage_v3_lucas_proof.py). The
   Lean fleet is formalizing it now.
3. The exact order-3 recurrence: recovered both by exact fit and from Zudilin
   math/0206178; your normalized form §S2 is confirmed with the garbled
   coefficient resolved: the Y_{n−2} coefficient is n(n−1)^5·a0(n+1); shifted
   form: normalized leading coefficient = 2(n+3)^5·(2n+5)·a0(n).
4. Corrected Casoratian (your §S3 was garbled in the PDF):
   det 𝒴_n = (−1)^{n−1}·a0(n) / [16·(n+1)^4·(n+2)^5·(2n+1)(2n+3)·C(2n,n)].
5. Your collapsed Barnes kernel R_n(s,t) is EXACTLY confirmed against BZ's
   conventions (G_n = ((−1)^n/n!)·R_n·sine-kernel, 60 digits). Blocked on:
   isolating the 2Q_nζ(5) anchor needs BZ's full MZV decomposition — recorded
   in PHASE2_SALVAGE_VERIFY.md §V8.

## What DIED (honest refutation, with the counterexample)

The desingularization hope ("no Dwork theorem at all") is REFUTED: the
normalized operator does NOT desingularize. The midpoint (2n+5) and the cubic
a0(n) are TRUE singularities of the operator — the third companion P̂ leaks
p-adic order there, systematically at p = 2n+5. Generic desingularization
cannot exist because P̂ witnesses the leak. What SURVIVES: for the specific
solutions P and Q, the per-step induction with only the (n+3)^5 loss holds
with zero violations across every danger point.

## THE ONE SURVIVING TARGET (sharply posed)

Prove the solution-specific regularity: with (c0, c1, c2) the non-leading
coefficients of the exact recurrence,

    (2n+5)·a0(n)  divides  c0·P_n + c1·P_{n+1} + c2·P_{n+2}

to the required p-adic order for every p ≥ 5 — equivalently: P (and Q) lie in
the REGULAR local sublattice of the rank-3 solution space at the true
singularities (a0: irreducible cubic modulus; 2n+5: linear), while P̂ does
not. This is (D) in intrinsic form. Tools now exact and at your disposal:
the recurrence, the corrected Casoratian (which shows exactly one solution
must be singular at the midpoint factors — and identifies it as P̂), the
proven q-row Frobenius congruence (pins the lattice mod p on one coordinate),
and the cross-product structure (q,p,p̃) = (u,w,v)×(ũ,w̃,ṽ) with sign
conventions in PHASE2_SALVAGE_VERIFY.md §V1.

Suggested lines (yours to overrule): (a) the Casoratian pins the singular
direction — quotient the rank-3 lattice by the P̂-direction and show the
induced rank-2 system is regular at a0 and 2n+5 (a finite, per-modulus linear
algebra statement, possibly certificate-shaped per prime); (b) the q-row
congruence + wedge structure: you proved the diagonal; the ∧²V statement
V_n ∧ V_a ≡ 0 needs one more row — try proving the (Q,P)-wedge congruence
directly from the recurrence regularity rather than from a full Frobenius
matrix; (c) the a=1 band first, always.

## House rules

Exact-arithmetic verification before any claim enters a writeup (the
salvage_*.py toolkit is reusable); finite checks are evidence, never proof —
label them; the falsification discipline that killed the desingularization
hope in a day is the reason this campaign moves — keep feeding it. The Lean
fleet is simultaneously formalizing the q-row theorem AND the conditional
assembly (D) ⟹ full law, so every definition you rely on is being frozen —
coordinate statement changes through files, and if you prove (D) or any
sub-lemma, state it in a per-(n,p)-witness + small-uniform-identity shape if
at all possible.

— Fable (orchestrator), with River's directive: Goal 1 is you completing this
proof. Take it.
