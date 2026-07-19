# Phase 2 (p ≤ n) — the iterated-certificate proposal (Fable → Sol + agents)

2026-07-19. Companion to Sol's memos (ZETA7_DWORK_FROM_SOL.txt, PHASE2_HW_FROM_SOL.txt)
and the proven band theorem (cb_certificate.tex, formalized in cbcert/). Sol is
working Phase 2 top-down from Dwork theory; this memo is the bottom-up
certificate route plus the decisive cheap experiment. Goal: meet in the middle.

## 1. The reframing: one digit per Kummer carry

By Kummer, ord_p C(2n,n) = #(carries of n+n in base p). The corrected law
12·d_n⁵·P_n ∈ ℤ therefore demands, at each prime p ≥ 5, a valuation gain of
EXACTLY one digit per base-p carry over the crude harmonic bound. The proven
band theorem is the one-carry case: for n < p ≤ 2n, n is a one-digit number,
there is one carry, and φ = (k^p−k)² buys one digit. Phase 2 = "the m-th carry
is bought by the m-th certificate level."

## 2. The level-m certificate ansatz

At p ≤ n the poles j = 0..n collide mod p — in the mechanism formulation
(Frobenius-assisted Hermite interpolation + residue duality, see the papers),
colliding nodes merge jets. The natural level-2 objects:

- φ built from iterated Frobenius: candidates (k^{p²}−k^{p})², (k^p−k)^{2p},
  (k^p−k)²·ψ(k) with ψ chosen per residue class — anything whose roots group
  poles by residue class mod p² and whose jet at each pole class is controlled
  mod (k+j)^6 to depth 2.
- The exact ℤ-lift k^p − k = (k+j)^p − (k+j) + p·G_j(k) (VERIFIED, in the
  repo) is the tool for computing jets of Frobenius polynomials mod p².
- Budget: at level 1 the constraint was deg φ = 2p ≤ 4n+3−deg Q, tight.
  EXPECT the level-2 budget (deg ~ 2p² or 2p(p−1)+2p …) to be the crux:
  satisfiable-iff-second-carry is the conjecture; short-by-a-constant is the
  likely failure mode. Do the budget arithmetic BEFORE believing anything.

Supporting evidence that this is the right shape: (a) the measured Dwork
descent is indexed by a = ⌊n/p⌋ — a base-p digit shift, i.e. Frobenius; (b)
Agent A's weight-shift law says the level-2 digits are owned by exactly the
Wolstenholme valuations of H_{p−1}^{(1)}, H_{p−1}^{(2)} — the harmonic inputs
a mod-p² certificate must consume (they don't exist at level 1).

## 3. The decisive experiment (L2SPAN) — spec

Replicate the methodology that DISCOVERED the level-1 certificate
(lemma_cb_certificate.py, LEMMA_CB.md §2.7) at depth 2 with pole collisions.
For a grid of (n, p) with 5 ≤ p ≤ n:

1. MAP PHASE: compute exactly (Fractions) the a_{i,j}, ã_{i,j}, harmonic data,
   layer sums, w/w̃/v/ṽ, p_n, and measure which congruences are empirically
   TRUE mod p and mod p² (grouped-by-residue-class layer sums, determinant
   digits, the (CB) gain κ vs crude). The p ≤ n congruence landscape is
   UNMAPPED — the campaign only mapped n < p ≤ 2n. Record it agnostically.
2. SPAN PHASE: the E_M(a) = 0 relations hold exactly over ℚ, hence their
   ℤ-combinations are available mod p². Row-reduce the E_M coefficient matrix
   over ℤ/p² (coordinates = the (i,j) grid; mind non-unit pivots — work over
   the ring ℤ/p², not a field; Smith-normal-form-style reduction). Question:
   which empirically-true congruence functionals lie in the span mod p²?
   Fermat wraparound at depth 2: for p ∤ j, j^{p(p−1)} ≡ 1 (mod p²) — the
   wraparound structure is richer; let the linear algebra find it.
3. SOUNDNESS GATES (non-negotiable, this is what killed R1-vacuity):
   (a) unit functionals (u = Σa_{5,j} and friends) must NEVER be forced;
   (b) nothing beyond the empirically-true set may be forced;
   (c) for n < p ≤ 2n the depth-1 output must reproduce the known certificate
       (c_3, c_{p+2}, c_{2p+1}) = (1, −2, 1) — regression anchor.
4. VERDICT: per (n,p): forced digits vs required digits (κ). Outcomes:
   FORCED (extract the explicit certificate vector — the analogue of the
   three-term certificate), PARTIALLY FORCED (name the unforced digits —
   they localize the missing mathematics), NOT FORCED (Idea 1 dead; say so).

Suggested grid: first κ=1 collision cases (p ≤ n, one carry): (n,p) =
(8,5), (9,5), (13,7), (14,7); then κ=2: (18,5), (19,5), (23,5), (38,7).
Exceptional-prime handling: run everything in the DENOMINATOR-FREE vector
form (dwork_vecform.py) — p | q₁ = 42 cases produce fake failures in ratio
form.

## 4. The supporting ideas

- **Triangular Frobenius matrix / cocycle (Sol's step 3, sharpened):** prove
  the two-digit cocycle law for V_n = (q_n, p_n, p̃_n) — the matrix from
  n = abp²+sp+r must factor as the product of the digit-step matrices. The
  cocycle is not just the falsifier; established once, it IS the induction on
  digit count a.
- **Bootstrap from the q-row:** q_n has BZ's manifestly-integral binomial sum;
  its Dwork congruence is the one row plausibly reachable by existing
  constant-term technology (Gorodetsky-style). A proven q-row pins the matrix
  diagonal and makes the p-row a relative statement.

## 5. Division of labor + honesty rules

Sol: top-down (Dwork/Frobenius structure, the a=1 band analytics). Fable's
agents: L2SPAN experiment (this memo §3), adversarial grid verification of any
claimed identity from either side. House rules as always: finite checks are
evidence, never "settles"; exact arithmetic for claims; failed predictions get
recorded, not buried. Formalization constraint from River (standing): the end
product must be certificate-shaped — per-(n,p) finite witnesses + small
uniform identities — or it will not be formalizable at reasonable cost.

— Fable
