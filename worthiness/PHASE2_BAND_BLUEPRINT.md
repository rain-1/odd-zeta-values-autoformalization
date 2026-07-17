# Phase-2 band proof blueprint: the p-adic linear form (Fable, 2026-07-18 ~00:30)

Target: (CB) at band primes n/2 < p ≤ 2n/3 (κ = ord_p binom(2n,n) = 1, L = ord_p d_n = 1):
**ord_p(p_n) ≥ −4** (Zudilin gives ≥ −5; need exactly +1).

## Reduction 1 (proved, elementary): PROX ⟸ a universal p-adic zeta relation

The three 2×2 minors of [[u,w,v],[ũ,w̃,ṽ]] are (q_n, ±p̃_n, ±p_n) (cross product).
If constants ρ_p, σ_p ∈ ℚ_p (n-INDEPENDENT) exist with

    (Z_p)   v_n ≡ ρ_p u_n + σ_p w_n   and   ṽ_n ≡ ρ_p ũ_n + σ_p w̃_n   (mod p^θ)

then p_n = w̃v − wṽ = ρ_p(uw̃ − ũw) + O(p^{θ−2}) = ρ_p q_n + O(p^{θ−2})
(using ord w, ord w̃ ≥ −2, Zudilin). With ord_p q_n ≥ κ (FREE — Q_n is BZ's
integer sumQ) and ord ρ_p ≥ −5:

    ord_p(p_n) ≥ min(κ − 5, θ − 2).

**Band case: θ = −1 suffices** (then ord p_n ≥ min(−4, −3) = −4 ✓). Since
ord v = −5, (Z_p) at θ = −1 demands gaining FOUR orders... no: (Z_p) means the
COMBINATION v − ρu − σw has ord ≥ −1 while v alone has −5: the constants must
absorb the whole singular part. Equivalently: **the p-singular part of v_n
(depth p^{-5}..p^{-1}) is ≡ (singular part of ρ_p)·u_n + (singular part of
σ_p)·w_n — universal multiples of u and w.** This is the actual claim to prove.

## Reduction 2 (derived, verify): singular parts are head-window functionals

Write n = p + r, 0 ≤ r < p/2. Only multiple of p in [1, n] is p itself. Then:

(a) H-singularities: H_j^{(i)} = Ĥ_j^{(i)} + [j ≥ p]·p^{-i} with Ĥ p-integral.
    So v ⊃ Σ_i p^{-i}·S_i^{tail}, S_i^{tail} = Σ_{j≥p} a_{i,j} =
    (−1)^{i+1} S_i^{head}, S_i^{head} := Σ_{j=0}^{r} a_{i,j} (reflection P1).
(b) a-singularities: a_{i,j} = B_j^{(6−i)}(−j)/(6−i)! where the log-derivative
    of B_j at −j has p-denominators ONLY from the four collision sources:
    m = j±p in the pole product (order-6 factors), j' = j−r and j' = j+p−r in
    the (k+n+j') product, m = j−p, j+p in the (k−m) product. Each derivative
    order picks ≤ 1 extra p. All collision couplings relate node j to nodes in
    the head window [0, r] or its reflection.
(c) Wolstenholme input: H_{p−1}^{(1)} ≡ 0 mod p², H_{p−1}^{(2)} ≡ 0 mod p,
    H_{p−1}^{(3)} ≡ 0 mod p², H_{p−1}^{(4)} ≡ 0 mod p, H_{p−1}^{(5)} ≡ 0 mod p²
    (p ≥ 7; standard). These control Ĥ_j for j ≥ p: Ĥ_j^{(i)} ≡ H_{j−p}^{(i)}
    shifted-block mod p^{1..2}.

Conjecture (to verify then prove): after subtracting the universal-constant
multiples of u_n and w_n built from p^{-i}·(Wolstenholme block constants), the
remaining singular functional vanishes BECAUSE the head-window sums S_i^{head}
and the collision couplings satisfy Frobenius-certificate-type congruences on
the window [0, r] (length r < p: distinct nodes — certificate territory; the
relevant degree budget must be re-derived for window sums, NOT full sums).

## Verification stages (agent):

V1. Exact decomposition check: compute v_n − Σ_i p^{-i}(−1)^{i+1}S_i^{head} and
    report its ord_p across the band table (expect ≥ −4 or the a-singular
    residue); tabulate ord_p of each S_i^{head}.
V2. Solve for the putative constants: at fixed p with ≥ 2 band n's, solve the
    2×2 system per n for (ρ_n, σ_n) mod p-powers where invertible (det q_n has
    ord κ — quantify the precision loss), test n-independence; ALSO test
    p̃_n ≡ ρ̃_p q_n with the SAME ρ-family (third-minor consistency).
V3. Identify the constants: compare ρ_p, σ_p digits against candidate
    Wolstenholme-block expressions: p^{-i}H-blocks, Fermat quotients q_p(2),
    Bernoulli B_{p−3}, B_{p−5} mod p (the standard basis for such constants).
V4. If V1–V3 hold: reduce to the finite list of head-window congruences that
    must be proved; check each against the E_M/Frobenius machinery on [0, r].

## Status

- Reduction 1: proved above (elementary determinant estimate), MODULO existence
  of the constants — which is the content.
- Reduction 2(a): proved (reflection). 2(b): derivation sketched, verify.
- Everything else: conjecture with a concrete verification path.
- The measured facts feeding this: universal ρ_p (1–4 digit agreement across n,
  lemma_cb_phase2_univ.py); w/u ≡ w̃/ũ mod p (dissection run); slack-0 tightness.

## BREAKTHROUGH ADDENDUM (2026-07-18 ~01:10, Fable)

The V3 constants are IDENTIFIED EXACTLY: ρ-unit = 29/28 = p₁/q₁ and σ-unit =
101/84 = p̃₁/q₁ — the n=1 LADDER RATIOS (exact determinant check at n=1).
Digit-2 prediction (n = 2p+r ⟹ constant p₂/q₂ = 24289/23424) CONFIRMED:
5 p-adic digits at p=5 (n=11,12), 3–4 at p=11 (n=23,24). Exceptional primes =
those dividing the digit-constant denominators (7 | 28, 84): need renormalized
statement. The general mechanism is a DWORK CONGRUENCE:

    p_n/q_n ≡ (p_a/q_a)·p^{-5}  mod p^{θ},  a = ⌊n/p⌋,

and Phase 2 reduces (pending the θ-law, agent stage V5) to proving this — a
known-technology statement (Dwork Frobenius structure; Delaygue–Rivoal–Roques;
Malik–Straub Lucas congruences for Apéry-like sequences). The p^{-5} factor is
the harmonic-layer depth of the outer digit; the archimedean limit of the same
ratio is ζ(5) — one ratio, two completions, same digit structure.
