# Salvage of Sol's crashed ChatGPT session (overnight 2026-07-19/20)

Source artifacts (committed under `chatgpt/`): `Mathematical Theorem Review.pdf`
(22pp print of the session; most chat pages render blank from lazy-loading —
the mathematical content is on pp. 13–21) and three screenshots of the FINAL
message, which died mid-delivery on the conversation-length limit ("Message
delivery timed out" / "You've reached the maximum length for this
conversation"). Also recovered on disk: `worthiness/zeta7_dwork.tex/.pdf` (the
Dwork note Sol wrote in tmux and River uploaded to the session) — was never
lost, only untracked; now committed.

Status flags: [PROVEN-IN-REPO] already a theorem here; [CLAIMED-EXACT] Sol
states an exact identity, needs verification; [CLAIMED-PROOF] Sol sketches a
proof, needs reconstruction + verification; [IN-FLIGHT] idea Sol was testing
at crash, needs execution; [OPEN] Sol explicitly marks open.

## S1. The master reduction — carries removed [CLAIMED-PROOF, assembly rigorous]

With κ_p(n) = v_p(C(2n,n)) and P_n = (−1)^{n+1} p_n / C(2n,n), we have
identically v_p(P_n) = v_p(p_n) − κ_p(n), so the denominator-free descent
becomes the ONE-STEP statement with no Kummer carries anywhere:

    (D):  v_p(P_n) ≥ v_p(P_{⌊n/p⌋}) − 5        (p ≥ 5, all n).

Iterating (D) down the digit chain n → ⌊n/p⌋ → … → n_L < p gives
v_p(P_n) ≥ v_p(P_{n_L}) − 5L, L = ⌊log_p n⌋; then 2n_L < p ⟹ P_{n_L}
p-integral by Zudilin's denominator theorem, and n_L < p ≤ 2n_L ⟹ the
PROVEN Phase-1 Frobenius certificate supplies the missing factor. Either way
v_p(P_n) ≥ −5⌊log_p n⌋ — the full p ≥ 5 law. **The entire large/small-prime
distinction collapses to proving (D).** (PDF pp. 16–17.)

## S2. Normalized weight-(0,3,5) recurrence — fifth powers intrinsic [CLAIMED-EXACT]

Substituting x_n = (−1)^{n+1} C(2n,n) Y_n into Zudilin's common third-order
recurrence (Zu02: Q_n, P_n, P̂_n are companion solutions), Sol derives (PDF
p. 17, some rendering garbled — re-derive):

    2(n+1)^5 (2n+1) a₀(n) Y_{n+1} − a₁(n) Y_n − 2n a₂(n) Y_{n−1}
        + n (n−1)^5 a₀(n+?) Y_{n−2} = 0,

i.e. the loss of exactly FIVE p-adic orders per digit descent is built into
the normalized recurrence, not an experimental fit. The three normalized
solutions form a filtered rank-3 system with weights 0, 3, 5.

## S3. Exact Casoratian [CLAIMED-EXACT]

For the fundamental matrix 𝒴_n of (Q, P, P̂) the determinant telescopes to

    det 𝒴_n = (−1)^n · a₀(n) / ( 4 (n−1)^5 n^6 C(2n,n) )     (PDF pp. 17–18),

"the apparently troublesome cubic a₀ telescopes almost entirely" — evidence
the right arithmetic object is the full solution lattice.

## S4. THE CLAIMED THEOREM (the one River feared lost): the Lucas–Frobenius
## q-row [CLAIMED-PROOF — likely fully provable, certificate-shaped]

With Brown–Zudilin's manifestly integral double-binomial formula

    Q_n = Σ_{k,l=0}^{n} C(n+k,n) C(n,k)² C(n+l,n) C(n,l)² C(n+k+l,n),

Lucas' theorem gives, for 0 ≤ r < p:

    **Q_{ap+r} ≡ Q_a · Q_r  (mod p).**

Proof sketch (PDF p. 18): write k = bp+s, l = cp+t; Lucas factorizes each
binomial into high/low digit factors; any low-digit carry kills the summand
mod p; the surviving summand factorizes into its (a,b,c) and (r,s,t) pieces;
summing over digit boxes gives the product. This is the first row of the
desired Frobenius matrix, rigorous — exactly the "bootstrap from the q-row."

## S5. The specified missing theorem [OPEN — precisely stated]

Saturated filtered vector V_n^{(p)} = (q_n, p^{3L_p(n)} p̃_n, p^{5L_p(n)} p_n)
(weights 0,3,5) with a denominator-free block Frobenius law

    V_{ap+r}^{(p)} = Φ_r(a) V_a^{(p)} + p E_{a,r},   Φ_r(a) ≡ upper-triangular
    with diagonal (Q_r, Q_r, Q_r) mod p,

in the appropriate saturated ℤ_p-lattice. Its last row, after saturation, IS
(D); the two-digit cocycle Φ_{sp+r}(ab) ≡ Φ_r(·)Φ_s(·) makes iteration
automatic. Division by q_a is FORBIDDEN (exceptional primes 7 | q₁ = 42);
the structural reason p_n is not a scalar "fifth derivative" of Q_n:

    (q_n, p_n, p̃_n) = (u, w, v) × (ũ, w̃, ṽ)     [cross product / 2×2 minors]

so the needed deformation is two-row/matrix-valued (screenshot 2). The gain
lives in ∧²V: V_n ∧ V_a ≡ 0 (mod p) — bilinear, matching the L2SPAN verdict.

## S6. Why the final arrow is open [OPEN]

Two sufficient ingredients, neither yet constructed (PDF p. 19):
(i) a parameterized period family 𝒬_n(ε) = Q_n + … + ε³P̂_n + … + ε⁵P_n + …
with Frobenius identity 𝒬_{ap+r}(ε) ≡ 𝒬_r(ε)·𝒬_a(pε) (mod p) — coefficient
extraction at ε⁵ then proves (D); or (ii) direct block expansion of Zudilin's
hypergeometric companions through harmonic weight 5 (the zeta7_dwork.tex
program: block expansion, (p_n, p̃_n) simultaneously, triangular matrix, then
general digit a).

## S7. IN-FLIGHT SHORTCUT #1 — desingularization [IN-FLIGHT, potentially decisive]

From screenshot 2 (final message): "the cubic a₀(n) is definitely an apparent
singularity and can be removed. I'm now testing whether the remaining midpoint
factor 2n−1 is apparent too. **If it desingularizes, the leading coefficient
becomes essentially n⁵, and the entire p ≥ 5 denominator theorem follows by
ordinary d_n⁵-induction — no unproved Dwork theorem at all.**" Sol did not
finish this test. It is pure computer algebra (ore_algebra-style
desingularization of the normalized order-3 operator) — EXECUTABLE NOW.

## S8. IN-FLIGHT SHORTCUT #2 — the order-2 Barnes kernel [IN-FLIGHT]

From screenshot 3: specializing Brown–Zudilin's Barnes double integral to the
symmetric family collapses the Gamma factors to

    R_n(s,t) = n! · (s+1)_n (t+1)_n (s+t+n+2)_n
               / [ (s+n+1)²_{n+1} (t+n+1)²_{n+1} ]

times the universal sine kernel π³ / (sin πs · sin πt · sin π(s+t)). Poles
have order only 2 per variable, polynomial coupling; the weight-5 denominator
should split into ≤ 2 Laurent derivatives + ≤ 3 harmonic/integration
denominators — "it avoids the non-integral order-six partial fractions that
killed the linear certificate route." Sol was working this out at crash.

## S9. Remaining even after (D) [known]

The {2,3} fixed losses v₂(A_n) ≥ v₂C(2n,n) − 2, v₃(A_n) ≥ v₃C(2n,n) − 1 are
separately needed for the factor 12 = 2²·3 (PDF pp. 19–20).

## S10. Sol's rigorous-boundary summary at crash (PDF p. 20)

Phase 1 proved + Q-row Lucas Frobenius + exact (0,3,5) recurrence + exact
Casoratian + linear certificates provably insufficient ⟹ full p ≥ 5 theorem
⟺ the single descent (D). "I do NOT yet have a proof of that last descent.
Calling the Brown–Zudilin law proved at this point would simply conceal the
open vector-Dwork theorem inside an unproved Frobenius assertion."

## Salvage verification campaign (dispatched 2026-07-20)

V1 cross-product identity + normalization Q_n = (−1)^{n+1} q_n / C(2n,n);
V2 the double-binomial formula vs exact q-data; V3 Lucas congruence grid +
proof reconstruction; V4 recover/verify the third-order recurrence and its
normalized weight-(0,3,5) form; V5 Casoratian; V6 the desingularization test
(S7 — priority); V7 (D) itself on a wide grid incl. exceptional primes;
V8 Barnes kernel anchor check (S8). Results: PHASE2_SALVAGE_VERIFY.md.
