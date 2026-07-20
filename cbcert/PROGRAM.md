# The ζ(5) denominator program — proof-dependency skeleton and formalization ladder

**Status: written down and SHELVED (River's directive, 2026-07-19).** Layers L0–L4
are active or in flight; L5 is cheap and deferred; L6 is open mathematics and is
*not* to be formalized until it exists on paper. The governing filter for all
future work in this program: **is it certificate-shaped?** (finite witness per n
plus a small uniform identity — the shape that formalizes).

## The mathematical story (one paragraph)

Brown–Zudilin (arXiv:2210.03391) print an experimental integrality claim
`d_n⁵·P_n ∈ ℤ` for the rational coefficients of their weight-5 linear forms; the
paper's own displayed symmetric value P₂ = 1190161/384 violates it — by exactly
12. The corrected law is `12·d_n⁵·P_n ∈ ℤ`, with the {2,3}-ceilings sharp, and
the constant 12 = 24/2 carries content: the Bernoulli/(2πi)²-lattice cost of the
ζ(2)-elimination (24) divided by a located Betti lattice index (2) of the
M̄₀,₈ motive. Chasing the proof produced a genuinely new technique — the
**Frobenius certificate** (`worthiness/cb_certificate.tex`): for every prime
n < p ≤ 2n (p ≥ 5), the identity φ = (k^p−k)² ≡ (k+j)² mod (k+j)⁶ at every pole,
plus deg φ = 2p ≤ 4n+2 and the residue-sum theorem on ℙ¹, forces the harmonic
functionals w_n, w̃_n ≡ 0 (mod p), whence the band theorem (CB₁): p | p_n.

## The ladder

```
L0  Definitions                                             [cbcert — DONE]
    R_n, partial fractions a_{i,j}, ã_{i,j}, harmonic sums H_j^{(i)},
    functionals u,w,v (+tilded), ladders q_n, p_n, p̃_n, d_n = lcm(1..n).
    All finite ℚ-objects. Cbcert/Defs.lean (+ Numeric.lean gate). Source: SPEC.md.

L1  Decay relations                                         [cbcert Lemma A — DONE]
    E_M(a) = 0 for 1 ≤ M ≤ 4n+4 (resp. 4n+2 tilded): the Laurent expansion of
    R_n at ∞. Cbcert/{PartialFraction,Decay}.lean — proved via the cleared PF
    identity + an elementary power-series (ℚ⟦X⟧) route, E_M(a)=[X^M]R_n(1/X)=0.

L2  Certificate identity                                    [cbcert Lemma B — DONE]
    Three-term certificate (c₃, c_{p+2}, c_{2p+1}) = (1, −2, 1) in ZMod p:
    pure binomial arithmetic (x^p = x, p | C(p,m), C(−i,r) signs).
    Cbcert/Certificate.lean. The mathematically new part.

L3  Assembly                                                [cbcert main — DONE]
    p-integrality (Lemma C, Cbcert/Integrality.lean) + L1 + L2 ⇒ (W): p | w_n, w̃_n
    for n < p ≤ 2n ⇒ (CB₁): p | p_n. Cbcert/Main.lean (residue map + ZMod-p
    reordering). Canonical theorems res_congruence_{w,wt,pn}, kernel-clean.
    SCOPE NOTE: general nonvanishing w_n,w̃_n,p_n ≠ 0 is explicitly OPEN (not needed
    for the residue-form theorems; only sharpens the padicValRat disjunct).

L4  Error exhibit                                           [in flight, 2026-07-19]
    Construction-derived P₂ = 1190161/384; ¬(d₂⁵·P₂ ∈ ℤ);
    sharp characterization (c·d₂⁵·P₂ ∈ ℤ ⟺ 12 | c); paper display
    cross-references in docstrings. Companion P̂₂ factor-2 failure optional.
    Module: CBCert/ErrorExhibit.lean.

L5  Finite-range corrected law                              [DONE n=2..8, 2026-07-19]
    12·d_n⁵·P_n ∈ ℤ (P_n = (−1)^{n+1} p_n/C(2n,n)) kernel-verified per n, one
    file per n (`Cbcert/FiniteLaw/N⟨n⟩.lean`) so lake parallelizes and ranges
    split across machines. Aggregate `law_upto : ∀ n∈Icc 2 8, CorrectedLaw n`
    (`Cbcert/FiniteLaw/All.lean`), axioms std, no native_decide, no sorry. Free
    byproduct `pn_ne_zero_⟨n⟩` upgrades `Main.pn_valuation`'s disjunct to the
    sharp form on the verified range. House rule (no native_decide) makes N
    compute-bound: norm_num kernel reduction grows ~1.8×/step (n=8 ≈ 35 min).
    Ground-truth gate `scripts/l5_gate.py` (exact Fractions, n=2..24 all integral
    — corrected law NOT falsified). Extend: `scripts/l5_gen.py NSTART NEND` +
    `scripts/l5_remote.sh HOST NSTART NEND` (remote-ready, point at kbld once
    SSH exists). Pure engineering on top of L0.

L6-staging  Two theorems landed (wave 1, 2026-07-20)         [cbcert — DONE, sorry-free]
    T1 Cbcert/LucasRow.lean: the Lucas–Frobenius q-row congruence
       `Q(ap+r) ≡ Q a · Q r (mod p)` (p prime, r<p) for the Brown–Zudilin
       double-binomial `Q_n` — the FIRST ROW of the Frobenius matrix, now a Lean
       theorem (Mathlib's Lucas + base-p reindex + carry-kill factorization).
    T2 Cbcert/Assembly.lean: Sol's master reduction as `descent_law`, with the open
       descent `hD` (= verified (D), salvage_v7 332/0) an EXPLICIT hypothesis.
       Conclusion `v_p(P n) ≥ −5·⌊log_p n⌋` for all n≥1, p≥5, proved by digit-chain
       induction with the terminal cases discharged from the PROVEN cbcert band +
       one-digit Kummer. `sorryAx`-free (hD is a hypothesis, not an axiom): **the
       whole p≥5 corrected law is now exactly one hypothesis (`hD`) away.** This is
       the assembly skeleton onto which any future proof of (D) drops in directly.

L6  The open mathematics                                    [BLOCKED — no paper proof]
    What a full `12·d_n⁵·P_n ∈ ℤ` theorem for ALL n still needs, in order:
    (a) q_n ∈ ℤ uniformly (cited from BZ cellular integrality; a formalizable
        route needs the manifestly-integral sum formula + an identity proof);
    (b) the a=1 band: symbolic-in-r closure of the weight-5 jet
        Q_HW ≡ 0 (mod p⁵). Status: grid-verified (86 pairs, p = 11..37, zero
        exceptions, ord ≥ 5 uniform); digit ownership known (weight-shift law:
        digits c₁, c₂ ⟺ Wolstenholme valuations of H_{p−1}^{(1)}, H_{p−1}^{(2)};
        reversal identity enters only c₃..c₅); OPEN: the chamber/interval
        residuals C₁ = C₂ = 0 symbolically. See worthiness/PHASE2_DWORK_HW.md,
        PHASE2_DWORK_ASSEMBLY.md, PHASE2_HW_FROM_SOL.txt.
    (c) head-window → full descent: the mod-p⁵ jet is a *shadow* of, not
        equivalent to, the descent floor ord_p(Δ₅) ≥ ord_p(q₁)+2 — the regular
        residual, companion determinant, and q-coordinate are separate
        obligations (Sol, PHASE2_HW_FROM_SOL.txt T1).
    (d) general digit a (the full Dwork-style descent; cocycle law for two
        digits is the decisive matrix test — worthiness/PHASE2_DWORK_A1.md §3).
    DESIGN REQUIREMENT for whoever resumes this: find certificate-shaped
    formulations (per-(n,p) finite witnesses + small uniform identities), as
    was done for L2/L3. The current jet/chamber formulation is not yet that
    shape, which is exactly why it is shelved.
```

## Effort estimates (2026-07-19 fleet velocity)

L0–L3: weeks (spec exists, scaffold green, certificate core is finite).
L4: days (in flight). L5: days of engineering + compute. L6: open-ended
mathematics; formalization cost unknowable until the paper proof exists.

## Provenance / key artifacts

- Paper (proven, band theorem): `worthiness/cb_certificate.tex` (+ check script,
  420 (n,p) pairs).
- Spec: `cbcert/SPEC.md`. Template project: `zeta5odd/` (kernel-verified
  odd-zeta theorem; comparator + blueprint packaging patterns).
- Error finding and corrected-law evidence: `worthiness/CONJECTURE.md`
  (103+ cells, {2,3}-ceilings attained; one boundary-prime ν-caveat at p=7).
- (DWORK)/jet campaign record: `worthiness/PHASE2_*` + Sol memos
  (`ZETA7_DWORK_FROM_SOL.txt`, `PHASE2_HW_FROM_SOL.txt`).
