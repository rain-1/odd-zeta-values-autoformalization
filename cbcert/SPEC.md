# cbcert — Lean 4 formalization of the Frobenius-certificate theorem (Tier 1)

Target paper: `worthiness/cb_certificate.tex` (proven, refereed). Template
project: `zeta5odd/` (complete, kernel-verified, std axioms — copy its lakefile/
toolchain/CI patterns). Repo honesty rules apply: no sorries in main line at
completion; finite checks live in a separate Numeric module.

## The theorem to formalize (self-contained, no Zudilin import needed)

For n ≥ 1 define (all in ℚ):
- R_n(k) = (n!)^4 (k + n/2) ∏_{j=1}^n (k−j) ∏_{j=1}^n (k+n+j) / ∏_{j=0}^n (k+j)^6
- a_{i,j} (1≤i≤6, 0≤j≤n): the partial-fraction coefficients,
  R_n = Σ_{i,j} a_{i,j}/(k+j)^i; equivalently a_{i,j} = T_{6−i}(j)/(6−i)! where
  T_m(j) is the m-th Taylor coefficient of B_j(k) := (k+j)^6 R_n(k) at k = −j.
- ã_{i,j} := j(n−j)a_{i,j} + (2j−n)a_{i+1,j} − a_{i+2,j} (indices >6 are 0)
  [the partial fractions of −k(k+n)R_n].
- w_n = Σ_j a_{3,j}, w̃_n = Σ_j ã_{3,j};
  H_j^{(i)} = Σ_{m=1}^j 1/m^i;
  v_n = Σ_{i,j} a_{i,j}H_j^{(i)}, ṽ_n = Σ_{i,j} ã_{i,j}H_j^{(i)};
  p_n = w̃_n v_n − w_n ṽ_n.

MAIN THEOREM (two parts), for every prime p with n < p ≤ 2n and p ≥ 5:
  (W):     padicValRat p w_n ≥ 1  ∧  padicValRat p w̃_n ≥ 1
  (CB₁):   padicValRat p p_n ≥ 1
(the second follows from the first by Prop 1 of the paper: p-integrality of all
a, ã, H for p > n plus the determinant estimate; no Zudilin denominator theorem
is needed).

## Proof architecture (from the paper; Lean-adapted)

KEY DESIGN: the certificate core needs NO rational functions — it is three-term
binomial congruences. Only the E_M relations need Laurent/partial-fraction
machinery.

E_M(b) := Σ_{i=1}^{min(6,M)} C(−i, M−i) · Σ_j j^{M−i} b_{i,j}, where
C(−i, r) = (−1)^r · C(i+r−1, r)  (integer).

Lemma A (decay; over ℚ): E_M(a) = 0 and E_M(ã) = 0 for 1 ≤ M ≤ 4n+4
(resp. ≤ 4n+2 for ã — check the exact range: ord_∞(−k(k+n)R_n) = 4n+3, so
E_M(ã)=0 for M ≤ 4n+2; the certificate needs M ∈ {3, p+2, 2p+1} ≤ 2n+2+... —
verify p ≤ 2n gives 2p+1 ≤ 4n+1 ≤ 4n+2 ✓).
  Route: RatFunc ℚ → LaurentSeries embedding (Mathlib: RingTheory.LaurentSeries);
  ord_∞ R_n = 4n+5 from degree count; expansion of (k+j)^{-i} termwise.

Lemma B (certificate identity; pure binomial arithmetic mod p): for p ≥ 5,
i ∈ 1..6, and every x ∈ ZMod p:
  Σ_{M ∈ {3, p+2, 2p+1}} c_M · C(−i, M−i) · x^{M−i} = δ_{i,3}   in ZMod p,
  with (c_3, c_{p+2}, c_{2p+1}) = (1, −2, 1) — terms with M−i < 0 omitted.
  Proof ingredients (all in Mathlib): x^p = x (ZMod.pow_card), C(p,m) ≡ 0 for
  0<m<p (Nat.Prime.dvd_choose), C(−i,r) sign formula. This encodes
  φ = (k^p−k)² ≡ (k−x)² mod (k−x)^6. Equivalent per-(i,x) computation:
  C(−i, 3−i)x^{3−i} − 2C(−i, p+2−i)x^{p+2−i} + C(−i, 2p+1−i)x^{2p+1−i} = δ_{i,3}.

Lemma C (p-integrality): for p > n: every a_{i,j}, ã_{i,j}, H_j^{(i)} (j ≤ n)
has padicValRat ≥ 0. Route: the Taylor/derivative formula for a_{i,j} has
denominators only from (m−j) with |m−j| ≤ 2n... (spell out: log-derivative
factors (−j−m)^{-1} etc., all with absolute value ≤ 2n < 2p, none ≡ 0 mod p
since p > n and the only multiples of p in [1,2n] is p itself — CAREFUL: values
n+j'−j can equal p! In the pole product only (k+j') with j' ≤ n appear in
denominators — differences |j−j'| ≤ n < p, safe. The numerator factors may
carry p — harmless for integrality. Write this argument precisely.)

Assembly (W): reduce a mod p (Lemma C), apply Lemma A mod p (all three M-indices
are ≤ 4n+2 when p ≤ 2n; ranges: 3 ≥ 1, 2p+1 ≤ 4n+1), combine with Lemma B
summed over j ∈ {0..n} ⊂ ZMod p (distinct since n < p):
  w_n ≡ Σ_j Σ_i δ_{i,3} a_{i,j} = Σ_M c_M E_M(a) ≡ 0.
Same for w̃ with its own decay range.

Assembly (CB₁) = Prop 1: ord_p C(2n,n) = 1 not needed for the ≥1 statement on
p_n — just: p_n = w̃v − wṽ with v, ṽ p-integral (Lemma C) and w, w̃ ≡ 0 (W).

## Module plan (6 workers; owner-file-per-worker, no shared files)

1. `Cbcert/Defs.lean` — all definitions above; basic lemmas (finiteness,
   ã in terms of a, degree counts as ℕ facts).
2. `Cbcert/PartialFraction.lean` — existence/uniqueness of the decomposition
   for distinct linear poles with multiplicity 6 over ℚ (search Mathlib first:
   RatFunc partial fractions / `IsCoprime` decompositions; else prove by
   induction), and the Taylor-coefficient formula for a_{i,j}.
3. `Cbcert/Decay.lean` — Lemma A (LaurentSeries route).
4. `Cbcert/Certificate.lean` — Lemma B (start here: quickest win, zero deps
   beyond Mathlib; also proves the C(−i,r) integer identities).
5. `Cbcert/Integrality.lean` — Lemma C.
6. `Cbcert/Main.lean` — assemblies, final theorems `w_congruence`,
   `wtilde_congruence`, `pn_valuation`; plus `Cbcert/Numeric.lean` sanity
   `decide`-checks (n ≤ 6, p ∈ window) gating merges.

## Management protocol (from zeta5odd experience)

- Manager: Opus; workers: 5–6 Opus subagents, each owning exactly the files
  above; integration through the manager only. Commit early and often; /tmp is
  session-scoped; keep a PROGRESS.md state map so any crashed worker can be
  resumed by a successor from committed state.
- Toolchain: copy zeta5odd's lake/toolchain pinning; build must stay green on
  main line — workers develop against stubs (`sorry`-stubs allowed mid-flight,
  tracked in PROGRESS.md, zero at the end).
- Statement-first discipline: Manager freezes Defs.lean + theorem statements
  (reviewed against SPEC) before parallel work begins. Any statement change
  goes through the manager.
- Honesty: if a lemma resists, weaken honestly (e.g. prove (W) first, leave
  (CB₁) staged) rather than axiomatize. NO new axioms; target
  [propext, Classical.choice, Quot.sound] like zeta5odd.
- Pitfall notes: ord_∞ ranges for ã differ from a (4n+2 vs 4n+4); j = 0 node
  needs the M−i ≥ 0 convention; n/2 half-integer is fine in ℚ (p odd);
  p = 2n+1 is EXCLUDED from the theorem (only p ≤ 2n).
