import Cbcert.Main
import Cbcert.FiniteLaw
import Cbcert.Integrality

/-!
# T2 — the conditional assembly (Sol's master reduction)

This module formalizes Sol's master reduction of the `p ≥ 5` part of the corrected
Brown–Zudilin law as a **theorem with the open descent as an explicit hypothesis**.
The point of the wave (L6-staging): the full `p ≥ 5` law is now exactly **one
hypothesis away** — the descent `hD` — and everything else (terminal integrality,
digit-chain bookkeeping) is discharged from the PROVEN cbcert lemmas.

`P := BZP` (the normalized weight-5 ladder `P n = (−1)^{n+1}·p_n / C(2n,n)`,
`Cbcert/FiniteLaw.lean`).

## The open hypothesis `hD` (NEVER proven here)

    `hD : ∀ m p, p.Prime → 5 ≤ p → p ≤ m →
            padicValRat p (P (m / p)) − 5 ≤ padicValRat p (P m)`

i.e. `v_p(P m) ≥ v_p(P (⌊m/p⌋)) − 5` in the descent regime `p ≤ m` (so `⌊m/p⌋ ≥ 1`).

**Faithfulness** (why this is the right freeze):

* (a) *Faithful to (D) as verified.* This is exactly the statement checked in
  `worthiness/salvage_v7.py`: `v_p(P_n) ≥ v_p(P_{⌊n/p⌋}) − 5` for `p ≥ 5`,
  **332 descents, 0 violations**, overwhelmingly tight (the `d_n⁵` reserve pays
  exactly 5 orders per digit level). The guard `p ≤ m` reproduces the script's
  `⌊m/p⌋ ≥ 1` filter.
* (b) *Provable-in-principle by Sol's eventual argument.* It is the master
  reduction §S1 = the vector-Dwork descent (D); `PHASE2_SALVAGE_VERIFY.md` §V6d/V7
  identifies it as the single surviving obligation of the whole `p ≥ 5` law.
* (c) *Free of `padicValRat`-at-zero traps.* Mathlib sets `padicValRat p 0 = 0`.
  The conclusion `−5·⌊log_p n⌋ ≤ v_p(P n)` is trivially true where `P n = 0`
  (RHS `= 0`, LHS `≤ 0`). In the induction step, if `P (n/p) = 0` then
  `v_p(P (n/p)) = 0` and `hD` gives `v_p(P n) ≥ −5 ≥ −5·⌊log_p n⌋` (since
  `⌊log_p n⌋ ≥ 0`); if `P (n/p) ≠ 0` the induction hypothesis feeds through
  directly. So the `v_p(0) = 0` convention never produces an unsound step — no
  separate nonvanishing hypothesis is required. (On the verified range `P m ≠ 0`
  for every index `m ≥ 1`, so the zero branch is vacuous there anyway.)

## Conclusion

    `descent_law : hD → ∀ n ≥ 1, ∀ p prime ≥ 5, −5·⌊log_p n⌋ ≤ padicValRat p (P n)`,

the `p`-part of the corrected law at `p ≥ 5` (`⌊log_p n⌋ = Nat.log p n`).

## Proof (strong induction on `n` via the digit chain `n → n/p`)

* **Terminal `n < p`** (`Nat.log p n = 0`, so RHS `= 0`): `P n` is `p`-integral,
  from PROVEN cbcert lemmas —
  - `2n < p`: `p_n` is `p`-integral (`Main.pn_pInt`, `p > n`) and `p ∤ C(2n,n)`
    (`Nat.factorization_choose`, `log p (2n) = 0`); so `v_p(P n) = v_p(p_n) ≥ 0`.
  - `n < p ≤ 2n`: `v_p(p_n) ≥ 1` is the PROVEN band `Main.res_congruence_pn` /
    `Main.pn_valuation`, and `ord_p C(2n,n) = 1` (one-digit Kummer:
    `2n = 1·p + (2n−p)`, one carry — `Nat.factorization_choose` /
    `padicValNat_choose`); so `v_p(P n) ≥ 1 − 1 = 0`.
* **Step `p ≤ n`**: `a := n/p ≥ 1`, `⌊log_p n⌋ = ⌊log_p a⌋ + 1`
  (`Nat.log_div_base` + `Nat.log_pos`); apply the IH at `a < n` and `hD` at `m = n`.

House rules: no `sorry` at completion, no `native_decide`, no new axioms; the axiom
audit of `descent_law` will show `[propext, Classical.choice, Quot.sound]` and
**no `sorryAx`** — `hD` is a hypothesis, not an axiom. That is the point of the
staging.
-/

namespace Cbcert.Assembly

open Cbcert

/-- The normalized weight-5 ladder `P n = (−1)^{n+1}·p_n / C(2n,n)`. -/
abbrev P : ℕ → ℚ := Cbcert.FiniteLaw.BZP

/-- The open descent hypothesis (D), frozen. See the module docstring for the
faithfulness argument. This proposition is a **hypothesis** of `descent_law`; it is
NOT proven in this project (it is Sol's master reduction / the vector-Dwork
descent). Verified numerically: `worthiness/salvage_v7.py`, 332 descents,
0 violations. -/
def DescentHyp : Prop :=
  ∀ (m p : ℕ), p.Prime → 5 ≤ p → p ≤ m →
    padicValRat p (P (m / p)) - 5 ≤ padicValRat p (P m)

/-- **Terminal integrality (PROVEN piece).** For `n ≥ 1`, prime `p ≥ 5` with
`n < p`, the value `P n` is `p`-integral. Combines `Main.pn_pInt` (for `p > 2n`)
and the band `Main.res_congruence_pn` + one-digit Kummer `ord_p C(2n,n) = 1`
(for `n < p ≤ 2n`). Does NOT use `hD`. -/
theorem P_pIntegral_terminal (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime) (h5 : 5 ≤ p)
    (hlt : n < p) : 0 ≤ padicValRat p (P n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  -- Unfold `P n = (-1)^{n+1} · pn n / C(2n,n)`.
  show (0 : ℤ) ≤ padicValRat p ((-1) ^ (n + 1) * pn n / (Nat.choose (2 * n) n : ℚ))
  -- `C(2n,n) > 0`, hence nonzero.
  have hCpos : 0 < Nat.choose (2 * n) n := Nat.choose_pos (by omega)
  have hC0 : ((Nat.choose (2 * n) n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hCpos.ne'
  have hCeq : Nat.choose (2 * n) n = Nat.choose (n + n) n := by rw [two_mul]
  -- Zero case: `pn n = 0 ⇒ P n = 0`.
  by_cases hpn : pn n = 0
  · rw [hpn]; simp
  -- The sign factor is `p`-adically trivial.
  have hsign : ((-1 : ℚ)) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hnum : ((-1 : ℚ)) ^ (n + 1) * pn n ≠ 0 := mul_ne_zero hsign hpn
  have hneg1 : padicValRat p (-1 : ℚ) = 0 := by
    rw [show (-1 : ℚ) = -(1 : ℚ) from by ring, padicValRat.neg, padicValRat.one]
  have hs0 : padicValRat p (((-1 : ℚ)) ^ (n + 1)) = 0 := by
    rw [padicValRat.pow, hneg1, mul_zero]
  rw [padicValRat.div hnum hC0, padicValRat.mul hsign hpn, hs0, zero_add]
  -- Goal: `0 ≤ v_p(pn n) − v_p(C(2n,n))`.
  by_cases hB : p ≤ 2 * n
  · -- Band `n < p ≤ 2n`: `v_p(pn n) ≥ 1` and `v_p(C(2n,n)) = 1` (one-digit Kummer).
    have hlt2 : n + n < p ^ 2 := by
      have h2 : 2 ≤ p := hp.two_le
      calc n + n < 2 * p := by omega
        _ ≤ p * p := by nlinarith
        _ = p ^ 2 := (pow_two p).symm
    have hvC : padicValRat p ((Nat.choose (2 * n) n : ℚ)) ≤ 1 := by
      rw [← padicValRat_of_nat, hCeq,
        padicValNat_choose' (n := n) (k := n) (b := 2)
          (Nat.log_lt_of_lt_pow' (by norm_num) hlt2)]
      exact_mod_cast le_trans (Finset.card_filter_le _ _) (by simp)
    have hpn1 : (1 : ℤ) ≤ padicValRat p (pn n) := by
      rcases Cbcert.Main.pn_valuation n hn p hp hlt hB h5 with h | h
      · exact absurd h hpn
      · exact h
    linarith [hvC, hpn1]
  · -- Range `2n < p`: `v_p(pn n) ≥ 0` and `p ∤ C(2n,n)`.
    have hvC : padicValRat p ((Nat.choose (2 * n) n : ℚ)) = 0 := by
      rw [← padicValRat_of_nat, hCeq,
        padicValNat_choose' (n := n) (k := n) (b := 1)
          (Nat.log_lt_of_lt_pow' (by norm_num) (by rw [pow_one]; omega))]
      simp
    rw [hvC, sub_zero]
    exact Cbcert.Main.pn_pInt n hp hlt hp2

/-- **T2 — conditional assembly.** Under the open descent `hD`, the `p ≥ 5` part of
the corrected Brown–Zudilin law holds for every `n ≥ 1`:
`v_p(P n) ≥ −5·⌊log_p n⌋`. -/
theorem descent_law (hD : DescentHyp) :
    ∀ (n : ℕ), 1 ≤ n → ∀ (p : ℕ), p.Prime → 5 ≤ p →
      (-5 : ℤ) * (Nat.log p n : ℤ) ≤ padicValRat p (P n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn p hp h5
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases hnp : n < p
    · -- Terminal `n < p`: `Nat.log p n = 0`, RHS `= 0`.
      have hlog : Nat.log p n = 0 := Nat.log_eq_zero_iff.mpr (Or.inl hnp)
      rw [hlog, Nat.cast_zero, mul_zero]
      exact P_pIntegral_terminal n p hn hp h5 hnp
    · -- Descent `p ≤ n`: apply the IH at `a = n/p` and `hD` at `n`.
      push_neg at hnp
      have hpn1 : 1 < p := hp.one_lt
      have ha1 : 1 ≤ n / p := Nat.div_pos hnp (by omega)
      have han : n / p < n := Nat.div_lt_self (by omega) hpn1
      have hlog : Nat.log p n = Nat.log p (n / p) + 1 := by
        rw [Nat.log_div_base]
        have : 1 ≤ Nat.log p n := Nat.log_pos hpn1 hnp
        omega
      have hIH := ih (n / p) han ha1 p hp h5
      have hDn := hD n p hp h5 hnp
      rw [hlog]; push_cast
      linarith [hIH, hDn]

end Cbcert.Assembly
