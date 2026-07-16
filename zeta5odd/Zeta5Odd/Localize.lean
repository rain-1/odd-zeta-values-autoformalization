/-
Piece 1 of Lemma 4: εn-localization of the sum r n.
Owner file — only `sum_localizes` (and its private helpers) lives here.
-/
import Zeta5Odd.Basic

open Filter Finset
open scoped Nat Topology

namespace Zeta5Odd

/-! ### Generic geometric comparison helpers (pure, sequence-level) -/

/-- If the successive ratio of a sequence stays `≤ ρ` on `[m, k)`, then
`u k ≤ ρ^(k-m) * u m`. -/
private lemma pow_ratio_upper {u : ℕ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    {m k : ℕ} (hmk : m ≤ k)
    (hstep : ∀ j, m ≤ j → j < k → u (j + 1) ≤ ρ * u j) :
    u k ≤ ρ ^ (k - m) * u m := by
  induction k with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · have hmk' : m ≤ k := Nat.lt_succ_iff.mp hlt
      have hstep' : ∀ j, m ≤ j → j < k → u (j + 1) ≤ ρ * u j := fun j hj hjk =>
        hstep j hj (hjk.trans (Nat.lt_succ_self k))
      have hlast : u (k + 1) ≤ ρ * u k := hstep k hmk' (Nat.lt_succ_self k)
      calc u (k + 1) ≤ ρ * u k := hlast
        _ ≤ ρ * (ρ ^ (k - m) * u m) := mul_le_mul_of_nonneg_left (ih hmk' hstep') hρ
        _ = ρ ^ (k + 1 - m) * u m := by
              rw [← mul_assoc, ← pow_succ']; congr 2; omega
    · have hmeq : m = k + 1 := le_antisymm hmk hge
      subst hmeq; simp

/-- If the successive ratio of a sequence stays `≥ ρ` on `[m, k)` (all terms
nonneg), then `ρ^(k-m) * u m ≤ u k`. -/
private lemma pow_ratio_lower {u : ℕ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hu : ∀ j, 0 ≤ u j) {m k : ℕ} (hmk : m ≤ k)
    (hstep : ∀ j, m ≤ j → j < k → ρ * u j ≤ u (j + 1)) :
    ρ ^ (k - m) * u m ≤ u k := by
  induction k with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · have hmk' : m ≤ k := Nat.lt_succ_iff.mp hlt
      have hstep' : ∀ j, m ≤ j → j < k → ρ * u j ≤ u (j + 1) := fun j hj hjk =>
        hstep j hj (hjk.trans (Nat.lt_succ_self k))
      have hlast : ρ * u k ≤ u (k + 1) := hstep k hmk' (Nat.lt_succ_self k)
      calc ρ ^ (k + 1 - m) * u m
          = ρ * (ρ ^ (k - m) * u m) := by
              rw [← mul_assoc, ← pow_succ']; congr 2; omega
        _ ≤ ρ * u k := mul_le_mul_of_nonneg_left (ih hmk' hstep') hρ
        _ ≤ u (k + 1) := hlast
    · have hmeq : m = k + 1 := le_antisymm hmk hge
      subst hmeq; simp

/-- Telescoping (variable-ratio) comparison: if `u (j+1) ≤ (w (j+1)/w j) * u j`
on `[m, k)` with `w > 0`, then `u k ≤ (w k / w m) * u m`. -/
private lemma prod_ratio_upper {u w : ℕ → ℝ} (hw : ∀ j, 0 < w j)
    {m k : ℕ} (hmk : m ≤ k)
    (hstep : ∀ j, m ≤ j → j < k → u (j + 1) ≤ (w (j + 1) / w j) * u j) :
    u k ≤ (w k / w m) * u m := by
  induction k with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.mp hmk
    rw [div_self (hw 0).ne', one_mul]
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · have hmk' : m ≤ k := Nat.lt_succ_iff.mp hlt
      have hstep' : ∀ j, m ≤ j → j < k → u (j + 1) ≤ (w (j + 1) / w j) * u j := fun j hj hjk =>
        hstep j hj (hjk.trans (Nat.lt_succ_self k))
      have hlast : u (k + 1) ≤ (w (k + 1) / w k) * u k := hstep k hmk' (Nat.lt_succ_self k)
      have hkm := (hw m).ne'
      have hkk := (hw k).ne'
      calc u (k + 1) ≤ (w (k + 1) / w k) * u k := hlast
        _ ≤ (w (k + 1) / w k) * ((w k / w m) * u m) :=
              mul_le_mul_of_nonneg_left (ih hmk' hstep')
                (div_nonneg (hw _).le (hw _).le)
        _ = (w (k + 1) / w m) * u m := by
              field_simp
    · have hmeq : m = k + 1 := le_antisymm hmk hge
      subst hmeq
      rw [div_self (hw (k + 1)).ne', one_mul]

/-! ### Polynomial-times-geometric tendsto helpers -/

/-- `(a m² + b) · λ^m → 0` for `0 ≤ λ < 1`. -/
private lemma tendsto_quad_geom {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (a b : ℝ) :
    Tendsto (fun m : ℕ => (a * (m : ℝ) ^ 2 + b) * lam ^ m) atTop (𝓝 0) := by
  have h2 : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * lam ^ m) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one 2 hlam0 hlam1
  have h0 : Tendsto (fun m : ℕ => lam ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1
  have key := (h2.const_mul a).add (h0.const_mul b)
  simp only [mul_zero, add_zero] at key
  refine key.congr (fun m => ?_)
  ring

/-- If `0 ≤ Q n ≤ a (d n)² + b` and `d n → ∞`, then `Q n · λ^(d n) → 0`. -/
private lemma tendsto_Q_geom {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    {Q : ℕ → ℝ} {d : ℕ → ℕ} (a b : ℝ)
    (hQpos : ∀ n, 0 ≤ Q n) (hQ : ∀ n, Q n ≤ a * (d n : ℝ) ^ 2 + b)
    (hd : Tendsto d atTop atTop) :
    Tendsto (fun n => Q n * lam ^ (d n)) atTop (𝓝 0) := by
  have hcomp : Tendsto (fun n => (a * (d n : ℝ) ^ 2 + b) * lam ^ (d n)) atTop (𝓝 0) :=
    (tendsto_quad_geom hlam0 hlam1 a b).comp hd
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hcomp
  · exact mul_nonneg (hQpos n) (pow_nonneg hlam0 _)
  · exact mul_le_mul_of_nonneg_right (hQ n) (pow_nonneg hlam0 _)

/-- Split the two-sided tail into a finite lower part and an upper subtype tail. -/
private lemma tail_decomp {u : ℕ → ℝ} (hsum : Summable u)
    {a b : ℝ} (hab : a ≤ b) :
    (∑' k : {k : ℕ // (k : ℝ) < a ∨ b < (k : ℝ)}, u k)
      = (∑ k ∈ Finset.range ⌈a⌉₊, u k) + (∑' k : {k : ℕ // b < (k : ℝ)}, u k) := by
  classical
  have hdisj : Disjoint {k : ℕ | (k : ℝ) < a} {k : ℕ | b < (k : ℝ)} := by
    rw [Set.disjoint_left]
    intro k hk hk'
    simp only [Set.mem_setOf_eq] at hk hk'
    linarith
  have key : (∑' k : {k : ℕ // (k : ℝ) < a ∨ b < (k : ℝ)}, u k)
      = (∑' k : {k : ℕ | (k : ℝ) < a}, u k) + (∑' k : {k : ℕ | b < (k : ℝ)}, u k) := by
    have h1 := tsum_subtype ({k : ℕ | (k : ℝ) < a} ∪ {k : ℕ | b < (k : ℝ)}) u
    rw [Set.indicator_union_of_disjoint hdisj,
        Summable.tsum_add (hsum.indicator _) (hsum.indicator _),
        ← _root_.tsum_subtype, ← _root_.tsum_subtype] at h1
    exact h1
  rw [key]
  congr 1
  rw [_root_.tsum_subtype]
  have hz : ∀ k ∉ Finset.range ⌈a⌉₊, {k : ℕ | (k : ℝ) < a}.indicator u k = 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hnm : k ∉ {k : ℕ | (k : ℝ) < a} := by
      rw [Set.mem_setOf_eq, ← Nat.lt_ceil]; exact hk
    exact Set.indicator_of_notMem hnm _
  rw [tsum_eq_sum hz]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range, Nat.lt_ceil] at hk
  exact Set.indicator_of_mem (show k ∈ {k : ℕ | (k : ℝ) < a} from hk) u

/-- Lower (finite) tail bound: geometric growth `≥ 1+δ` up to index `Nlo + D`
makes the finite head `∑_{k<Nlo} u k` at most `Nlo · (1+δ)^{-(D+1)} · u_{Nlo+D}`. -/
private lemma lower_tail_le {u : ℕ → ℝ} (hpos : ∀ k, 0 < u k)
    {δ A : ℝ} (hδ : 0 < δ)
    (hstep : ∀ j : ℕ, (j : ℝ) ≤ A → (1 + δ) * u j ≤ u (j + 1))
    (Nlo D : ℕ) (hAbd : ((Nlo + D : ℕ) : ℝ) - 1 ≤ A) :
    (∑ k ∈ Finset.range Nlo, u k)
      ≤ (Nlo : ℝ) * ((1 + δ)⁻¹) ^ (D + 1) * u (Nlo + D) := by
  set mlo := Nlo + D with hmlo
  set β : ℝ := (1 + δ)⁻¹ with hβ
  have hδ1 : (0 : ℝ) < 1 + δ := by linarith
  have hβpos : 0 < β := by rw [hβ]; positivity
  have hβ1 : β ≤ 1 := by rw [hβ]; exact (inv_le_one₀ hδ1).mpr (by linarith)
  have hpt : ∀ k, k < Nlo → u k ≤ β ^ (D + 1) * u mlo := by
    intro k hk
    have hkmlo : k ≤ mlo := by omega
    have hstep' : ∀ j, k ≤ j → j < mlo → (1 + δ) * u j ≤ u (j + 1) := by
      intro j _ hjm
      apply hstep
      have hjc : (j : ℝ) ≤ (mlo : ℝ) - 1 := by
        have : j + 1 ≤ mlo := hjm
        have h2 := (Nat.cast_le (α := ℝ)).mpr this
        push_cast at h2; linarith
      have : (mlo : ℝ) - 1 ≤ A := by push_cast [hmlo] at hAbd ⊢; linarith
      linarith
    have hpr := pow_ratio_lower (le_of_lt hδ1) (fun j => (hpos j).le) hkmlo hstep'
    have huk : u k ≤ u mlo / (1 + δ) ^ (mlo - k) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [hpr]
    calc u k ≤ u mlo / (1 + δ) ^ (mlo - k) := huk
      _ = u mlo * ((1 + δ) ^ (mlo - k))⁻¹ := by rw [div_eq_mul_inv]
      _ = u mlo * β ^ (mlo - k) := by rw [hβ, inv_pow]
      _ ≤ u mlo * β ^ (D + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hβpos.le hβ1 (by omega)) (hpos mlo).le
      _ = β ^ (D + 1) * u mlo := by ring
  calc (∑ k ∈ Finset.range Nlo, u k)
      ≤ ∑ _k ∈ Finset.range Nlo, β ^ (D + 1) * u mlo :=
        Finset.sum_le_sum (fun k hk => hpt k (Finset.mem_range.mp hk))
    _ = (Nlo : ℝ) * β ^ (D + 1) * u mlo := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- Upper (infinite) tail bound: the near-window `1-δ` margin plus the
telescoping square-ratio majorant bound `∑_{k>C} u k` by
`(K+σ)² · (∑ 1/(k+1)²) · (1-δ)^E · u_{mhi}`, where `K` is the first index
above `C`, `mhi + E = K`. -/
private lemma upper_tail_le {u : ℕ → ℝ} (hpos : ∀ k, 0 < u k) (hsum : Summable u)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {B C σ : ℝ} (hσ1 : 1 ≤ σ)
    (hmid : ∀ j : ℕ, B ≤ (j : ℝ) → (j : ℝ) ≤ C → u (j + 1) ≤ (1 - δ) * u j)
    (htel : ∀ j : ℕ, B ≤ (j : ℝ) →
      u (j + 1) ≤ (((j : ℝ) + σ) / ((j : ℝ) + σ + 1)) ^ 2 * u j)
    (K mhi E : ℕ) (hKmhi : K = mhi + E)
    (hmhiB : B ≤ (mhi : ℝ)) (hK1C : ((K - 1 : ℕ) : ℝ) ≤ C)
    (hKrel : ∀ k : ℕ, C < (k : ℝ) ↔ K ≤ k) :
    (∑' k : {k : ℕ // C < (k : ℝ)}, u k)
      ≤ ((K : ℝ) + σ) ^ 2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2) * ((1 - δ) ^ E * u mhi) := by
  have hσ0 : (0 : ℝ) < σ := lt_of_lt_of_le one_pos hσ1
  set w : ℕ → ℝ := fun j => 1 / ((j : ℝ) + σ) ^ 2 with hw
  have hwpos : ∀ j, 0 < w j := fun j => by rw [hw]; positivity
  -- telescoping majorant on `[K, ∞)`
  have htelstep : ∀ j, K ≤ j → u (j + 1) ≤ (w (j + 1) / w j) * u j := by
    intro j hj
    have hjB : B ≤ (j : ℝ) := by
      have : (mhi : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : mhi ≤ j)
      linarith
    have hstep := htel j hjB
    have e1 : ((j : ℝ) + σ) ≠ 0 := by positivity
    have e2 : ((j : ℝ) + σ + 1) ≠ 0 := by positivity
    have e3 : ((j : ℝ) + 1 + σ) ≠ 0 := by positivity
    have hww : (((j : ℝ) + σ) / ((j : ℝ) + σ + 1)) ^ 2 = w (j + 1) / w j := by
      simp only [hw]; push_cast; field_simp; ring
    rwa [hww] at hstep
  have hptmaj : ∀ k : ℕ, K ≤ k → u k ≤ (w k / w K) * u K := fun k hk =>
    prod_ratio_upper hwpos hk (fun j hj _ => htelstep j hj)
  -- middle margin gives `u K ≤ (1-δ)^E u mhi`
  have hUK : u K ≤ (1 - δ) ^ E * u mhi := by
    have hmk : mhi ≤ K := by omega
    have hstep : ∀ j, mhi ≤ j → j < K → u (j + 1) ≤ (1 - δ) * u j := by
      intro j hj hjK
      apply hmid
      · have : (mhi : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        linarith
      · have hle : j ≤ K - 1 := by omega
        have : (j : ℝ) ≤ ((K - 1 : ℕ) : ℝ) := by exact_mod_cast hle
        linarith
    have hpr := pow_ratio_upper (by linarith : (0 : ℝ) ≤ 1 - δ) hmk hstep
    have hEeq : K - mhi = E := by omega
    rwa [hEeq] at hpr
  -- summability of the base and the majorant
  have hS2sum : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    refine ((summable_nat_add_iff 1).mpr h0).congr (fun k => ?_)
    push_cast; ring
  have hwle : ∀ k : ℕ, w k ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
    intro k; rw [hw]
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hwsum : Summable w := hS2sum.of_nonneg_of_le (fun k => (hwpos k).le) hwle
  set P : ℝ := ((K : ℝ) + σ) ^ 2 * u K with hP
  have hwKne : ((K : ℝ) + σ) ^ 2 ≠ 0 := by positivity
  have hmajeq : ∀ k : ℕ, (w k / w K) * u K = P * w k := by
    intro k
    simp only [hw, hP]; field_simp
  have hsummaj : Summable (fun k : ℕ => P * w k) := hwsum.mul_left P
  -- assemble the tsum bound
  have hsubU : Summable (fun x : {k : ℕ // C < (k : ℝ)} => u ↑x) :=
    hsum.subtype (fun k => C < (k : ℝ))
  have hsubM : Summable (fun x : {k : ℕ // C < (k : ℝ)} => P * w ↑x) :=
    hsummaj.subtype (fun k => C < (k : ℝ))
  have hpwpos : 0 ≤ P := by rw [hP]; exact mul_nonneg (by positivity) (hpos K).le
  calc (∑' k : {k : ℕ // C < (k : ℝ)}, u k)
      ≤ ∑' k : {k : ℕ // C < (k : ℝ)}, P * w ↑k := by
        refine hsubU.tsum_le_tsum (fun x => ?_) hsubM
        have hKx : K ≤ (x : ℕ) := (hKrel _).mp x.2
        rw [← hmajeq]
        exact hptmaj _ hKx
    _ ≤ ∑' k : ℕ, P * w k :=
        Summable.tsum_subtype_le (fun k => P * w k) {k : ℕ | C < (k : ℝ)}
          (fun k => by positivity) hsummaj
    _ = P * ∑' k : ℕ, w k := by rw [tsum_mul_left]
    _ ≤ P * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left (hwsum.tsum_le_tsum hwle hS2sum) hpwpos
    _ ≤ ((K : ℝ) + σ) ^ 2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2) * ((1 - δ) ^ E * u mhi) := by
        have hbase : 0 ≤ ((K : ℝ) + σ) ^ 2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2) :=
          mul_nonneg (by positivity) (tsum_nonneg (fun k => by positivity))
        calc P * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2
            = (((K : ℝ) + σ) ^ 2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2)) * u K := by rw [hP]; ring
          _ ≤ (((K : ℝ) + σ) ^ 2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2)) * ((1 - δ) ^ E * u mhi) :=
                mul_le_mul_of_nonneg_left hUK hbase
          _ = ((K : ℝ) + σ) ^ 2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2) * ((1 - δ) ^ E * u mhi) := by
                ring

/-! ### Generic εn-localization

An abstract positive summable family `u n` whose successive term ratio
* is `≥ 1 + δlo` below `(x₀ - ε/2)·n` (geometric growth up to the peak),
* is `≤ 1 - δhi` on the near-upper window `[(x₀+ε/2)·n, (x₀+ε)·n]`,
* obeys the telescoping square-ratio majorant `((j+σ)/(j+σ+1))²` above
  `(x₀+ε/2)·n` (polynomial-with-huge-exponent decay controlling the far tail),
has negligible tail outside the window `[(x₀-ε)n, (x₀+ε)n]`. -/
private lemma localize_general
    (u : ℕ → ℕ → ℝ) (S : ℕ → ℝ) (x₀ ε : ℝ) (hx₀ : 0 < x₀) (hε : 0 < ε)
    (hpos : ∀ n k, 0 < u n k) (hsum : ∀ n, Summable (u n))
    (hS : ∀ n, S n = ∑' k, u n k)
    (shift : ℕ → ℝ) (hshift1 : ∀ n, 1 ≤ shift n) (hshiftbd : ∀ n, shift n ≤ 2 * (n : ℝ) + 2)
    (δlo : ℝ) (hδlo : 0 < δlo)
    (hlower : ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
        (j : ℝ) ≤ (x₀ - ε / 2) * n → (1 + δlo) * u n j ≤ u n (j + 1))
    (δhi : ℝ) (hδhi : 0 < δhi) (hδhi1 : δhi < 1)
    (hupperMid : ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
        (x₀ + ε / 2) * n ≤ (j : ℝ) → (j : ℝ) ≤ (x₀ + ε) * n → u n (j + 1) ≤ (1 - δhi) * u n j)
    (hupperTel : ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
        (x₀ + ε / 2) * n ≤ (j : ℝ) →
          u n (j + 1) ≤ (((j : ℝ) + shift n) / ((j : ℝ) + shift n + 1)) ^ 2 * u n j) :
    Tendsto (fun n : ℕ =>
        (∑' k : {k : ℕ // (k : ℝ) < (x₀ - ε) * n ∨ (x₀ + ε) * n < (k : ℝ)}, u n k) / S n)
      atTop (𝓝 0) := by
  sorry

/-! ### Analytic cores for `c` (term ratio ≈ f(k/n)²) -/

/-- Lower geometric margin for `c`: below `(x₀ - ε/2)·n` the term ratio exceeds
`1 + δ`.  (From `c_ratio` compared with `f(k/n)² > 1` on `(0, x₀)`.) -/
private lemma c_lower_core (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      (j : ℝ) ≤ (x₀ - ε / 2) * n → (1 + δ) * c q n j ≤ c q n (j + 1) := by
  sorry

/-- Upper margins for `c`: a `1 - δ` middle margin on `[(x₀+ε/2)n, (x₀+ε)n]`
and the telescoping square-ratio majorant above `(x₀+ε/2)n`. -/
private lemma c_upper_core (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      (∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
        (x₀ + ε / 2) * n ≤ (j : ℝ) → (j : ℝ) ≤ (x₀ + ε) * n →
          c q n (j + 1) ≤ (1 - δ) * c q n j) ∧
      (∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
        (x₀ + ε / 2) * n ≤ (j : ℝ) →
          c q n (j + 1) ≤
            (((j : ℝ) + (2 * n + 2)) / ((j : ℝ) + (2 * n + 2) + 1)) ^ 2 * c q n j) := by
  sorry

/-! ### Analytic cores for `chat` -/

private lemma chat_lower_core (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      (j : ℝ) ≤ (x₀ - ε / 2) * n → (1 + δ) * chat q n j ≤ chat q n (j + 1) := by
  sorry

private lemma chat_upper_core (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      (∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
        (x₀ + ε / 2) * n ≤ (j : ℝ) → (j : ℝ) ≤ (x₀ + ε) * n →
          chat q n (j + 1) ≤ (1 - δ) * chat q n j) ∧
      (∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
        (x₀ + ε / 2) * n ≤ (j : ℝ) →
          chat q n (j + 1) ≤
            (((j : ℝ) + (2 * n + 2)) / ((j : ℝ) + (2 * n + 2) + 1)) ^ 2 * chat q n j) := by
  sorry

/-! ### Main theorems -/

/-- Piece 1 (εn-localization): for every ε > 0, the tail of `r n` outside
the window `|k - x₀ n| ≤ εn` is exponentially negligible relative to the
whole sum.  This replaces de Bruijn's γ√n localization. -/
theorem sum_localizes (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
        (∑' k : {k : ℕ // (k : ℝ) < (x₀ - ε) * n ∨ (x₀ + ε) * n < (k : ℝ)},
          c q n k) / r q n)
      atTop (𝓝 0) := by
  obtain ⟨δlo, hδlo, hlower⟩ := c_lower_core q hq hx₀ hfx₀ hε
  obtain ⟨δhi, hδhi, hδhi1, hmid, htel⟩ := c_upper_core q hq hx₀ hfx₀ hε
  exact localize_general (c q) (r q) x₀ ε hx₀ hε (fun n k => c_pos q n k)
    (fun n => summable_c q n hq) (fun _ => rfl) (fun n => 2 * (n : ℝ) + 2)
    (fun n => by have h : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith) (fun n => le_refl _)
    δlo hδlo hlower δhi hδhi hδhi1 hmid htel

/-- Same localization for the half-shifted series `r̂` (needed by
`tendsto_ratio`): the machinery is identical — the term ratio
`chat (k+1) / chat k` is the same exact rational function up to
half-integer shifts. -/
theorem sum_localizes_chat (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
        (∑' k : {k : ℕ // (k : ℝ) < (x₀ - ε) * n ∨ (x₀ + ε) * n < (k : ℝ)},
          chat q n k) / rhat q n)
      atTop (𝓝 0) := by
  obtain ⟨δlo, hδlo, hlower⟩ := chat_lower_core q hq hx₀ hfx₀ hε
  obtain ⟨δhi, hδhi, hδhi1, hmid, htel⟩ := chat_upper_core q hq hx₀ hfx₀ hε
  exact localize_general (chat q) (rhat q) x₀ ε hx₀ hε (fun n k => chat_pos q n k)
    (fun n => summable_chat q n hq) (fun _ => rfl) (fun n => 2 * (n : ℝ) + 2)
    (fun n => by have h : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith) (fun n => le_refl _)
    δlo hδlo hlower δhi hδhi hδhi1 hmid htel

end Zeta5Odd
