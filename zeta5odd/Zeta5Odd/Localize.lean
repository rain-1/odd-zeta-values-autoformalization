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

/-- If `0 ≤ Q n ≤ a n² + b` (`a ≥ 0`) then `Q n · λ^(⌊c n⌋ + 1) → 0` for
`0 < c`, `0 ≤ λ < 1`.  (Geometric decay in `⌊c n⌋` beats the polynomial in `n`.) -/
private lemma tendsto_npoly_floor_geom {c lam : ℝ} (hc : 0 < c)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) {Q : ℕ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hQ0 : ∀ n, 0 ≤ Q n) (hQ : ∀ n, Q n ≤ a * (n : ℝ) ^ 2 + b) :
    Tendsto (fun n => Q n * lam ^ (⌊c * (n : ℝ)⌋₊ + 1)) atTop (𝓝 0) := by
  have hdtend : Tendsto (fun n : ℕ => ⌊c * (n : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp
      (Filter.Tendsto.const_mul_atTop hc (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have key : Tendsto (fun n => (Q n * lam) * lam ^ (⌊c * (n : ℝ)⌋₊)) atTop (𝓝 0) := by
    refine tendsto_Q_geom hlam0 hlam1 (lam * (2 * a / c ^ 2)) (lam * (2 * a / c ^ 2 + b))
      (fun n => mul_nonneg (hQ0 n) hlam0) (fun n => ?_) hdtend
    have hcn : c * (n : ℝ) ≤ ((⌊c * (n : ℝ)⌋₊ : ℝ)) + 1 := (Nat.lt_floor_add_one _).le
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hd0 : (0 : ℝ) ≤ (⌊c * (n : ℝ)⌋₊ : ℝ) := Nat.cast_nonneg _
    have hnsq : (n : ℝ) ^ 2 * c ^ 2 ≤ 2 * (⌊c * (n : ℝ)⌋₊ : ℝ) ^ 2 + 2 := by
      nlinarith [hcn, hn0, hd0, mul_nonneg hc.le hn0, sq_nonneg ((⌊c * (n : ℝ)⌋₊ : ℝ) - 1)]
    have hgoal : a * (n : ℝ) ^ 2 ≤ 2 * a * ((⌊c * (n : ℝ)⌋₊ : ℝ) ^ 2 + 1) / c ^ 2 := by
      rw [le_div_iff₀ hc2]; nlinarith [hnsq, ha]
    have hexp : 2 * a * ((⌊c * (n : ℝ)⌋₊ : ℝ) ^ 2 + 1) / c ^ 2
        = (2 * a / c ^ 2) * (⌊c * (n : ℝ)⌋₊ : ℝ) ^ 2 + 2 * a / c ^ 2 := by
      field_simp
    calc Q n * lam ≤ (a * (n : ℝ) ^ 2 + b) * lam :=
          mul_le_mul_of_nonneg_right (hQ n) hlam0
      _ ≤ ((2 * a / c ^ 2) * (⌊c * (n : ℝ)⌋₊ : ℝ) ^ 2 + (2 * a / c ^ 2 + b)) * lam := by
            apply mul_le_mul_of_nonneg_right _ hlam0
            linarith [hgoal, hexp.le]
      _ = lam * (2 * a / c ^ 2) * (⌊c * (n : ℝ)⌋₊ : ℝ) ^ 2 + lam * (2 * a / c ^ 2 + b) := by ring
  refine key.congr (fun n => ?_)
  rw [pow_succ]; ring

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
  have hδlo1 : (1 : ℝ) < 1 + δlo := by linarith
  set βlo : ℝ := (1 + δlo)⁻¹ with hβlo
  have hβlo0 : 0 ≤ βlo := by rw [hβlo]; positivity
  have hβlo1 : βlo < 1 := by rw [hβlo]; exact (inv_lt_one₀ (by linarith)).mpr hδlo1
  set S₂ : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 with hS2
  have hS2nn : 0 ≤ S₂ := by rw [hS2]; exact tsum_nonneg (fun k => by positivity)
  have hxε : (0 : ℝ) ≤ x₀ + ε := by linarith
  have hnn2 : ∀ n : ℕ, (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    intro n; rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      nlinarith
  have hceilbd : ∀ n : ℕ, (⌈(x₀ - ε) * (n : ℝ)⌉₊ : ℝ) ≤ (x₀ + ε) * (n : ℝ) + 1 := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rcases le_or_gt ((x₀ - ε) * (n : ℝ)) 0 with h | h
    · rw [Nat.ceil_eq_zero.mpr h]; push_cast; nlinarith
    · have := (Nat.ceil_lt_add_one h.le).le; nlinarith
  have hfloorbd : ∀ n : ℕ, ((⌊(x₀ + ε) * (n : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ (x₀ + ε) * (n : ℝ) + 1 := by
    intro n
    have hn : (0 : ℝ) ≤ (x₀ + ε) * (n : ℝ) := mul_nonneg hxε (Nat.cast_nonneg n)
    have := Nat.floor_le hn
    push_cast; linarith
  set M : ℝ := x₀ + ε + 2 with hM
  have hMpos : 0 < M := by rw [hM]; linarith
  -- the two vanishing envelope sequences
  set glo : ℕ → ℝ := fun n =>
    (⌈(x₀ - ε) * (n : ℝ)⌉₊ : ℝ) * βlo ^ (⌊ε / 4 * (n : ℝ)⌋₊ + 1) with hglo
  set ghi : ℕ → ℝ := fun n =>
    (((⌊(x₀ + ε) * (n : ℝ)⌋₊ + 1 : ℕ) : ℝ) + shift n) ^ 2 * S₂ *
      (1 - δhi) ^ (⌊ε / 4 * (n : ℝ)⌋₊ + 1) with hghi
  -- Tendsto glo → 0
  have hgt : Tendsto glo atTop (𝓝 0) := by
    rw [hglo]
    refine tendsto_npoly_floor_geom (Q := fun n => (⌈(x₀ - ε) * (n : ℝ)⌉₊ : ℝ))
      (c := ε / 4) (lam := βlo) (a := x₀ + ε) (b := 1)
      (by linarith) hβlo0 hβlo1 hxε (fun n => by positivity) (fun n => ?_)
    have h1 := hceilbd n
    have h2 : (x₀ + ε) * (n : ℝ) ≤ (x₀ + ε) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (hnn2 n) hxε
    linarith
  -- Tendsto ghi → 0
  have hht : Tendsto ghi atTop (𝓝 0) := by
    rw [hghi]
    refine tendsto_npoly_floor_geom
      (Q := fun n => (((⌊(x₀ + ε) * (n : ℝ)⌋₊ + 1 : ℕ) : ℝ) + shift n) ^ 2 * S₂)
      (c := ε / 4) (lam := 1 - δhi) (a := (M ^ 2 + 6 * M) * S₂) (b := 9 * S₂)
      (by linarith) (by linarith) (by linarith)
      (by positivity) (fun n => by positivity) (fun n => ?_)
    have hks : (((⌊(x₀ + ε) * (n : ℝ)⌋₊ + 1 : ℕ) : ℝ) + shift n) ≤ M * (n : ℝ) + 3 := by
      have hf := hfloorbd n; have hs := hshiftbd n; rw [hM]; nlinarith
    have hks0 : 0 ≤ (((⌊(x₀ + ε) * (n : ℝ)⌋₊ + 1 : ℕ) : ℝ) + shift n) := by
      have := hshift1 n; positivity
    have hsq : (((⌊(x₀ + ε) * (n : ℝ)⌋₊ + 1 : ℕ) : ℝ) + shift n) ^ 2 ≤ (M * (n : ℝ) + 3) ^ 2 :=
      pow_le_pow_left₀ hks0 hks 2
    have hlin : M * (n : ℝ) ≤ M * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (hnn2 n) hMpos.le
    calc (((⌊(x₀ + ε) * (n : ℝ)⌋₊ + 1 : ℕ) : ℝ) + shift n) ^ 2 * S₂
        ≤ (M * (n : ℝ) + 3) ^ 2 * S₂ := mul_le_mul_of_nonneg_right hsq hS2nn
      _ ≤ (M ^ 2 + 6 * M) * S₂ * (n : ℝ) ^ 2 + 9 * S₂ := by nlinarith [hlin, hS2nn, hMpos]
  have htendsto : Tendsto (fun n => glo n + ghi n) atTop (𝓝 0) := by
    have := hgt.add hht; simpa using this
  -- eventual bound  T n / S n ≤ glo n + ghi n
  have hev1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ε / 4 * (n : ℝ) :=
    (Filter.Tendsto.const_mul_atTop (by linarith : (0:ℝ) < ε/4)
      (tendsto_natCast_atTop_atTop (R := ℝ)) |>.eventually_ge_atTop 1)
  have hbound : ∀ᶠ n : ℕ in atTop,
      (∑' k : {k : ℕ // (k : ℝ) < (x₀ - ε) * n ∨ (x₀ + ε) * n < (k : ℝ)}, u n k) / S n
        ≤ glo n + ghi n := by
    filter_upwards [hlower, hupperMid, hupperTel, hev1] with n hln humn hutn hn1
    -- shorthands
    set Nlo := ⌈(x₀ - ε) * (n : ℝ)⌉₊ with hNlo
    set K := ⌊(x₀ + ε) * (n : ℝ)⌋₊ + 1 with hK
    set dn := ⌊ε / 4 * (n : ℝ)⌋₊ with hdn
    have hS_eq : S n = ∑' k, u n k := hS n
    have hSpos : 0 < S n := by
      rw [hS_eq]; exact (hsum n).tsum_pos (fun k => (hpos n k).le) 0 (hpos n 0)
    have hab : (x₀ - ε) * (n : ℝ) ≤ (x₀ + ε) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
    have hsplit := tail_decomp (hsum n) hab
    -- K ≥ dn + 1
    have hKdn : dn + 1 ≤ K := by
      rw [hK, hdn]
      have : ⌊ε / 4 * (n : ℝ)⌋₊ ≤ ⌊(x₀ + ε) * (n : ℝ)⌋₊ :=
        Nat.floor_mono (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n))
      omega
    -- reference points
    have hmhiB : (x₀ + ε / 2) * (n : ℝ) ≤ ((K - (dn + 1) : ℕ) : ℝ) := by
      have hKlow : (x₀ + ε) * (n : ℝ) < (K : ℝ) := by
        rw [hK]; push_cast; exact Nat.lt_floor_add_one _
      have hdnbd : (dn : ℝ) ≤ ε / 4 * (n : ℝ) := by rw [hdn]; exact Nat.floor_le (by positivity)
      have hcast : ((K - (dn + 1) : ℕ) : ℝ) = (K : ℝ) - ((dn : ℝ) + 1) := by
        have : dn + 1 ≤ K := hKdn
        push_cast [Nat.cast_sub this]; ring
      rw [hcast]
      have key : (x₀ + ε / 2) * (n : ℝ) + ε / 4 * (n : ℝ) + ε / 4 * (n : ℝ)
          = (x₀ + ε) * (n : ℝ) := by ring
      linarith [hKlow, hdnbd, hn1, key]
    have hK1C : ((K - 1 : ℕ) : ℝ) ≤ (x₀ + ε) * (n : ℝ) := by
      rw [hK]
      simp only [Nat.add_sub_cancel]
      exact Nat.floor_le (mul_nonneg hxε (Nat.cast_nonneg n))
    have hKrel : ∀ k : ℕ, (x₀ + ε) * (n : ℝ) < (k : ℝ) ↔ K ≤ k := by
      intro k
      rw [hK, Nat.add_one_le_iff, Nat.floor_lt (mul_nonneg hxε (Nat.cast_nonneg n))]
    have hglonn : 0 ≤ glo n := by rw [hglo]; positivity
    have hghinn : 0 ≤ ghi n := by
      rw [hghi]; refine mul_nonneg (mul_nonneg (by positivity) hS2nn) ?_
      exact pow_nonneg (by linarith) _
    -- lower finite-sum bound
    have hlowfin : (∑ k ∈ Finset.range Nlo, u n k) ≤ glo n * u n (Nlo + dn) := by
      rcases Nat.eq_zero_or_pos Nlo with hN0 | hNpos
      · rw [hN0, Finset.range_zero, Finset.sum_empty]
        exact mul_nonneg hglonn (hpos n _).le
      · have hpos' : 0 < (x₀ - ε) * (n : ℝ) := by
          by_contra h; push_neg at h
          rw [hNlo, Nat.ceil_eq_zero.mpr h] at hNpos; exact absurd hNpos (by norm_num)
        have hAbd : ((Nlo + dn : ℕ) : ℝ) - 1 ≤ (x₀ - ε / 2) * (n : ℝ) := by
          have hNlobd : (Nlo : ℝ) ≤ (x₀ - ε) * (n : ℝ) + 1 := by
            rw [hNlo]; exact (Nat.ceil_lt_add_one hpos'.le).le
          have hdnbd : (dn : ℝ) ≤ ε / 4 * (n : ℝ) := by rw [hdn]; exact Nat.floor_le (by positivity)
          have key : (x₀ - ε) * (n : ℝ) + ε / 4 * (n : ℝ) ≤ (x₀ - ε / 2) * (n : ℝ) := by
            have he : (x₀ - ε) * (n : ℝ) + ε / 4 * (n : ℝ) = (x₀ - 3 * ε / 4) * (n : ℝ) := by ring
            rw [he]; exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
          push_cast; linarith [hNlobd, hdnbd, key]
        have hlt := lower_tail_le (hpos n) hδlo hln Nlo dn hAbd
        calc (∑ k ∈ Finset.range Nlo, u n k)
            ≤ (Nlo : ℝ) * ((1 + δlo)⁻¹) ^ (dn + 1) * u n (Nlo + dn) := hlt
          _ = glo n * u n (Nlo + dn) := by simp only [hglo, hβlo, hNlo, hdn]
    -- upper subtype bound
    have hupfin : (∑' k : {k : ℕ // (x₀ + ε) * (n : ℝ) < (k : ℝ)}, u n k)
        ≤ ghi n * u n (K - (dn + 1)) := by
      have hmain : (∑' k : {k : ℕ // (x₀ + ε) * (n : ℝ) < (k : ℝ)}, u n k)
          ≤ ((K : ℝ) + shift n) ^ 2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2) *
              ((1 - δhi) ^ (dn + 1) * u n (K - (dn + 1))) :=
        upper_tail_le (hpos n) (hsum n) hδhi hδhi1 (hshift1 n) humn hutn
          K (K - (dn + 1)) (dn + 1) (by omega) hmhiB hK1C hKrel
      rw [hghi]
      calc (∑' k : {k : ℕ // (x₀ + ε) * (n : ℝ) < (k : ℝ)}, u n k)
          ≤ ((K : ℝ) + shift n) ^ 2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2) *
              ((1 - δhi) ^ (dn + 1) * u n (K - (dn + 1))) := hmain
        _ = (((⌊(x₀ + ε) * (n : ℝ)⌋₊ + 1 : ℕ) : ℝ) + shift n) ^ 2 * S₂ *
              (1 - δhi) ^ (dn + 1) * u n (K - (dn + 1)) := by rw [hS2, hK]; push_cast; ring
    -- combine
    have hmlo_le : u n (Nlo + dn) ≤ S n := by
      rw [hS_eq]; exact (hsum n).le_tsum _ (fun j _ => (hpos n j).le)
    have hmhi_le : u n (K - (dn + 1)) ≤ S n := by
      rw [hS_eq]; exact (hsum n).le_tsum _ (fun j _ => (hpos n j).le)
    rw [hsplit, div_le_iff₀ hSpos]
    calc (∑ k ∈ Finset.range Nlo, u n k)
            + (∑' k : {k : ℕ // (x₀ + ε) * (n : ℝ) < (k : ℝ)}, u n k)
        ≤ glo n * u n (Nlo + dn) + ghi n * u n (K - (dn + 1)) := add_le_add hlowfin hupfin
      _ ≤ glo n * S n + ghi n * S n :=
            add_le_add (mul_le_mul_of_nonneg_left hmlo_le hglonn)
              (mul_le_mul_of_nonneg_left hmhi_le hghinn)
      _ = (glo n + ghi n) * S n := by ring
  exact squeeze_zero' (Eventually.of_forall (fun n => by
    have hSpos : 0 < S n := by
      rw [hS n]; exact (hsum n).tsum_pos (fun k => (hpos n k).le) 0 (hpos n 0)
    exact div_nonneg (tsum_nonneg (fun x => (hpos n x).le)) hSpos.le)) hbound htendsto

/-! ### Analytic cores for `c` (term ratio ≈ f(k/n)²)

These four `sorry`s are the *only* remaining gaps.  Each reduces, via the exact
identity `c_ratio` (and `chat`'s analogue), to a bound on the term ratio
`ρ(j,n) := c q n (j+1) / c q n j
   = (6n+2j+4)(6n+2j+3)/((2j+3)(2j+2)) · ((n+j+1)/(2n+j+2))^(2q)`,
which tends to `f(j/n)²` as `n → ∞` (uniformly on `j/n` in compact subsets of
`(0,∞)`).  Two analytic inputs are needed:

* **Profile shape** (reproduce from `Basic.existsUnique_x0`'s internal `L`,`N`
  machinery): `f q x > 1` for `0 < x < x₀` and `f q x < 1` for `x > x₀`
  (here `x₀` is *the* unique positive crossing by `existsUnique_x0` + `hfx₀`).
* **Ratio ≈ profile²**: `ρ(j,n) = f(j/n)²·(1 + O(1/n))` with the `O(1/n)`
  uniform on `j/n ∈ [x_min, x_max]` (bounded away from `0`).  For the far-tail
  telescoping bound the exponent `2q ≥ 8` and `q ≥ 4` are what make the `B`-power
  decay beat the `A`-growth so that `ρ ≤ ((j+2n+2)/(j+2n+3))²` above `(x₀+ε/2)n`.

The lower core gives a uniform *constant* margin (min of `f²` on `(0,x₀-ε/2]`);
the upper core gives both a constant margin on `[(x₀+ε/2)n,(x₀+ε)n]` and the
telescoping square-ratio majorant that controls `k ≫ n` where the margin decays. -/

/-- Shape of the profile `f`: there is a turning point `x₁ > x₀` with `f`
strictly decreasing on `(0, x₁)`, and `f < 1` on all of `(x₀, ∞)`.  (Reproduces
the `L`/`N` log-derivative analysis of `Basic.existsUnique_x0` and pins `x₀` to
the unique crossing via that theorem.) -/
private lemma f_shape (q : ℕ) (hq : 4 ≤ q) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfx₀ : f q x₀ = 1) :
    ∃ x₁ : ℝ, x₀ < x₁ ∧ StrictAntiOn (f q) (Set.Ioo 0 x₁) ∧
      (∀ x : ℝ, x₀ < x → f q x < 1) := by
  set qr : ℝ := (q : ℝ) with hqr
  have hqr4 : (4 : ℝ) ≤ qr := by rw [hqr]; exact_mod_cast hq
  set N : ℝ → ℝ := fun x => (qr - 3) * x ^ 2 + 3 * (qr - 3) * x - 6 with hN
  set L : ℝ → ℝ := fun x =>
    Real.log (x + 3) - Real.log x + qr * (Real.log (x + 1) - Real.log (x + 2)) with hL
  have hfpos : ∀ x : ℝ, 0 < x → 0 < f q x := by
    intro x hx
    have : (0:ℝ) < (x+1)/(x+2) := by positivity
    unfold f; positivity
  have hLlog : ∀ x : ℝ, 0 < x → Real.log (f q x) = L x := by
    intro x hx
    unfold f
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_div (by positivity) (by positivity), hL]
  have hfexp : ∀ x : ℝ, 0 < x → f q x = Real.exp (L x) := by
    intro x hx; rw [← hLlog x hx, Real.exp_log (hfpos x hx)]
  have hf1 : ∀ x : ℝ, 0 < x → (f q x = 1 ↔ L x = 0) := by
    intro x hx
    rw [← hLlog x hx]
    constructor
    · intro h; rw [h]; exact Real.log_one
    · intro h; exact Real.eq_one_of_pos_of_log_eq_zero (hfpos x hx) h
  have hLderiv : ∀ x : ℝ, 0 < x →
      HasDerivAt L (N x / (x * (x + 1) * (x + 2) * (x + 3))) x := by
    intro x hx
    have e3 : HasDerivAt (fun y : ℝ => Real.log (y + 3)) (1 / (x + 3)) x := by
      have := ((hasDerivAt_id x).add_const (3:ℝ)).log (by positivity); simpa using this
    have e0 : HasDerivAt (fun y : ℝ => Real.log y) (1 / x) x := by
      simpa using (Real.hasDerivAt_log (by positivity : x ≠ 0))
    have e1 : HasDerivAt (fun y : ℝ => Real.log (y + 1)) (1 / (x + 1)) x := by
      have := ((hasDerivAt_id x).add_const (1:ℝ)).log (by positivity); simpa using this
    have e2 : HasDerivAt (fun y : ℝ => Real.log (y + 2)) (1 / (x + 2)) x := by
      have := ((hasDerivAt_id x).add_const (2:ℝ)).log (by positivity); simpa using this
    have hd := (e3.sub e0).add ((e1.sub e2).const_mul qr)
    have heq : 1 / (x + 3) - 1 / x + qr * (1 / (x + 1) - 1 / (x + 2))
        = N x / (x * (x + 1) * (x + 2) * (x + 3)) := by rw [hN]; field_simp; ring
    rw [heq] at hd; exact hd
  have hNmono : StrictMonoOn N (Set.Ici 0) := by
    intro a ha b hb hab
    simp only [Set.mem_Ici] at ha hb
    simp only [hN]
    nlinarith [mul_pos (mul_pos (show (0:ℝ) < qr - 3 by linarith)
      (show (0:ℝ) < b - a by linarith)) (show (0:ℝ) < b + a + 3 by linarith)]
  have hNcont : Continuous N := by rw [hN]; fun_prop
  have hN0 : N 0 = -6 := by rw [hN]; ring
  have hN3 : 0 < N 3 := by simp only [hN]; nlinarith [hqr4]
  obtain ⟨x₁, hx₁mem, hx₁0⟩ : ∃ x ∈ Set.Icc (0:ℝ) 3, N x = 0 := by
    have hmem : (0:ℝ) ∈ Set.Icc (N 0) (N 3) := by
      rw [Set.mem_Icc, hN0]; exact ⟨by norm_num, hN3.le⟩
    obtain ⟨x, hx, hxeq⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 3)
      hNcont.continuousOn hmem
    exact ⟨x, hx, hxeq⟩
  have hx₁pos : 0 < x₁ := by
    rcases lt_or_eq_of_le hx₁mem.1 with h | h
    · exact h
    · exfalso; rw [← h] at hx₁0; rw [hN0] at hx₁0; norm_num at hx₁0
  have hNneg : ∀ x : ℝ, 0 < x → x < x₁ → N x < 0 := by
    intro x hx hxx₁
    have := hNmono (Set.mem_Ici.mpr hx.le) (Set.mem_Ici.mpr hx₁pos.le) hxx₁
    rw [hx₁0] at this; exact this
  have hNpos : ∀ x : ℝ, x₁ < x → 0 < N x := by
    intro x hxx₁
    have := hNmono (Set.mem_Ici.mpr hx₁pos.le) (Set.mem_Ici.mpr (by linarith : (0:ℝ) ≤ x)) hxx₁
    rw [hx₁0] at this; exact this
  have hden : ∀ x : ℝ, 0 < x → 0 < x * (x + 1) * (x + 2) * (x + 3) := by
    intro x hx; positivity
  have hLcont1 : ContinuousOn L (Set.Ioo 0 x₁) :=
    fun x hx => (hLderiv x hx.1).continuousAt.continuousWithinAt
  have hLanti : StrictAntiOn L (Set.Ioo 0 x₁) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo 0 x₁) hLcont1
    rw [interior_Ioo]
    intro x hx
    rw [(hLderiv x hx.1).deriv]
    exact div_neg_of_neg_of_pos (hNneg x hx.1 hx.2) (hden x hx.1)
  have hLcont2 : ContinuousOn L (Set.Ici x₁) :=
    fun x hx => (hLderiv x (lt_of_lt_of_le hx₁pos hx)).continuousAt.continuousWithinAt
  have hLmono : StrictMonoOn L (Set.Ici x₁) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici x₁) hLcont2
    rw [interior_Ici]
    intro x hx
    rw [(hLderiv x (lt_trans hx₁pos hx)).deriv]
    exact div_pos (hNpos x hx) (hden x (lt_trans hx₁pos hx))
  have hLtend0 : Tendsto L atTop (𝓝 0) := by
    have key : ∀ a b : ℝ,
        Tendsto (fun x : ℝ => Real.log (x + a) - Real.log (x + b)) atTop (𝓝 0) := by
      intro a b
      have hr : Tendsto (fun x : ℝ => (x + a) / (x + b)) atTop (𝓝 1) := by
        have h0 : Tendsto (fun x : ℝ => (a - b) / (x + b)) atTop (𝓝 0) :=
          Tendsto.div_atTop tendsto_const_nhds
            (tendsto_atTop_add_const_right atTop b tendsto_id)
        have h1 : Tendsto (fun x : ℝ => 1 + (a - b) / (x + b)) atTop (𝓝 1) := by
          simpa using h0.const_add 1
        refine h1.congr' ?_
        filter_upwards [eventually_gt_atTop (-b)] with x hx
        have hxb : x + b ≠ 0 := ne_of_gt (by linarith)
        field_simp; ring
      have hc := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hr
      rw [Real.log_one] at hc
      refine hc.congr' ?_
      filter_upwards [eventually_gt_atTop (max (-a) (-b))] with x hx
      rw [max_lt_iff] at hx
      exact Real.log_div (ne_of_gt (by linarith [hx.1] : (0:ℝ) < x + a))
        (ne_of_gt (by linarith [hx.2] : (0:ℝ) < x + b))
    have hA : Tendsto (fun x : ℝ => Real.log (x + 3) - Real.log x) atTop (𝓝 0) := by
      refine (key 3 0).congr (fun x => ?_); rw [add_zero]
    have hB := ((key 1 2).const_mul qr)
    have := hA.add hB
    simp only [mul_zero, add_zero] at this
    exact this.congr (fun x => by simp only [hL])
  have hLneg : ∀ x : ℝ, x₁ ≤ x → L x < 0 := by
    intro x hx
    have h1 : L x < L (x + 1) :=
      hLmono (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (by linarith)) (by linarith)
    have h2 : L (x + 1) ≤ 0 := by
      refine ge_of_tendsto hLtend0 ?_
      filter_upwards [eventually_ge_atTop (x + 1)] with y hy
      exact hLmono.monotoneOn (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) hy
    linarith
  -- `x₀` is the unique crossing, hence `x₀ < x₁`.
  have hLx₀ : L x₀ = 0 := (hf1 x₀ hx₀).mp hfx₀
  have hx₀x₁ : x₀ < x₁ := by
    by_contra h; push_neg at h; exact absurd hLx₀ (ne_of_lt (hLneg x₀ h))
  refine ⟨x₁, hx₀x₁, ?_, ?_⟩
  · -- StrictAntiOn (f q) (Ioo 0 x₁)
    intro a ha b hb hab
    rw [hfexp a ha.1, hfexp b hb.1]
    exact Real.exp_lt_exp.mpr (hLanti ha hb hab)
  · -- f < 1 on (x₀, ∞)
    intro x hx
    have hxpos : 0 < x := lt_trans hx₀ hx
    have hLx : L x < 0 := by
      rcases lt_or_ge x x₁ with hlt | hge
      · have := hLanti (Set.mem_Ioo.mpr ⟨hx₀, hx₀x₁⟩) (Set.mem_Ioo.mpr ⟨hxpos, hlt⟩) hx
        rwa [hLx₀] at this
      · exact hLneg x hge
    rw [hfexp x hxpos]
    calc Real.exp (L x) < Real.exp 0 := Real.exp_lt_exp.mpr hLx
      _ = 1 := Real.exp_zero

/-- Bernoulli bridge for the `2q`-th power (`B`-part of the term ratio): the exact
base `(n+j+1)/(2n+j+2)` beats the profile base `(n+j)/(2n+j)` up to a `1 - 2q/n`
factor. -/
private lemma bridge_B (q j n : ℕ) (hn : 1 ≤ n) :
    (1 - 2 * (q : ℝ) / n) * (((n + j : ℕ) : ℝ) / ((2 * n + j : ℕ) : ℝ)) ^ (2 * q)
      ≤ (((n + j + 1 : ℕ) : ℝ) / ((2 * n + j + 2 : ℕ) : ℝ)) ^ (2 * q) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnj1 : (0 : ℝ) < ((n + j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n + j)
  have hd1 : (0 : ℝ) < ((2 * n + j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * n + j)
  have hd2 : (0 : ℝ) < ((2 * n + j + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2 * n + j + 2)
  have hnj2 : (0 : ℝ) < ((n + j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n + j + 1)
  set bB : ℝ := ((n + j + 1 : ℕ) : ℝ) / ((2 * n + j + 2 : ℕ) : ℝ) with hbB
  set bg : ℝ := ((n + j : ℕ) : ℝ) / ((2 * n + j : ℕ) : ℝ) with hbg
  have hbg_pos : 0 < bg := by rw [hbg]; exact div_pos hnj1 hd1
  -- r := bB / bg ≥ 1 - 1/n
  set r : ℝ := bB / bg with hr
  have hbBr : bB = r * bg := by rw [hr]; field_simp
  have hkey : (1 - 1 / (n : ℝ)) * bg ≤ bB := by
    rw [← sub_nonneg, hbB, hbg]
    have expand : ((n + j + 1 : ℕ) : ℝ) / ((2 * n + j + 2 : ℕ) : ℝ)
          - (1 - 1 / (n : ℝ)) * (((n + j : ℕ) : ℝ) / ((2 * n + j : ℕ) : ℝ))
        = ((j : ℝ) ^ 2 + 2 * (n : ℝ) * (j : ℝ) + 2 * (j : ℝ) + 2 * (n : ℝ) ^ 2 + 2 * (n : ℝ))
          / ((n : ℝ) * ((2 * n + j : ℕ) : ℝ) * ((2 * n + j + 2 : ℕ) : ℝ)) := by
      rw [eq_div_iff (by positivity)]
      field_simp
      push_cast
      ring
    rw [expand]
    positivity
  have hr_lb : 1 - 1 / (n : ℝ) ≤ r := by rw [hr]; exact (le_div_iff₀ hbg_pos).mpr hkey
  have h1n : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hnR]; exact_mod_cast hn
  -- r^(2q) ≥ (1-1/n)^(2q) ≥ 1 - 2q/n
  have hpow1 : (1 - 1 / (n : ℝ)) ^ (2 * q) ≤ r ^ (2 * q) :=
    pow_le_pow_left₀ h1n hr_lb (2 * q)
  have hbern : 1 - 2 * (q : ℝ) / n ≤ (1 - 1 / (n : ℝ)) ^ (2 * q) := by
    have hH : (-2 : ℝ) ≤ -(1 / (n : ℝ)) := by
      have : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact_mod_cast hn
      linarith
    have := one_add_mul_le_pow hH (2 * q)
    have hrw : (1 : ℝ) + (2 * q : ℕ) * (-(1 / (n : ℝ))) = 1 - 2 * (q : ℝ) / n := by
      push_cast; ring
    have hrw2 : (1 : ℝ) + -(1 / (n : ℝ)) = 1 - 1 / (n : ℝ) := by ring
    rw [hrw, hrw2] at this
    exact this
  have hr2q : 1 - 2 * (q : ℝ) / n ≤ r ^ (2 * q) := le_trans hbern hpow1
  calc (1 - 2 * (q : ℝ) / n) * bg ^ (2 * q)
      ≤ r ^ (2 * q) * bg ^ (2 * q) :=
        mul_le_mul_of_nonneg_right hr2q (by positivity)
    _ = (r * bg) ^ (2 * q) := by rw [mul_pow]
    _ = bB ^ (2 * q) := by rw [← hbBr]

/-- Rational bridge for the `A`-part of the term ratio: it beats the profile
`g₁(j/n) = ((j+3n)/j)²` up to a `1 - 4/j` factor (`j ≥ 1`). -/
private lemma bridge_A (j n : ℕ) (hj : 1 ≤ j) :
    (1 - 4 / (j : ℝ)) * (((j : ℝ) + 3 * n) ^ 2 / (j : ℝ) ^ 2)
      ≤ (6 * (n : ℝ) + 2 * j + 4) * (6 * (n : ℝ) + 2 * j + 3)
          / ((2 * (j : ℝ) + 3) * (2 * (j : ℝ) + 2)) := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : (0 : ℝ) < 2 * (j : ℝ) ^ 2 + 5 * j + 3 := by positivity
  set g1 : ℝ := ((j : ℝ) + 3 * n) ^ 2 / (j : ℝ) ^ 2 with hg1
  have hg1nn : 0 ≤ g1 := by rw [hg1]; positivity
  set A : ℝ := (6 * (n : ℝ) + 2 * j + 4) * (6 * (n : ℝ) + 2 * j + 3)
      / ((2 * (j : ℝ) + 3) * (2 * (j : ℝ) + 2)) with hA
  set D : ℝ := 2 * (j : ℝ) ^ 2 / (2 * (j : ℝ) ^ 2 + 5 * j + 3) with hD
  have step2 : 1 - 4 / (j : ℝ) ≤ D := by
    rw [hD, ← sub_nonneg]
    have hEq : 2 * (j : ℝ) ^ 2 / (2 * (j : ℝ) ^ 2 + 5 * j + 3) - (1 - 4 / (j : ℝ))
        = (3 * (j : ℝ) ^ 2 + 17 * j + 12) / ((j : ℝ) * (2 * (j : ℝ) ^ 2 + 5 * j + 3)) := by
      field_simp; ring
    rw [hEq]; positivity
  have step1 : D * g1 ≤ A := by
    rw [← sub_nonneg, hA, hD, hg1]
    have hEq : (6 * (n : ℝ) + 2 * j + 4) * (6 * (n : ℝ) + 2 * j + 3)
            / ((2 * (j : ℝ) + 3) * (2 * (j : ℝ) + 2))
          - 2 * (j : ℝ) ^ 2 / (2 * (j : ℝ) ^ 2 + 5 * j + 3)
              * (((j : ℝ) + 3 * n) ^ 2 / (j : ℝ) ^ 2)
        = (42 * (n : ℝ) + 14 * j + 12) / (2 * (2 * (j : ℝ) ^ 2 + 5 * j + 3)) := by
      field_simp; ring
    rw [hEq]; positivity
  calc (1 - 4 / (j : ℝ)) * g1 ≤ D * g1 := mul_le_mul_of_nonneg_right step2 hg1nn
    _ ≤ A := step1

/-- Combined lower bound for the term ratio (`c_ratio` × `bridge_A` × `bridge_B`):
`c(j+1)/c(j) ≥ (1-4/j)(1-2q/n)·f(j/n)²`. -/
private lemma c_ratio_lb (q j n : ℕ) (hj : 1 ≤ j) (hn : 1 ≤ n) (hn2q : 2 * q ≤ n) :
    (1 - 4 / (j : ℝ)) * (1 - 2 * (q : ℝ) / n) * f q ((j : ℝ) / n) ^ 2
      ≤ c q n (j + 1) / c q n j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  set g1 : ℝ := ((j : ℝ) + 3 * n) ^ 2 / (j : ℝ) ^ 2 with hg1
  set g2 : ℝ := (((n + j : ℕ) : ℝ) / ((2 * n + j : ℕ) : ℝ)) ^ (2 * q) with hg2
  have hg1nn : 0 ≤ g1 := by rw [hg1]; positivity
  have hg2nn : 0 ≤ g2 := by rw [hg2]; positivity
  have e1 : ((j : ℝ) / n + 3) / ((j : ℝ) / n) = ((j : ℝ) + 3 * n) / (j : ℝ) := by
    field_simp
  have e2 : ((j : ℝ) / n + 1) / ((j : ℝ) / n + 2) = ((n + j : ℕ) : ℝ) / ((2 * n + j : ℕ) : ℝ) := by
    push_cast; field_simp; ring
  have hfeval : f q ((j : ℝ) / n) ^ 2 = g1 * g2 := by
    unfold f
    rw [e1, e2, mul_pow, ← pow_mul, mul_comm q 2, div_pow, hg1, hg2]
  rw [hfeval]
  have hA := bridge_A j n hj
  have hB := bridge_B q j n hn
  rw [c_ratio]
  have h2qn : 0 ≤ 1 - 2 * (q : ℝ) / n := by
    rw [sub_nonneg, div_le_one hnR]; exact_mod_cast hn2q
  rcases le_or_gt 0 (1 - 4 / (j : ℝ)) with h4 | h4
  · calc (1 - 4 / (j : ℝ)) * (1 - 2 * (q : ℝ) / n) * (g1 * g2)
        = ((1 - 4 / (j : ℝ)) * g1) * ((1 - 2 * (q : ℝ) / n) * g2) := by ring
      _ ≤ _ := mul_le_mul hA hB (mul_nonneg h2qn hg2nn) (le_trans (by positivity) hA)
  · have hLneg : (1 - 4 / (j : ℝ)) * (1 - 2 * (q : ℝ) / n) * (g1 * g2) ≤ 0 := by
      have : (1 - 4 / (j : ℝ)) * (1 - 2 * (q : ℝ) / n) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt h4) h2qn
      exact mul_nonpos_of_nonpos_of_nonneg this (mul_nonneg hg1nn hg2nn)
    exact le_trans hLneg (by positivity)

/-- Lower geometric margin for `c`: below `(x₀ - ε/2)·n` the term ratio
`c(j+1)/c(j)` (given exactly by `c_ratio`) exceeds `1 + δ`, because
`f(j/n)² ≥ f(x₀-ε/2)² > 1` on `(0, x₀)` and `ρ → f²`. -/
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
