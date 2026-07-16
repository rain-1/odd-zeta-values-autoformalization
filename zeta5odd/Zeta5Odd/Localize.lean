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
