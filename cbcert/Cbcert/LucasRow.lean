import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Int.GCD
import Cbcert.Defs

/-!
# T1 — the Lucas–Frobenius `q`-row theorem

The Brown–Zudilin weight-`0` ladder is captured by the manifestly-integral
double-binomial sum

    `Q n = Σ_{k,l ∈ range (n+1)} C(n+k,n)·C(n,k)²·C(n+l,n)·C(n,l)²·C(n+k+l,n)`

(see `worthiness/PHASE2_SALVAGE_VERIFY.md` §V2: `Q n = (−1)^{n+1}·q_n/C(2n,n)`,
integers `1, 21, 2989, 714549, …`).  The theorem (`Q_lucas_frobenius`) is the first
row of the Frobenius matrix: for every prime `p` and `r < p`,

    `Q (a*p + r) ≡ Q a · Q r  (mod p)`.

## Proof route (mirror `worthiness/salvage_v3_lucas_proof.py`, VERIFIED on 2.19M
summands, 0 exceptions)

Split every index in base `p`: `k = b*p + s`, `l = c*p + t` (`0 ≤ s,t < p`),
`N = a*p + r`.  Two claims:

* **(CARRY-KILL)** the summand
  `T(k,l) = C(N+k,N)·C(N,k)²·C(N+l,N)·C(N,l)²·C(N+k+l,N)`
  satisfies `T ≡ 0 (mod p)` unless **all** of `b ≤ a, c ≤ a, s ≤ r, t ≤ r,
  r+s < p, r+t < p, r+s+t < p`.  Any base-`p` carry pushes a low digit of one
  argument below the corresponding digit of `N`, so a Lucas factor `C(·, r) = 0`
  (or `C(r, s) = 0`).  Mathlib input: `Choose.choose_modEq_choose_mod_mul_choose_div`
  (single-digit Lucas: `choose n k ≡ choose (n%p) (k%p) * choose (n/p) (k/p) [ZMOD p]`).
* **(FACTOR)** on the surviving box the summand splits
  `T(bp+s, cp+t) ≡ T_hi(b,c;a)·T_lo(s,t;r) (mod p)`, where
  `T_hi = C(a+b,a)C(a,b)²C(a+c,a)C(a,c)²C(a+b+c,a)` is the `(b,c)`-summand of `Q a`
  and `T_lo` the `(s,t)`-summand of `Q r`.

Summation over the box gives `Q N ≡ (Σ T_hi)(Σ T_lo) = Q a · Q r`, the surviving
high box being exactly `{0 ≤ b,c ≤ a}` (support of `Q a` mod `p`) and the low box
the mod-`p` support of `Q r`.

House rules: no `sorry` at completion, no `native_decide`, no new axioms, axioms
exactly `[propext, Classical.choice, Quot.sound]`.

**Bridge to the project's `q_n` (STAGED, honest note):** `Q n = (−1)^{n+1}·q_n /
C(2n,n)` with `q_n = u_n·w̃_n − ũ_n·w_n` (`Cbcert/Defs.lean`; `ErrorExhibit.Q2_eq`
already proves `−(u·w̃ − ũ·w)/6 = 2989 = Q 2`).  This normalization bridge is not
needed for the standalone congruence and is left for a follow-up wave.
-/

namespace Cbcert.LucasRow

open Finset

/-- The Brown–Zudilin double-binomial weight-`0` value, over `ℕ`
(manifestly a natural number). -/
def Q (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
    Nat.choose (n + k) n * (Nat.choose n k) ^ 2 * Nat.choose (n + l) n
      * (Nat.choose n l) ^ 2 * Nat.choose (n + k + l) n

/-- The `(k,l)`-summand of `Q n`, factored out so that the row theorem can talk
about summands of `Q (a*p+r)`, `Q a` and `Q r` uniformly. By construction
`Q n = ∑ k ∈ range (n+1), ∑ l ∈ range (n+1), S n k l` (`Q_eq`, definitional). -/
def S (n k l : ℕ) : ℕ :=
  Nat.choose (n + k) n * (Nat.choose n k) ^ 2 * Nat.choose (n + l) n
    * (Nat.choose n l) ^ 2 * Nat.choose (n + k + l) n

/-! ### Numeric gate

`Q` reproduces the verified integer sequence `1, 21, 2989, 714549, …`
(`worthiness/salvage_data.py`, PHASE2 §V2). `Q 2 = 2989` matches
`ErrorExhibit.Q2_eq`. Kernel `decide` only, no `native_decide`. -/

theorem Q_zero : Q 0 = 1 := by decide
theorem Q_one : Q 1 = 21 := by decide
theorem Q_two : Q 2 = 2989 := by decide
theorem Q_three : Q 3 = 714549 := by decide
theorem Q_four : Q 4 = 217515501 := by decide

-- `Q 5 = 76157194521`, `Q 6 = 29212502584861` (cross-checked exactly in
-- `worthiness/salvage_data.py`; omitted from the kernel gate for build speed).

/-- Sanity instance of the congruence, `Q (2·5+2) ≡ Q 2 · Q 2 (mod 5)`
(`Q 12 mod 5 = (2989·2989) mod 5`), verified in `salvage_v123.py`
(1592 checks, 0 failures). Documented here; the general theorem is
`Q_lucas_frobenius`. -/
example : True := trivial

/-! ### The theorem -/

/-- **Lucas–Frobenius `q`-row.** For every prime `p` and `r < p`,
`Q (a*p + r) ≡ Q a · Q r (mod p)`. -/
theorem Q_lucas_frobenius (a r p : ℕ) (hp : p.Prime) (hr : r < p) :
    (Q (a * p + r) : ℤ) ≡ (Q a : ℤ) * (Q r : ℤ) [ZMOD (p : ℤ)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- Reduce the ℤ-congruence to an equality in `ZMod p`.
  have goalcast : ((Q a : ℤ) * (Q r : ℤ)) = ((Q a * Q r : ℕ) : ℤ) := by push_cast; ring
  rw [goalcast, Int.natCast_modEq_iff, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  -- `Q n` as a double sum of the factored summand `S`.
  have Q_eq : ∀ n : ℕ, Q n = ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1), S n k l := fun n => rfl
  have hsub : ∀ m n : ℕ, m ≤ n → range m ⊆ range n :=
    fun m n h => Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le hx h))
  -- Base-`p` digit arithmetic: for `y < p`, `(x*p+y) % p = y` and `(x*p+y) / p = x`.
  have hmodp : ∀ x y : ℕ, y < p → (x * p + y) % p = y := by
    intro x y hy
    rw [Nat.mul_comm x p, Nat.add_comm (p * x) y, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
  have hdivp : ∀ x y : ℕ, y < p → (x * p + y) / p = x := by
    intro x y hy
    have hm := hmodp x y hy
    have hd := Nat.div_add_mod (x * p + y) p
    rw [hm] at hd
    have h2 : p * ((x * p + y) / p) = p * x := by rw [Nat.mul_comm p x]; omega
    exact Nat.eq_of_mul_eq_mul_left hp.pos h2
  -- Single-digit Lucas over `ZMod p`.
  have lucas1 : ∀ n k : ℕ, (Nat.choose n k : ZMod p)
      = (Nat.choose (n % p) (k % p) : ZMod p) * (Nat.choose (n / p) (k / p) : ZMod p) := by
    intro n k
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := p)
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ p).2 h
    push_cast at h2
    exact h2
  -- A carried high digit kills a Lucas factor: `choose m d ≡ 0 (mod p)` when `d < p`,
  -- `p ≤ m < 2p` and `m - p < d`.
  have hzero : ∀ m d : ℕ, d < p → p ≤ m → m < 2 * p → m - p < d →
      (Nat.choose m d : ZMod p) = 0 := by
    intro m d hd hpm hm2 hmd
    have h1 : m % p = m - p := by
      conv_lhs => rw [show m = 1 * p + (m - p) from by omega]
      rw [hmodp 1 (m - p) (by omega)]
    have h3 : m / p = 1 := by
      conv_lhs => rw [show m = 1 * p + (m - p) from by omega]
      rw [hdivp 1 (m - p) (by omega)]
    rw [lucas1 m d, h1, h3, Nat.mod_eq_of_lt hd, Nat.div_eq_of_lt hd,
      Nat.choose_eq_zero_of_lt hmd]
    simp
  -- Factor `choose N k` where `N = x*p+z`, `k = y*p+w` (`z,w < p`).
  have LA : ∀ x z y w : ℕ, z < p → w < p →
      (Nat.choose (x * p + z) (y * p + w) : ZMod p)
        = (Nat.choose z w : ZMod p) * (Nat.choose x y : ZMod p) := by
    intro x z y w hz hw
    rw [lucas1 (x * p + z) (y * p + w), hmodp x z hz, hmodp y w hw, hdivp x z hz, hdivp y w hw]
  -- Factor `choose (N+k) N` where `N = x*p+z`, `k = y*p+w` (`z,w < p`).
  have LB : ∀ x y z w : ℕ, z < p → w < p →
      (Nat.choose ((x * p + z) + (y * p + w)) (x * p + z) : ZMod p)
        = (Nat.choose (z + w) z : ZMod p) * (Nat.choose (x + y) x : ZMod p) := by
    intro x y z w hz hw
    have hrw : (x * p + z) + (y * p + w) = (x + y) * p + (z + w) := by ring
    rw [hrw, lucas1 ((x + y) * p + (z + w)) (x * p + z), hmodp x z hz, hdivp x z hz]
    rcases lt_or_ge (z + w) p with hlt | hge
    · rw [hmodp (x + y) (z + w) hlt, hdivp (x + y) (z + w) hlt]
    · have hsplit : (x + y) * p + (z + w) = (x + y + 1) * p + (z + w - p) := by
        have haux : (x + y + 1) * p = (x + y) * p + p := by ring
        omega
      rw [hsplit, hmodp (x + y + 1) (z + w - p) (by omega),
        hdivp (x + y + 1) (z + w - p) (by omega),
        Nat.choose_eq_zero_of_lt (show z + w - p < z by omega),
        hzero (z + w) z hz hge (by omega) (by omega)]
      simp
  -- Factor `choose (N+k+l) N` where `N = x*p+z`, `k = y1*p+w1`, `l = y2*p+w2`,
  -- under the no-carry hypothesis `w1 + w2 < p`.
  have LC : ∀ x y1 y2 z w1 w2 : ℕ, z < p → w1 + w2 < p →
      (Nat.choose (((x * p + z) + (y1 * p + w1)) + (y2 * p + w2)) (x * p + z) : ZMod p)
        = (Nat.choose (z + w1 + w2) z : ZMod p) * (Nat.choose (x + y1 + y2) x : ZMod p) := by
    intro x y1 y2 z w1 w2 hz hw
    have hrw : ((x * p + z) + (y1 * p + w1)) + (y2 * p + w2)
        = (x + y1 + y2) * p + (z + w1 + w2) := by ring
    rw [hrw, lucas1 ((x + y1 + y2) * p + (z + w1 + w2)) (x * p + z), hmodp x z hz, hdivp x z hz]
    rcases lt_or_ge (z + w1 + w2) p with hlt | hge
    · rw [hmodp (x + y1 + y2) (z + w1 + w2) hlt, hdivp (x + y1 + y2) (z + w1 + w2) hlt]
    · have hsplit : (x + y1 + y2) * p + (z + w1 + w2)
          = (x + y1 + y2 + 1) * p + (z + w1 + w2 - p) := by
        have haux : (x + y1 + y2 + 1) * p = (x + y1 + y2) * p + p := by ring
        omega
      rw [hsplit, hmodp (x + y1 + y2 + 1) (z + w1 + w2 - p) (by omega),
        hdivp (x + y1 + y2 + 1) (z + w1 + w2 - p) (by omega),
        Nat.choose_eq_zero_of_lt (show z + w1 + w2 - p < z by omega),
        hzero (z + w1 + w2) z hz hge (by omega) (by omega)]
      simp
  -- Cast expansion of `S` over `ZMod p`.
  have hcast : ∀ n k l : ℕ, (S n k l : ZMod p)
      = (Nat.choose (n + k) n : ZMod p) * (Nat.choose n k : ZMod p) ^ 2
        * (Nat.choose (n + l) n : ZMod p) * (Nat.choose n l : ZMod p) ^ 2
        * (Nat.choose (n + k + l) n : ZMod p) := by
    intro n k l; unfold S; push_cast; ring
  -- The pointwise factorization of a base-`p`-split summand.
  have POINT : ∀ b s c t : ℕ, s < p → t < p →
      (S (a * p + r) (b * p + s) (c * p + t) : ZMod p)
        = (S a b c : ZMod p) * (S r s t : ZMod p) := by
    intro b s c t hs ht
    rw [hcast (a * p + r) (b * p + s) (c * p + t), hcast a b c, hcast r s t]
    rw [LB a b r s hr hs, LA a r b s hr hs, LB a c r t hr ht, LA a r c t hr ht]
    rcases lt_or_ge (s + t) p with hst | hst
    · -- No carry: the fifth factor also splits (`LC`).
      rw [LC a b c r s t hr hst]; ring
    · -- Carry: a Lucas factor vanishes on both sides.
      by_cases hsr : r < s
      · have h0 : (Nat.choose r s : ZMod p) = 0 := by simp [Nat.choose_eq_zero_of_lt hsr]
        rw [h0]; ring
      · simp only [not_lt] at hsr
        have hrt : p ≤ r + t := by omega
        have h0 : (Nat.choose (r + t) r : ZMod p) = 0 :=
          hzero (r + t) r hr hrt (by omega) (by omega)
        rw [h0]; ring
  -- Reindex `range ((a+1)*p)` by base-`p` digits.
  have REIDX : ∀ f : ℕ → ZMod p,
      (∑ k ∈ range ((a + 1) * p), f k)
        = ∑ b ∈ range (a + 1), ∑ s ∈ range p, f (b * p + s) := by
    intro f
    rw [← Finset.sum_product']
    refine Finset.sum_bij' (fun k _ => (k / p, k % p)) (fun x _ => x.1 * p + x.2) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨(Nat.div_lt_iff_lt_mul hp.pos).2 hk, Nat.mod_lt _ hp.pos⟩
    · rintro ⟨x1, x2⟩ hx
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
      rw [Finset.mem_range]
      calc x1 * p + x2 < x1 * p + p := by omega
        _ = (x1 + 1) * p := by ring
        _ ≤ (a + 1) * p := Nat.mul_le_mul_right _ (by omega)
    · intro k _; exact Nat.div_add_mod' k p
    · rintro ⟨x1, x2⟩ hx
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
      rw [hdivp x1 x2 hx.2, hmodp x1 x2 hx.2]
    · intro k _; congr 1; exact (Nat.div_add_mod' k p).symm
  -- The `(b,c)`-box is exactly `Q a`.
  have hiEq : (∑ b ∈ range (a + 1), ∑ c ∈ range (a + 1), (S a b c : ZMod p)) = (Q a : ZMod p) := by
    rw [Q_eq a]; push_cast; rfl
  -- The full `(s,t)`-box over `range p` collapses to `Q r` (large digits are killed).
  have loEq : (∑ s ∈ range p, ∑ t ∈ range p, (S r s t : ZMod p)) = (Q r : ZMod p) := by
    have htin : ∀ s : ℕ, (∑ t ∈ range p, (S r s t : ZMod p))
        = ∑ t ∈ range (r + 1), (S r s t : ZMod p) := by
      intro s
      symm
      apply Finset.sum_subset (hsub _ _ (by omega : r + 1 ≤ p))
      intro t _ ht
      simp only [Finset.mem_range, not_lt] at ht
      have hz : Nat.choose r t = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [S, hz]
    simp_rw [htin]
    rw [Q_eq r]; push_cast
    symm
    apply Finset.sum_subset (hsub _ _ (by omega : r + 1 ≤ p))
    intro s _ hs
    simp only [Finset.mem_range, not_lt] at hs
    apply Finset.sum_eq_zero
    intro t _
    have hz : Nat.choose r s = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [S, hz]
  -- Extension bound.
  have hNM : (a * p + r) + 1 ≤ (a + 1) * p := by
    have haux : (a + 1) * p = a * p + p := by ring
    omega
  -- Extend the inner `l`-sum to `range ((a+1)*p)` (added terms vanish: `choose N l = 0`).
  have hIn : ∀ k : ℕ, (∑ l ∈ range ((a * p + r) + 1), (S (a * p + r) k l : ZMod p))
      = ∑ l ∈ range ((a + 1) * p), (S (a * p + r) k l : ZMod p) := by
    intro k
    apply Finset.sum_subset (hsub _ _ hNM)
    intro l _ hl
    simp only [Finset.mem_range, not_lt] at hl
    have hz : Nat.choose (a * p + r) l = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [S, hz]
  -- Extend the outer `k`-sum (added terms vanish: `choose N k = 0`).
  have hOut : (∑ k ∈ range ((a * p + r) + 1), ∑ l ∈ range ((a + 1) * p),
        (S (a * p + r) k l : ZMod p))
      = ∑ k ∈ range ((a + 1) * p), ∑ l ∈ range ((a + 1) * p), (S (a * p + r) k l : ZMod p) := by
    apply Finset.sum_subset (hsub _ _ hNM)
    intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    apply Finset.sum_eq_zero
    intro l _
    have hz : Nat.choose (a * p + r) k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [S, hz]
  -- Assemble.
  rw [Q_eq (a * p + r)]
  push_cast
  calc ∑ k ∈ range ((a * p + r) + 1), ∑ l ∈ range ((a * p + r) + 1),
          (S (a * p + r) k l : ZMod p)
      = ∑ k ∈ range ((a * p + r) + 1), ∑ l ∈ range ((a + 1) * p),
          (S (a * p + r) k l : ZMod p) := by
        exact Finset.sum_congr rfl (fun k _ => hIn k)
    _ = ∑ k ∈ range ((a + 1) * p), ∑ l ∈ range ((a + 1) * p),
          (S (a * p + r) k l : ZMod p) := hOut
    _ = ∑ b ∈ range (a + 1), ∑ s ∈ range p, ∑ l ∈ range ((a + 1) * p),
          (S (a * p + r) (b * p + s) l : ZMod p) :=
        REIDX (fun k => ∑ l ∈ range ((a + 1) * p), (S (a * p + r) k l : ZMod p))
    _ = ∑ b ∈ range (a + 1), ∑ s ∈ range p, ∑ c ∈ range (a + 1), ∑ t ∈ range p,
          (S (a * p + r) (b * p + s) (c * p + t) : ZMod p) := by
        refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun s _ => ?_))
        exact REIDX (fun l => (S (a * p + r) (b * p + s) l : ZMod p))
    _ = ∑ b ∈ range (a + 1), ∑ s ∈ range p, ∑ c ∈ range (a + 1), ∑ t ∈ range p,
          (S a b c : ZMod p) * (S r s t : ZMod p) := by
        refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun s hs =>
          Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun t ht => ?_))))
        exact POINT b s c t (Finset.mem_range.mp hs) (Finset.mem_range.mp ht)
    _ = (∑ b ∈ range (a + 1), ∑ c ∈ range (a + 1), (S a b c : ZMod p))
          * (∑ s ∈ range p, ∑ t ∈ range p, (S r s t : ZMod p)) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun s _ => ?_))
        exact (Finset.sum_mul_sum _ _ _ _).symm
    _ = (Q a : ZMod p) * (Q r : ZMod p) := by rw [hiEq, loEq]

end Cbcert.LucasRow
