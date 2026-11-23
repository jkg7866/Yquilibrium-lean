/-
  Yquilibrium (Goeree, 21 Nov 2026), Proposition 1: the non-convex replica economy with
  n buyers (a = 3/5, ω = (25,45)) and n sellers (a = 9/20, ω = (75,55)), CES with ρ = 5/2.
  Prices enter through the ratio r = p₀/(p₀+p₁) (the paper's p).
-/
import Yquilibrium.CES2

open Finset Set

noncomputable section

namespace Yq

lemma sum_dot_eq' {K N : Type*} [Fintype K] [Fintype N] (p : K → ℝ) (x : N → K → ℝ) :
    ∑ i, dot p (x i) = ∑ k, p k * ∑ i, x i k := by
  simp only [dot, Finset.mul_sum]
  exact Finset.sum_comm

namespace Economy

variable {K N : Type*} [Fintype K] [Fintype N] (E : Economy N K)

/-- Lemma 3, in the form used below. -/
theorem root_iff_optimal [Nonempty N] [Nonempty K] {x : N → K → ℝ} {p : K → ℝ} :
    E.IsRoot x p ↔ E.Feasible x ∧ p ∈ E.Prices ∧ (∀ k, 0 < p k) ∧
      (∀ i, Optimal (E.pref i) p (dot p (x i)) (x i)) ∧ ∑ i, dot p (x i) = 1 := by
  constructor
  · intro h
    obtain ⟨m, hm, hW⟩ := E.root_iff.1 h
    have hinc := E.walrasianFor_income hW
    refine ⟨hW.1, hW.2.1, (E.root_pos_pareto h).1, fun i => ?_, ?_⟩
    · rw [hinc i]
      exact hW.2.2 i
    · rw [Finset.sum_congr rfl fun i _ => hinc i]
      exact hm.2
  · rintro ⟨hx, hp, hpos, hopt, hs⟩
    exact E.root_iff.2 ⟨fun i => dot p (x i), ⟨fun i => dot_nonneg hp.1 (hx.1 i), hs⟩, hx, hp,
      hopt⟩

/-- At a root, markets clear exactly. -/
theorem root_clears {x : N → K → ℝ} {p : K → ℝ} (hx : E.Feasible x) (hp : p ∈ E.Prices)
    (hpos : ∀ k, 0 < p k) (hs : ∑ i, dot p (x i) = 1) : ∀ k, ∑ i, x i k = E.W k := by
  have h1 : ∑ k, p k * (E.W k - ∑ i, x i k) = 0 := by
    have h2 : dot p E.W = 1 := hp.2
    simp only [dot] at h2
    rw [sum_dot_eq'] at hs
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ p k * (E.W k - ∑ i, x i k) :=
    fun k _ => mul_nonneg (hpos k).le (sub_nonneg.2 (hx.2 k))
  intro k
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1 k (mem_univ k)
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (hpos k).ne'
  · linarith

end Economy

/-! ### The replica economy -/

variable (n : ℕ)

/-- Share parameters: buyers `3/5`, sellers `9/20`. -/
def aOf : Fin n ⊕ Fin n → ℝ := Sum.elim (fun _ => 3 / 5) (fun _ => 9 / 20)

lemma aOf_pos (i : Fin n ⊕ Fin n) : 0 < aOf n i := by
  cases i <;> simp [aOf] <;> norm_num

lemma aOf_lt (i : Fin n ⊕ Fin n) : aOf n i < 1 := by
  cases i <;> simp [aOf] <;> norm_num

/-- Endowments: buyers `(25,45)`, sellers `(75,55)`. -/
def ωOf : Fin n ⊕ Fin n → Fin 2 → ℝ := Sum.elim (fun _ => ![25, 45]) (fun _ => ![75, 55])

/-- The non-convex replica economy with `n` buyers and `n` sellers. -/
def replica : Economy (Fin n ⊕ Fin n) (Fin 2) where
  pref i := cesPref (aOf n i) (5 / 2) (aOf_pos n i) (aOf_lt n i) (by norm_num)
  ω := ωOf n
  ω_pos := by rintro (j | j) k <;> fin_cases k <;> simp [ωOf]

instance [NeZero n] : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl 0⟩

lemma replica_W (k : Fin 2) : (replica n).W k = 100 * n := by
  simp only [Economy.W, replica, ωOf, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  fin_cases k <;> simp <;> ring

lemma replica_R (i : Fin n ⊕ Fin n) (z x : Fin 2 → ℝ) :
    ((replica n).pref i).R z x ↔ ces (aOf n i) (5 / 2) x ≤ ces (aOf n i) (5 / 2) z := Iff.rfl

lemma replica_opt_iff (i : Fin n ⊕ Fin n) {p : Fin 2 → ℝ} (hp : ∀ k, 0 < p k) {m : ℝ}
    (hm : 0 ≤ m) {z : Fin 2 → ℝ} :
    Optimal ((replica n).pref i) p m z ↔
      0 ≤ z ∧ dot p z = m ∧ (z 0 = 0 ∨ z 1 = 0) ∧
        (0 < z 0 → (1 - aOf n i) * p 0 ≤ aOf n i * p 1) ∧
        (0 < z 1 → aOf n i * p 1 ≤ (1 - aOf n i) * p 0) :=
  ces_optimal_iff (aOf_pos n i) (aOf_lt n i) (by norm_num) hp hm

variable {n}

/-- Roots of the replica economy: strictly positive prices, exact market clearing, and every
  consumer holding a single good, the one it prefers at the price ratio. -/
theorem replica_root_iff [NeZero n] {x : Fin n ⊕ Fin n → Fin 2 → ℝ} {p : Fin 2 → ℝ} :
    (replica n).IsRoot x p ↔ p ∈ (replica n).Prices ∧ (∀ k, 0 < p k) ∧
      (∀ k, ∑ i, x i k = 100 * n) ∧ ∀ i, 0 ≤ x i ∧ (x i 0 = 0 ∨ x i 1 = 0) ∧
        (0 < x i 0 → (1 - aOf n i) * p 0 ≤ aOf n i * p 1) ∧
        (0 < x i 1 → aOf n i * p 1 ≤ (1 - aOf n i) * p 0) := by
  rw [Economy.root_iff_optimal]
  constructor
  · rintro ⟨hx, hp, hpos, hopt, hs⟩
    refine ⟨hp, hpos, fun k => ?_, fun i => ?_⟩
    · rw [(replica n).root_clears hx hp hpos hs k, replica_W]
    · obtain ⟨h0, -, h1, h2, h3⟩ :=
        (replica_opt_iff n i hpos (dot_nonneg hp.1 (hx.1 i))).1 (hopt i)
      exact ⟨h0, h1, h2, h3⟩
  · rintro ⟨hp, hpos, hclear, hi⟩
    have hx : (replica n).Feasible x :=
      ⟨fun i => (hi i).1, fun k => by rw [hclear k, replica_W]⟩
    refine ⟨hx, hp, hpos, fun i => ?_, ?_⟩
    · obtain ⟨h0, h1, h2, h3⟩ := hi i
      exact (replica_opt_iff n i hpos (dot_nonneg hp.1 h0)).2 ⟨h0, rfl, h1, h2, h3⟩
    · rw [sum_dot_eq']
      have h := hp.2
      simp only [dot] at h
      rw [← h]
      exact Finset.sum_congr rfl fun k _ => by rw [hclear k, replica_W]

/-- At a root the price ratio lies in `[9/20, 3/5]`. -/
lemma replica_root_range [NeZero n] {x : Fin n ⊕ Fin n → Fin 2 → ℝ} {p : Fin 2 → ℝ}
    (h : (replica n).IsRoot x p) : 9 * p 1 ≤ 11 * p 0 ∧ 2 * p 0 ≤ 3 * p 1 := by
  obtain ⟨-, hpos, hclear, hi⟩ := replica_root_iff.1 h
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (NeZero.pos n)
  have hex : ∀ k, ∃ i, 0 < x i k := by
    intro k
    by_contra hc
    push_neg at hc
    have : ∑ i, x i k ≤ 0 := Finset.sum_nonpos fun i _ => hc i
    rw [hclear k] at this
    linarith
  obtain ⟨i0, hi0⟩ := hex 0
  obtain ⟨i1, hi1⟩ := hex 1
  have hp0 := hpos 0
  have hp1 := hpos 1
  constructor
  · have := (hi i1).2.2.2 hi1
    cases i1 <;> simp [aOf] at this <;> linarith
  · have := (hi i0).2.2.1 hi0
    cases i0 <;> simp [aOf] at this <;> linarith

/-- The allocation in which buyers hold all `x` and sellers all `y`, at equal prices. -/
def xStar (n : ℕ) : Fin n ⊕ Fin n → Fin 2 → ℝ := Sum.elim (fun _ => ![100, 0]) (fun _ => ![0, 100])

/-- Equal prices, normalized to `⟨p|W⟩ = 1`. -/
def pStar (n : ℕ) : Fin 2 → ℝ := fun _ => 1 / (200 * n)

lemma xStar_root [NeZero n] : (replica n).IsRoot (xStar n) (pStar n) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (NeZero.pos n)
  have hps : ∀ k, 0 < pStar n k := fun k => by simp only [pStar]; positivity
  rw [replica_root_iff]
  refine ⟨⟨fun k => (hps k).le, ?_⟩, hps, fun k => ?_, ?_⟩
  · rw [dot_two, replica_W, replica_W]
    simp only [pStar]
    field_simp
    ring
  · simp only [xStar, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    fin_cases k <;> simp <;> ring
  · have hq : (0 : ℝ) < 1 / (200 * n) := by positivity
    rintro (j | j)
    · refine ⟨fun k => ?_, Or.inr (by simp [xStar]), fun _ => ?_, fun h => ?_⟩
      · fin_cases k <;> simp [xStar]
      · simp only [aOf, Sum.elim_inl, pStar]
        nlinarith
      · simp [xStar] at h
    · refine ⟨fun k => ?_, Or.inl (by simp [xStar]), fun h => ?_, fun _ => ?_⟩
      · fin_cases k <;> simp [xStar]
      · simp [xStar] at h
      · simp only [aOf, Sum.elim_inr, pStar]
        nlinarith

/-- The potential is non-negative and vanishes at `(xStar, pStar)`, so Yquilibria are roots. -/
lemma replica_isYq_root [NeZero n] {x : Fin n ⊕ Fin n → Fin 2 → ℝ} {p : Fin 2 → ℝ}
    (h : (replica n).IsYq x p) : (replica n).IsRoot x p := by
  obtain ⟨hx, hp, hmin⟩ := h
  have hs := xStar_root (n := n)
  have h1 := hmin (xStar n) (pStar n) hs.1 hs.2.1
  rw [hs.2.2] at h1
  exact ⟨hx, hp, le_antisymm h1 ((replica n).Y_nonneg hx hp)⟩

/-- **Proposition 1(a)**: every Yquilibrium is a root of the potential, no consumer holds both
  goods, and the price ratio lies in `[9/20, 3/5]`. -/
theorem prop1_a [NeZero n] {x : Fin n ⊕ Fin n → Fin 2 → ℝ} {p : Fin 2 → ℝ}
    (h : (replica n).IsYq x p) :
    (replica n).IsRoot x p ∧ (∀ i, x i 0 = 0 ∨ x i 1 = 0) ∧
      9 / 20 ≤ p 0 / (p 0 + p 1) ∧ p 0 / (p 0 + p 1) ≤ 3 / 5 := by
  have hroot := replica_isYq_root h
  obtain ⟨-, hpos, -, hi⟩ := replica_root_iff.1 hroot
  obtain ⟨h1, h2⟩ := replica_root_range hroot
  have hp0 := hpos 0
  have hp1 := hpos 1
  refine ⟨hroot, fun i => (hi i).2.1, ?_, ?_⟩
  · rw [le_div_iff₀ (by linarith)]
    linarith
  · rw [div_le_iff₀ (by linarith)]
    linarith

/-! ### Individually rational Yquilibria -/

/-- Individual-rationality thresholds: a buyer holding only `x` (resp. `y`) needs at least
  `TxB` (resp. `TyB`); a seller needs `TxS` (resp. `TyS`). Approximately 36.5, 54.8, 94.0, 76.9. -/
def TxB : ℝ := ces (3 / 5) (5 / 2) ![25, 45] / (3 / 5)
def TyB : ℝ := ces (3 / 5) (5 / 2) ![25, 45] / (2 / 5)
def TxS : ℝ := ces (9 / 20) (5 / 2) ![75, 55] / (9 / 20)
def TyS : ℝ := ces (9 / 20) (5 / 2) ![75, 55] / (11 / 20)

lemma xStar_IR [NeZero n] : (replica n).IR (xStar n) := by
  obtain ⟨-, hB⟩ := uB_bounds
  obtain ⟨-, hS⟩ := uS_bounds
  rintro (j | j)
  · show ces (3 / 5) (5 / 2) ![25, 45] ≤ ces (3 / 5) (5 / 2) ![100, 0]
    rw [ces_x (z := ![100, 0]) (by norm_num) (by norm_num) (by simp) (by simp)]
    norm_num
    linarith
  · show ces (9 / 20) (5 / 2) ![75, 55] ≤ ces (9 / 20) (5 / 2) ![0, 100]
    rw [ces_y (z := ![0, 100]) (by norm_num) (by norm_num) (by simp) (by simp)]
    norm_num
    linarith

/-- `𝒴⁺` consists exactly of the individually-rational roots. -/
theorem prop1_IR_iff [NeZero n] {x : Fin n ⊕ Fin n → Fin 2 → ℝ} {p : Fin 2 → ℝ} :
    (replica n).IsYqIR x p ↔ (replica n).IsRoot x p ∧ (replica n).IR x := by
  constructor
  · rintro ⟨hx, hIR, hp, hmin⟩
    have hs := xStar_root (n := n)
    have h1 := hmin (xStar n) (pStar n) hs.1 xStar_IR hs.2.1
    rw [hs.2.2] at h1
    exact ⟨⟨hx, hp, le_antisymm h1 ((replica n).Y_nonneg hx hp)⟩, hIR⟩
  · rintro ⟨⟨hx, hp, hY⟩, hIR⟩
    exact ⟨hx, hIR, hp, fun x' p' hx' _ hp' => by rw [hY]; exact (replica n).Y_nonneg hx' hp'⟩

lemma IR_buyer {x : Fin n ⊕ Fin n → Fin 2 → ℝ} (hIR : (replica n).IR x) (j : Fin n)
    (h0 : 0 ≤ x (Sum.inl j)) :
    (x (Sum.inl j) 1 = 0 → TxB ≤ x (Sum.inl j) 0) ∧ (x (Sum.inl j) 0 = 0 → TyB ≤ x (Sum.inl j) 1) := by
  have h := hIR (Sum.inl j)
  change ces (3 / 5) (5 / 2) ![25, 45] ≤ ces (3 / 5) (5 / 2) (x (Sum.inl j)) at h
  constructor
  · intro hy
    rw [ces_x (by norm_num) (by norm_num) (h0 0) hy] at h
    rw [TxB, div_le_iff₀ (by norm_num)]
    linarith
  · intro hx
    rw [ces_y (by norm_num) (by norm_num) hx (h0 1)] at h
    rw [TyB, div_le_iff₀ (by norm_num)]
    linarith

lemma IR_seller {x : Fin n ⊕ Fin n → Fin 2 → ℝ} (hIR : (replica n).IR x) (j : Fin n)
    (h0 : 0 ≤ x (Sum.inr j)) :
    (x (Sum.inr j) 1 = 0 → TxS ≤ x (Sum.inr j) 0) ∧ (x (Sum.inr j) 0 = 0 → TyS ≤ x (Sum.inr j) 1) := by
  have h := hIR (Sum.inr j)
  change ces (9 / 20) (5 / 2) ![75, 55] ≤ ces (9 / 20) (5 / 2) (x (Sum.inr j)) at h
  constructor
  · intro hy
    rw [ces_x (by norm_num) (by norm_num) (h0 0) hy] at h
    rw [TxS, div_le_iff₀ (by norm_num)]
    linarith
  · intro hx
    rw [ces_y (by norm_num) (by norm_num) hx (h0 1)] at h
    rw [TyS, div_le_iff₀ (by norm_num)]
    linarith

/-- **Proposition 1(b)**: in an individually-rational Yquilibrium every consumer holds enough of
  a single good, and
  (i) for `9/20 < r < 3/5` buyers hold only `x` and sellers only `y`;
  (ii) for `r = 9/20` buyers hold only `x`, the `s` sellers holding `x` satisfy
       `n·TxB + s·TxS ≤ 100 n`, and `s ≥ 1` requires `n ≥ 2`;
  (iii) for `r = 3/5` sellers hold only `y`, the `b` buyers holding `y` satisfy
       `n·TyS + b·TyB ≤ 100 n`, and `b ≥ 1` requires `n ≥ 3`.
  (The converse is `prop1_IR_iff` with `replica_root_iff`.) -/
theorem prop1_b [NeZero n] {x : Fin n ⊕ Fin n → Fin 2 → ℝ} {p : Fin 2 → ℝ}
    (h : (replica n).IsYqIR x p) :
    (∀ j, (x (Sum.inl j) 1 = 0 ∧ TxB ≤ x (Sum.inl j) 0) ∨
      (x (Sum.inl j) 0 = 0 ∧ TyB ≤ x (Sum.inl j) 1)) ∧
    (∀ j, (x (Sum.inr j) 1 = 0 ∧ TxS ≤ x (Sum.inr j) 0) ∨
      (x (Sum.inr j) 0 = 0 ∧ TyS ≤ x (Sum.inr j) 1)) ∧
    (9 / 20 < p 0 / (p 0 + p 1) → p 0 / (p 0 + p 1) < 3 / 5 →
      (∀ j, x (Sum.inl j) 1 = 0) ∧ ∀ j, x (Sum.inr j) 0 = 0) ∧
    (p 0 / (p 0 + p 1) = 9 / 20 → (∀ j, x (Sum.inl j) 1 = 0) ∧
      (n : ℝ) * TxB + (#{j | 0 < x (Sum.inr j) 0} : ℝ) * TxS ≤ 100 * n ∧
      (1 ≤ #{j | 0 < x (Sum.inr j) 0} → 2 ≤ n)) ∧
    (p 0 / (p 0 + p 1) = 3 / 5 → (∀ j, x (Sum.inr j) 0 = 0) ∧
      (n : ℝ) * TyS + (#{j | 0 < x (Sum.inl j) 1} : ℝ) * TyB ≤ 100 * n ∧
      (1 ≤ #{j | 0 < x (Sum.inl j) 1} → 3 ≤ n)) := by
  obtain ⟨hroot, hIR⟩ := prop1_IR_iff.1 h
  obtain ⟨-, hpos, hclear, hi⟩ := replica_root_iff.1 hroot
  have hp0 := hpos 0
  have hp1 := hpos 1
  have hsum : 0 < p 0 + p 1 := by linarith
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.one_le
  obtain ⟨hB1, hB2⟩ := uB_bounds
  obtain ⟨hS1, hS2⟩ := uS_bounds
  have hTxB : 35 ≤ TxB := by rw [TxB, le_div_iff₀ (by norm_num)]; linarith
  have hTyB : 52 ≤ TyB := by rw [TyB, le_div_iff₀ (by norm_num)]; linarith
  have hTxS : 93 ≤ TxS := by rw [TxS, le_div_iff₀ (by norm_num)]; linarith
  have hTyS : 76 ≤ TyS := by rw [TyS, le_div_iff₀ (by norm_num)]; linarith
  -- buyers and sellers: a single good, enough of it
  have hbuy : ∀ j, (x (Sum.inl j) 1 = 0 ∧ TxB ≤ x (Sum.inl j) 0) ∨
      (x (Sum.inl j) 0 = 0 ∧ TyB ≤ x (Sum.inl j) 1) := fun j => by
    obtain ⟨h0, hs, -, -⟩ := hi (Sum.inl j)
    obtain ⟨hx, hy⟩ := IR_buyer hIR j h0
    rcases hs with hs | hs
    · exact Or.inr ⟨hs, hy hs⟩
    · exact Or.inl ⟨hs, hx hs⟩
  have hsell : ∀ j, (x (Sum.inr j) 1 = 0 ∧ TxS ≤ x (Sum.inr j) 0) ∨
      (x (Sum.inr j) 0 = 0 ∧ TyS ≤ x (Sum.inr j) 1) := fun j => by
    obtain ⟨h0, hs, -, -⟩ := hi (Sum.inr j)
    obtain ⟨hx, hy⟩ := IR_seller hIR j h0
    rcases hs with hs | hs
    · exact Or.inr ⟨hs, hy hs⟩
    · exact Or.inl ⟨hs, hx hs⟩
  -- price conditions in linear form
  have hcondB : ∀ j, (0 < x (Sum.inl j) 0 → 2 * p 0 ≤ 3 * p 1) ∧
      (0 < x (Sum.inl j) 1 → 3 * p 1 ≤ 2 * p 0) := fun j => by
    obtain ⟨-, -, h1, h2⟩ := hi (Sum.inl j)
    simp only [aOf, Sum.elim_inl] at h1 h2
    exact ⟨fun h => by have := h1 h; linarith, fun h => by have := h2 h; linarith⟩
  have hcondS : ∀ j, (0 < x (Sum.inr j) 0 → 11 * p 0 ≤ 9 * p 1) ∧
      (0 < x (Sum.inr j) 1 → 9 * p 1 ≤ 11 * p 0) := fun j => by
    obtain ⟨-, -, h1, h2⟩ := hi (Sum.inr j)
    simp only [aOf, Sum.elim_inr] at h1 h2
    exact ⟨fun h => by have := h1 h; linarith, fun h => by have := h2 h; linarith⟩
  have hnn : ∀ i k, 0 ≤ x i k := fun i k => (hi i).1 k
  have hzero : ∀ i k, ¬ 0 < x i k → x i k = 0 := fun i k h => le_antisymm (not_lt.1 h) (hnn i k)
  refine ⟨hbuy, hsell, ?_, ?_, ?_⟩
  · -- (i)
    intro hlo hhi
    rw [lt_div_iff₀ hsum] at hlo
    rw [div_lt_iff₀ hsum] at hhi
    exact ⟨fun j => hzero _ _ fun h => by have := (hcondB j).2 h; linarith,
      fun j => hzero _ _ fun h => by have := (hcondS j).1 h; linarith⟩
  · -- (ii)
    intro heq
    rw [div_eq_iff hsum.ne'] at heq
    have hB : ∀ j, x (Sum.inl j) 1 = 0 :=
      fun j => hzero _ _ fun h => by have := (hcondB j).2 h; linarith
    have hclear0 := hclear 0
    rw [Fintype.sum_sum_type] at hclear0
    have hbuyers : (n : ℝ) * TxB ≤ ∑ j, x (Sum.inl j) 0 := by
      have : ∑ _j : Fin n, TxB ≤ ∑ j, x (Sum.inl j) 0 := Finset.sum_le_sum fun j _ => by
        rcases hbuy j with h | h
        · exact h.2
        · exact absurd h.1 (by have := hB j; rw [this] at h; linarith [h.2])
      simpa using this
    have hsellers : (#{j | 0 < x (Sum.inr j) 0} : ℝ) * TxS ≤ ∑ j, x (Sum.inr j) 0 := by
      calc (#{j | 0 < x (Sum.inr j) 0} : ℝ) * TxS
          = ∑ j ∈ univ.filter (fun j => 0 < x (Sum.inr j) 0), TxS := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ j ∈ univ.filter (fun j => 0 < x (Sum.inr j) 0), x (Sum.inr j) 0 :=
            Finset.sum_le_sum fun j hj => by
              have hj' : 0 < x (Sum.inr j) 0 := (Finset.mem_filter.1 hj).2
              rcases hsell j with h | h
              · exact h.2
              · rw [h.1] at hj'
                exact absurd hj' (lt_irrefl _)
        _ ≤ ∑ j, x (Sum.inr j) 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun j _ _ => hnn _ _
    have hbound : (n : ℝ) * TxB + (#{j | 0 < x (Sum.inr j) 0} : ℝ) * TxS ≤ 100 * n := by
      linarith
    refine ⟨hB, hbound, fun hs => ?_⟩
    have hs' : (1 : ℝ) ≤ #{j | 0 < x (Sum.inr j) 0} := by exact_mod_cast hs
    by_contra hlt
    push_neg at hlt
    have hn1 : (n : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 hlt
    nlinarith
  · -- (iii)
    intro heq
    rw [div_eq_iff hsum.ne'] at heq
    have hS : ∀ j, x (Sum.inr j) 0 = 0 :=
      fun j => hzero _ _ fun h => by have := (hcondS j).1 h; linarith
    have hclear1 := hclear 1
    rw [Fintype.sum_sum_type] at hclear1
    have hsellers : (n : ℝ) * TyS ≤ ∑ j, x (Sum.inr j) 1 := by
      have : ∑ _j : Fin n, TyS ≤ ∑ j, x (Sum.inr j) 1 := Finset.sum_le_sum fun j _ => by
        rcases hsell j with h | h
        · exact absurd h.2 (by rw [hS j]; linarith)
        · exact h.2
      simpa using this
    have hbuyers : (#{j | 0 < x (Sum.inl j) 1} : ℝ) * TyB ≤ ∑ j, x (Sum.inl j) 1 := by
      calc (#{j | 0 < x (Sum.inl j) 1} : ℝ) * TyB
          = ∑ j ∈ univ.filter (fun j => 0 < x (Sum.inl j) 1), TyB := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ j ∈ univ.filter (fun j => 0 < x (Sum.inl j) 1), x (Sum.inl j) 1 :=
            Finset.sum_le_sum fun j hj => by
              have hj' : 0 < x (Sum.inl j) 1 := (Finset.mem_filter.1 hj).2
              rcases hbuy j with h | h
              · rw [h.1] at hj'
                exact absurd hj' (lt_irrefl _)
              · exact h.2
        _ ≤ ∑ j, x (Sum.inl j) 1 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun j _ _ => hnn _ _
    have hbound : (n : ℝ) * TyS + (#{j | 0 < x (Sum.inl j) 1} : ℝ) * TyB ≤ 100 * n := by
      linarith
    refine ⟨hS, hbound, fun hb => ?_⟩
    have hb' : (1 : ℝ) ≤ #{j | 0 < x (Sum.inl j) 1} := by exact_mod_cast hb
    by_contra hlt
    push_neg at hlt
    have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 hlt
    nlinarith

/-! ### Walrasian equilibria -/

/-- **Proposition 1(c)**, necessity: at a Walrasian equilibrium the price ratio is `9/20` and
  exactly `s = 9n/64` sellers hold `x`. -/
theorem prop1_c_nec [NeZero n] {x : Fin n ⊕ Fin n → Fin 2 → ℝ} {p : Fin 2 → ℝ}
    (h : (replica n).IsWalrasian x p) :
    p 0 / (p 0 + p 1) = 9 / 20 ∧ 64 * #{j | 0 < x (Sum.inr j) 0} = 9 * n := by
  have hroot := ((replica n).theorem2_b h).2.1
  obtain ⟨-, hpos, hclear, hi⟩ := replica_root_iff.1 hroot
  obtain ⟨hr1, hr2⟩ := replica_root_range hroot
  have hinc := (replica n).walrasianFor_income h
  have hp0 := hpos 0
  have hp1 := hpos 1
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.one_le
  have hnn : ∀ i k, 0 ≤ x i k := fun i k => (hi i).1 k
  have hzero : ∀ i k, ¬ 0 < x i k → x i k = 0 := fun i k h => le_antisymm (not_lt.1 h) (hnn i k)
  have hcondB : ∀ j, (0 < x (Sum.inl j) 1 → 3 * p 1 ≤ 2 * p 0) := fun j h => by
    have := (hi (Sum.inl j)).2.2.2 h
    simp only [aOf, Sum.elim_inl] at this
    linarith
  have hcondS : ∀ j, (0 < x (Sum.inr j) 0 → 11 * p 0 ≤ 9 * p 1) := fun j h => by
    have := (hi (Sum.inr j)).2.2.1 h
    simp only [aOf, Sum.elim_inr] at this
    linarith
  -- incomes
  have hincB : ∀ j, p 0 * x (Sum.inl j) 0 + p 1 * x (Sum.inl j) 1 = 25 * p 0 + 45 * p 1 :=
    fun j => by
      have := hinc (Sum.inl j)
      rw [dot_two, dot_two] at this
      simpa [replica, ωOf, mul_comm] using this
  have hincS : ∀ j, p 0 * x (Sum.inr j) 0 + p 1 * x (Sum.inr j) 1 = 75 * p 0 + 55 * p 1 :=
    fun j => by
      have := hinc (Sum.inr j)
      rw [dot_two, dot_two] at this
      simpa [replica, ωOf, mul_comm] using this
  have hclear0 := hclear 0
  rw [Fintype.sum_sum_type] at hclear0
  -- some seller holds x
  have hseller : ∃ j, 0 < x (Sum.inr j) 0 := by
    by_contra hc
    push_neg at hc
    have hS0 : ∑ j, x (Sum.inr j) 0 = 0 :=
      Finset.sum_eq_zero fun j _ => le_antisymm (hc j) (hnn _ _)
    have hB80 : ∀ j, x (Sum.inl j) 0 ≤ 80 := fun j => by
      have h1 := hincB j
      have h2 := mul_nonneg hp1.le (hnn (Sum.inl j) 1)
      nlinarith
    have : ∑ j, x (Sum.inl j) 0 ≤ ∑ _j : Fin n, (80 : ℝ) := Finset.sum_le_sum fun j _ => hB80 j
    simp at this
    linarith
  obtain ⟨j0, hj0⟩ := hseller
  have heq : 11 * p 0 = 9 * p 1 := le_antisymm (hcondS j0 hj0) hr1
  refine ⟨by rw [div_eq_iff (by linarith)]; linarith, ?_⟩
  -- buyers hold 80 units of x, x-holding sellers 1280/9
  have hB : ∀ j, x (Sum.inl j) 0 = 80 := fun j => by
    have hy : x (Sum.inl j) 1 = 0 := hzero _ _ fun h => by have := hcondB j h; linarith
    have := hincB j
    rw [hy] at this
    nlinarith
  have hS : ∀ j, x (Sum.inr j) 0 = if 0 < x (Sum.inr j) 0 then 1280 / 9 else 0 := fun j => by
    split_ifs with hpos'
    · rcases (hi (Sum.inr j)).2.1 with h0 | h1
      · rw [h0] at hpos'
        exact absurd hpos' (lt_irrefl _)
      · have := hincS j
        rw [h1] at this
        nlinarith
    · exact hzero _ _ hpos'
  rw [Finset.sum_congr rfl fun j _ => hB j, Finset.sum_congr rfl fun j _ => hS j,
    Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.sum_const_zero, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, add_zero] at hclear0
  have : ((64 * #{j | 0 < x (Sum.inr j) 0} : ℕ) : ℝ) = ((9 * n : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this

/-- **Proposition 1(c)**: Walrasian equilibria exist iff `n` is a multiple of 64. -/
theorem prop1_c [NeZero n] : (∃ x p, (replica n).IsWalrasian x p) ↔ 64 ∣ n := by
  constructor
  · rintro ⟨x, p, h⟩
    have h64 := (prop1_c_nec h).2
    have : 64 ∣ n * 9 := ⟨_, by rw [mul_comm n 9, ← h64]⟩
    exact Nat.Coprime.dvd_of_dvd_mul_right (by decide) this
  · rintro ⟨k, rfl⟩
    have hn : (0 : ℝ) < ((64 * k : ℕ) : ℝ) := Nat.cast_pos.2 (NeZero.pos _)
    have hk : (0 : ℝ) < k := by
      have : (0 : ℝ) < 64 * (k : ℝ) := by exact_mod_cast hn
      linarith
    set c : ℝ := 1 / (2000 * ((64 * k : ℕ) : ℝ)) with hc
    have hcpos : 0 < c := by positivity
    let p : Fin 2 → ℝ := fun i => if i = 0 then 9 * c else 11 * c
    have hp0 : p 0 = 9 * c := if_pos rfl
    have hp1 : p 1 = 11 * c := if_neg (by decide)
    let x : Fin (64 * k) ⊕ Fin (64 * k) → Fin 2 → ℝ := Sum.elim (fun _ => ![80, 0])
      (fun j => ![if (j : ℕ) < 9 * k then 1280 / 9 else 0, if (j : ℕ) < 9 * k then 0 else 1280 / 11])
    have hpos : ∀ i, 0 < p i := fun i => by
      fin_cases i
      · show 0 < p 0
        rw [hp0]
        positivity
      · show 0 < p 1
        rw [hp1]
        positivity
    have hcard : #{j : Fin (64 * k) | (j : ℕ) < 9 * k} = 9 * k := by
      rw [Fin.card_filter_val_lt]
      omega
    have hcard' : #{j : Fin (64 * k) | ¬ (j : ℕ) < 9 * k} = 55 * k := by
      have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (64 * k))))
        (fun j : Fin (64 * k) => (j : ℕ) < 9 * k)
      rw [hcard, Finset.card_univ, Fintype.card_fin] at this
      omega
    refine ⟨x, p, ⟨⟨fun i k' => ?_, fun k' => ?_⟩, ⟨fun i => (hpos i).le, ?_⟩, fun i => ?_⟩⟩
    · rcases i with j | j
      · fin_cases k' <;> simp [x]
      · fin_cases k' <;> simp only [x, Sum.elim_inr] <;> split_ifs <;> simp <;> norm_num
    · rw [replica_W]
      simp only [x, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      fin_cases k'
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite, Finset.sum_const_zero,
          add_zero, hcard]
        push_cast
        linarith
      · have hy : ∑ j : Fin (64 * k), (if (j : ℕ) < 9 * k then (0 : ℝ) else 1280 / 11) =
            ((55 * k : ℕ) : ℝ) * (1280 / 11) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, hcard',
            nsmul_eq_mul]
        simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_zero]
        rw [hy]
        simp
        push_cast
        linarith
    · rw [dot_two, replica_W, replica_W, hp0, hp1, hc]
      field_simp
      ring
    · have hm : 0 ≤ dot p ((replica (64 * k)).ω i) :=
        dot_nonneg (fun i => (hpos i).le) ((replica (64 * k)).ω_nonneg i)
      rw [replica_opt_iff (64 * k) i hpos hm]
      rcases i with j | j
      · refine ⟨fun k' => by fin_cases k' <;> simp [x], ?_, Or.inr (by simp [x]),
          fun _ => ?_, fun h => ?_⟩
        · simp only [dot_two, x, Sum.elim_inl, replica, ωOf, hp0, hp1]
          simp
          ring
        · simp only [aOf, Sum.elim_inl, hp0, hp1]
          nlinarith
        · simp [x] at h
      · by_cases hj : (j : ℕ) < 9 * k
        · refine ⟨fun k' => by fin_cases k' <;> simp [x, hj] <;> norm_num, ?_,
            Or.inr (by simp [x, hj]), fun _ => ?_, fun h => ?_⟩
          · simp only [dot_two, x, Sum.elim_inr, if_pos hj, replica, ωOf, hp0, hp1]
            simp
            ring
          · simp only [aOf, Sum.elim_inr, hp0, hp1]
            nlinarith
          · simp [x, hj] at h
        · refine ⟨fun k' => by fin_cases k' <;> simp [x, hj] <;> norm_num, ?_,
            Or.inl (by simp [x, hj]), fun h => ?_, fun _ => ?_⟩
          · simp only [dot_two, x, Sum.elim_inr, if_neg hj, replica, ωOf, hp0, hp1]
            simp
            ring
          · simp [x, hj] at h
          · simp only [aOf, Sum.elim_inr, hp0, hp1]
            nlinarith

end Yq
