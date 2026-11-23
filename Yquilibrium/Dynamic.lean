/-
  Yquilibrium (Goeree, 21 Nov 2026), Definition 4 (stochastic dynamic) and Theorem 4,
  part 1: the pathwise properties (invariance, individual rationality, feasibility, barter).
  These hold for every sequence of draws, not just almost surely.
-/
import Yquilibrium.Duality

open Finset Set

noncomputable section

namespace Yq

namespace Economy

variable {K N : Type*} [Fintype K] [Fintype N] (E : Economy N K)

/-- Theorem 4's assumptions on utilities used here: `u` represents the preferences, is
  continuous, and is strictly quasiconcave. -/
structure DynRep (E : Economy N K) (u : N → (K → ℝ) → ℝ) : Prop where
  rep : ∀ i z x, 0 ≤ z → 0 ≤ x → ((E.pref i).R z x ↔ u i x ≤ u i z)
  cont : ∀ i, ContinuousOn (u i) {z | 0 ≤ z}
  sqc : ∀ i (x y : K → ℝ), 0 ≤ x → 0 ≤ y → x ≠ y → ∀ a : ℝ, 0 < a → a < 1 →
    min (u i x) (u i y) < u i (a • x + (1 - a) • y)

variable {E} {u : N → (K → ℝ) → ℝ}

lemma DynRep.qc (hu : E.DynRep u) (i : N) {x y : K → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : min (u i x) (u i y) ≤ u i (a • x + (1 - a) • y) := by
  by_cases hxy : x = y
  · subst hxy
    rw [← add_smul, add_sub_cancel, one_smul, min_self]
  rcases ha0.lt_or_eq with ha0' | ha0'
  · rcases ha1.lt_or_eq with ha1' | ha1'
    · exact (hu.sqc i x y hx hy hxy a ha0' ha1').le
    · rw [ha1', sub_self, zero_smul, add_zero, one_smul]
      exact min_le_left _ _
  · rw [← ha0', zero_smul, zero_add, sub_zero, one_smul]
    exact min_le_right _ _

/-! ### Demand -/

lemma optimal_exists (hu : E.DynRep u) (i : N) {p : K → ℝ} (hp : ∀ k, 0 < p k) {m : ℝ}
    (hm : 0 ≤ m) : ∃ z, Optimal (E.pref i) p m z := by
  obtain ⟨zs, ⟨hzs0, hzsm⟩, -, hmax⟩ := vind_attained (hu.cont i) hp hm
  exact ⟨zs, hzs0, hzsm, fun z hz hzm => (hu.rep i zs z hzs0 hz).2 (hmax z hz hzm)⟩

/-- Under strict quasiconcavity the optimal bundle is unique. -/
lemma optimal_unique (hu : E.DynRep u) (i : N) {p : K → ℝ} {m : ℝ} {z z' : K → ℝ}
    (h : Optimal (E.pref i) p m z) (h' : Optimal (E.pref i) p m z') : z = z' := by
  by_contra hne
  obtain ⟨hz0, hzm, hopt⟩ := h
  obtain ⟨hz0', hzm', hopt'⟩ := h'
  have hw0 : 0 ≤ (1 / 2 : ℝ) • z + (1 - 1 / 2 : ℝ) • z' := fun k => by
    simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hz0 k
    have := hz0' k
    simp only [Pi.zero_apply] at *
    linarith
  have hwm : dot p ((1 / 2 : ℝ) • z + (1 - 1 / 2 : ℝ) • z') ≤ m := by
    simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hzm hzm' ⊢
    have : ∑ k, p k * (1 / 2 * z k + (1 - 1 / 2) * z' k) =
        1 / 2 * ∑ k, p k * z k + 1 / 2 * ∑ k, p k * z' k := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    linarith
  have h1 := (hu.rep i z z' hz0 hz0').1 (hopt z' hz0' hzm')
  have h2 := (hu.rep i z' z hz0' hz0).1 (hopt' z hz0 hzm)
  have h3 := (hu.rep i z _ hz0 hw0).1 (hopt _ hw0 hwm)
  have h4 := hu.sqc i z z' hz0 hz0' hne (1 / 2) (by norm_num) (by norm_num)
  rw [min_eq_right h1] at h4
  linarith

/-- Consumer `i`'s demand `dᵢ(p,m)` (well defined for `p ≫ 0`, `m ≥ 0`). -/
def demand (E : Economy N K) (i : N) (p : K → ℝ) (m : ℝ) : K → ℝ :=
  Classical.epsilon fun z => Optimal (E.pref i) p m z

lemma demand_spec (hu : E.DynRep u) (i : N) {p : K → ℝ} (hp : ∀ k, 0 < p k) {m : ℝ}
    (hm : 0 ≤ m) : Optimal (E.pref i) p m (E.demand i p m) :=
  Classical.epsilon_spec (optimal_exists hu i hp hm)

/-! ### One period of trade -/

/-- The random inputs of one period: proposer, price, trade size, and the order in which the
  other consumers are asked. -/
structure Draw (N K : Type*) where
  P : N
  p : K → ℝ
  Δ : ℝ
  order : List N

/-- A draw is admissible if the price is strictly positive and normalized, and `0 < Δ ≤ 1`. -/
def Draw.Valid (E : Economy N K) (ω : Draw N K) : Prop :=
  (∀ k, 0 < ω.p k) ∧ dot ω.p E.W = 1 ∧ 0 < ω.Δ ∧ ω.Δ ≤ 1

/-- The proposer's excess demand `z_P(p) = d_P(p, ⟨p|x_P⟩) − x_P`. -/
def excess (E : Economy N K) (x : N → K → ℝ) (ω : Draw N K) : K → ℝ :=
  E.demand ω.P ω.p (dot ω.p (x ω.P)) - x ω.P

open Classical in
/-- Consumer `j` accepts the order iff `j ≠ P`, its bundle stays non-negative, and the trade
  strictly increases its utility. -/
def Accepts (E : Economy N K) (x : N → K → ℝ) (ω : Draw N K) (j : N) : Bool :=
  decide (j ≠ ω.P ∧ 0 ≤ x j - ω.Δ • E.excess x ω ∧
    ¬ (E.pref j).R (x j) (x j - ω.Δ • E.excess x ω))

/-- The responder: the first consumer in the order who accepts. -/
def responder (E : Economy N K) (x : N → K → ℝ) (ω : Draw N K) : Option N :=
  ω.order.find? (E.Accepts x ω)

variable [DecidableEq N]

/-- One period of the stochastic dynamic (Definition 4). -/
def step (E : Economy N K) (x : N → K → ℝ) (ω : Draw N K) : N → K → ℝ :=
  match E.responder x ω with
  | none => x
  | some r => Function.update (Function.update x ω.P (x ω.P + ω.Δ • E.excess x ω)) r
      (x r - ω.Δ • E.excess x ω)

/-- The path of the dynamic from the endowments, for a sequence of draws. -/
def path (E : Economy N K) (ω : ℕ → Draw N K) : ℕ → N → K → ℝ
  | 0 => E.ω
  | t + 1 => E.step (E.path ω t) (ω t)

/-- States that use exactly the resources `W`. -/
def Exact (E : Economy N K) (x : N → K → ℝ) : Prop := (∀ i, 0 ≤ x i) ∧ ∀ k, ∑ i, x i k = E.W k

lemma responder_spec {x : N → K → ℝ} {ω : Draw N K} {r : N} (h : E.responder x ω = some r) :
    r ≠ ω.P ∧ 0 ≤ x r - ω.Δ • E.excess x ω ∧
      ¬ (E.pref r).R (x r) (x r - ω.Δ • E.excess x ω) := by
  have := List.find?_some h
  simpa [Accepts] using this

/-! ### The four pathwise properties -/

/-- **Barter**: the proposer's excess demand has zero value at the drawn price, so the goods
  exchanged have equal value at the common price `p_t`. -/
theorem barter (hu : E.DynRep u) {x : N → K → ℝ} (hx : ∀ i, 0 ≤ x i) {ω : Draw N K}
    (hω : ω.Valid E) : dot ω.p (E.excess x ω) = 0 := by
  have hm := dot_nonneg (fun k => (hω.1 k).le) (hx ω.P)
  have hd := demand_spec hu ω.P hω.1 hm
  have h := (optimal_mu (fun k => (hω.1 k).le) hd).2
  simp only [excess, dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at h ⊢
  rw [h, sub_self]

/-- The proposer's new bundle `(1−Δ) x_P + Δ d_P`. -/
lemma proposer_bundle (x : N → K → ℝ) (ω : Draw N K) :
    x ω.P + ω.Δ • E.excess x ω =
      ω.Δ • E.demand ω.P ω.p (dot ω.p (x ω.P)) + (1 - ω.Δ) • x ω.P := by
  simp only [excess, smul_sub, sub_smul, one_smul]
  abel

/-- **Feasibility**: a period of trade keeps bundles non-negative and aggregate holdings
  unchanged. -/
theorem step_exact (hu : E.DynRep u) {x : N → K → ℝ} (hx : E.Exact x) {ω : Draw N K}
    (hω : ω.Valid E) : E.Exact (E.step x ω) := by
  have hm := dot_nonneg (fun k => (hω.1 k).le) (hx.1 ω.P)
  have hd := (demand_spec hu ω.P hω.1 hm).1
  unfold step
  split
  · exact hx
  · rename_i r hr
    obtain ⟨hrP, hr0, -⟩ := responder_spec hr
    refine ⟨fun i => ?_, fun k => ?_⟩
    · by_cases hir : i = r
      · subst hir
        rw [Function.update_self]
        exact hr0
      · rw [Function.update_of_ne hir]
        by_cases hiP : i = ω.P
        · subst hiP
          rw [Function.update_self, proposer_bundle]
          intro k
          simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          exact add_nonneg (mul_nonneg hω.2.2.1.le (hd k))
            (mul_nonneg (by linarith [hω.2.2.2]) (hx.1 _ k))
        · rw [Function.update_of_ne hiP]
          exact hx.1 i
    · rw [← hx.2 k]
      have hsplit : ∀ y : N → K → ℝ, ∑ i, y i k = y r k + y ω.P k +
          ∑ i ∈ (univ.erase r).erase ω.P, y i k := by
        intro y
        rw [← Finset.add_sum_erase _ _ (mem_univ r),
          ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hrP.symm, mem_univ ω.P⟩)]
        ring
      rw [hsplit, hsplit x]
      have hrest : ∑ i ∈ (univ.erase r).erase ω.P,
          Function.update (Function.update x ω.P (x ω.P + ω.Δ • E.excess x ω)) r
            (x r - ω.Δ • E.excess x ω) i k = ∑ i ∈ (univ.erase r).erase ω.P, x i k :=
        Finset.sum_congr rfl fun i hi => by
          have hiP := Finset.ne_of_mem_erase hi
          have hir := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
          rw [Function.update_of_ne hir, Function.update_of_ne hiP]
      rw [hrest, Function.update_self, Function.update_of_ne hrP.symm, Function.update_self]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring

/-- **Individual rationality (one period)**: nobody is worse off after a period of trade; the
  responder is strictly better off and the proposer weakly. -/
theorem step_improves (hu : E.DynRep u) {x : N → K → ℝ} (hx : ∀ i, 0 ≤ x i) {ω : Draw N K}
    (hω : ω.Valid E) (i : N) : u i (x i) ≤ u i (E.step x ω i) := by
  have hm := dot_nonneg (fun k => (hω.1 k).le) (hx ω.P)
  have hd := demand_spec hu ω.P hω.1 hm
  rcases hr : E.responder x ω with _ | r
  · simp only [step, hr]
    exact le_rfl
  · simp only [step, hr]
    obtain ⟨hrP, hr0, hstrict⟩ := responder_spec hr
    by_cases hir : i = r
    · subst hir
      rw [Function.update_self]
      exact le_of_lt (lt_of_not_ge fun h => hstrict ((hu.rep i (x i) _ (hx i) hr0).2 h))
    · rw [Function.update_of_ne hir]
      by_cases hiP : i = ω.P
      · subst hiP
        rw [Function.update_self, proposer_bundle]
        -- u(d_P) ≥ u(x_P), since x_P is affordable at its own value
        have hdx : u ω.P (x ω.P) ≤ u ω.P (E.demand ω.P ω.p (dot ω.p (x ω.P))) :=
          (hu.rep ω.P _ (x ω.P) hd.1 (hx ω.P)).1 (hd.2.2 (x ω.P) (hx ω.P) le_rfl)
        have := hu.qc ω.P hd.1 (hx ω.P) hω.2.2.1.le hω.2.2.2
        rw [min_eq_right hdx] at this
        exact this
      · rw [Function.update_of_ne hiP]

/-- **Feasibility along the path.** -/
theorem path_exact (hu : E.DynRep u) (ω : ℕ → Draw N K) (hω : ∀ t, (ω t).Valid E) :
    ∀ t, E.Exact (E.path ω t)
  | 0 => ⟨E.ω_nonneg, fun _ => rfl⟩
  | t + 1 => step_exact hu (path_exact hu ω hω t) (hω t)

/-- **Utilities never fall along the path.** -/
theorem path_monotone (hu : E.DynRep u) (ω : ℕ → Draw N K) (hω : ∀ t, (ω t).Valid E)
    (i : N) : Monotone fun t => u i (E.path ω t i) :=
  monotone_nat_of_le_succ fun t =>
    step_improves hu (path_exact hu ω hω t).1 (hω t) i

/-- **Individual rationality along the path**: every consumer is always at least as well off
  as at the endowment. -/
theorem path_IR (hu : E.DynRep u) (ω : ℕ → Draw N K) (hω : ∀ t, (ω t).Valid E) (t : ℕ) :
    E.IR (E.path ω t) := fun i =>
  (hu.rep i _ _ ((path_exact hu ω hω t).1 i) (E.ω_nonneg i)).2
    (path_monotone hu ω hω i (Nat.zero_le t))

/-- **Invariance**: the dynamic is defined from preferences alone, so a strictly increasing
  transformation of the utilities represents the same preferences and leaves every assumption,
  and the process itself, unchanged. -/
theorem invariance (hu : E.DynRep u) (φ : N → ℝ → ℝ) (hφ : ∀ i, StrictMono (φ i))
    (hφc : ∀ i, Continuous (φ i)) : E.DynRep fun i z => φ i (u i z) where
  rep i z x hz hx := (hu.rep i z x hz hx).trans (hφ i).le_iff_le.symm
  cont i := (hφc i).comp_continuousOn (hu.cont i)
  sqc i x y hx hy hxy a ha0 ha1 := by
    have h := hu.sqc i x y hx hy hxy a ha0 ha1
    rw [← (hφ i).monotone.map_min]
    exact hφ i h

end Economy

end Yq
