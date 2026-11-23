/-
  Yquilibrium (Goeree, version of 23 Nov 2026), Appendix A.
  Corollary 1(b) (second welfare theorem): with convex preferences every Pareto-optimal
  allocation is part of a root.
-/
import Yquilibrium.Roots
import Yquilibrium.Imports2

open Finset Filter Topology Set

noncomputable section

namespace Yq

variable {K : Type*} [Fintype K]

/-- Convex preferences: upper contour sets are convex. -/
def Pref.IsConvex (P : Pref K) : Prop := ∀ y, 0 ≤ y → Convex ℝ {z | 0 ≤ z ∧ P.R z y}

/-- With convex preferences, strict upper contour sets are convex. -/
lemma Pref.convex_strict {P : Pref K} (hP : P.IsConvex) {x : K → ℝ} (hx : 0 ≤ x) :
    Convex ℝ {z | 0 ≤ z ∧ ¬ P.R x z} := by
  intro z hz z' hz' a b ha hb hab
  rcases P.total z z' hz.1 hz'.1 with h | h
  · have hm := hP z' hz'.1 ⟨hz.1, h⟩ ⟨hz'.1, P.refl hz'.1⟩ ha hb hab
    exact ⟨hm.1, P.strict_of_weak_strict hx hz'.1 hm.1 hm.2 hz'.2⟩
  · have hm := hP z hz.1 ⟨hz.1, P.refl hz.1⟩ ⟨hz'.1, h⟩ ha hb hab
    exact ⟨hm.1, P.strict_of_weak_strict hx hz.1 hm.1 hm.2 hz.2⟩

lemma dot_sum_right {N : Type*} [Fintype N] (p : K → ℝ) (z : N → K → ℝ) :
    dot p (∑ i, z i) = ∑ i, dot p (z i) := by
  simp only [dot, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

namespace Economy

variable {N : Type*} [Fintype N] (E : Economy N K)

/-- Weak Pareto optimality: no feasible allocation makes every consumer strictly better off. -/
def WeaklyParetoOptimal (x : N → K → ℝ) : Prop :=
  E.Feasible x ∧ ¬ ∃ x', E.Feasible x' ∧ ∀ i, ¬ (E.pref i).R (x i) (x' i)

/-- **Corollary 1(b)**, strengthened: with convex preferences every *weakly* Pareto-optimal
  allocation is part of a root `(x,p)` with `p ≫ 0`. -/
theorem corollary1_b_weak [Nonempty N] [Nonempty K] (hconv : ∀ i, (E.pref i).IsConvex)
    {x : N → K → ℝ} (hPO : E.WeaklyParetoOptimal x) :
    ∃ p, E.IsRoot x p ∧ (∀ k, 0 < p k) ∧ E.IsYqFor (fun i => dot p (x i)) x p := by
  classical
  obtain ⟨hxF, hnot⟩ := hPO
  -- Z = ∑ᵢ Pᵢˢ, the sum of strict upper contour sets
  set Z : Set (K → ℝ) := {s | ∃ z : N → K → ℝ,
    (∀ i, 0 ≤ z i ∧ ¬ (E.pref i).R (x i) (z i)) ∧ s = ∑ i, z i} with hZdef
  -- L = interior of {w ≤ W}
  set L : Set (K → ℝ) := {w | ∀ k, w k < E.W k} with hLdef
  have hZc : Convex ℝ Z := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩ a b ha hb hab
    refine ⟨fun i => a • z i + b • z' i,
      fun i => (E.pref i).convex_strict (hconv i) (hxF.1 i) (hz i) (hz' i) ha hb hab, ?_⟩
    simp [Finset.smul_sum, Finset.sum_add_distrib]
  have hLo : IsOpen L := by
    have : L = ⋂ k, {w : K → ℝ | w k < E.W k} := by ext w; simp [hLdef]
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_lt (continuous_apply k) continuous_const
  have hLc : Convex ℝ L := by
    intro w hw w' hw' a b ha hb hab
    have hw : ∀ k, w k < E.W k := hw
    have hw' : ∀ k, w' k < E.W k := hw'
    show ∀ k, (a • w + b • w') k < E.W k
    intro k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : a * w k ≤ a * E.W k := mul_le_mul_of_nonneg_left (hw k).le ha
    have h2 : b * w' k ≤ b * E.W k := mul_le_mul_of_nonneg_left (hw' k).le hb
    have hW : a * E.W k + b * E.W k = E.W k := by rw [← add_mul, hab, one_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · have : a * w k < a * E.W k := mul_lt_mul_of_pos_left (hw k) ha'
      linarith
    · have hb' : 0 < b := by linarith
      have : b * w' k < b * E.W k := mul_lt_mul_of_pos_left (hw' k) hb'
      linarith
  have hdisj : Disjoint L Z := by
    rw [Set.disjoint_left]
    rintro w hwL ⟨z, hz, rfl⟩
    have hwL : ∀ k, (∑ i, z i) k < E.W k := hwL
    apply hnot
    refine ⟨z, ⟨fun i => (hz i).1, fun k => ?_⟩, fun i => (hz i).2⟩
    have := (hwL k).le
    simpa [Finset.sum_apply] using this
  -- separating hyperplane
  obtain ⟨f, u, hfL, hfZ⟩ := geometric_hahn_banach_open hLc hLo hZc hdisj
  set q : K → ℝ := fun k => f (fun j => if k = j then 1 else 0) with hqdef
  have hf : ∀ w, f w = dot q w := by
    intro w
    have := LinearMap.pi_apply_eq_sum_univ (f : (K → ℝ) →ₗ[ℝ] ℝ) w
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this, dot]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  -- the bundle W - δ𝟏 - t eₖ lies in L
  have hσ_mem : ∀ δ > 0, ∀ t ≥ 0, ∀ k₀, (fun j => E.W j + (-δ) - (if j = k₀ then t else 0)) ∈ L := by
    intro δ hδ t ht k₀ j
    show E.W j + -δ - (if j = k₀ then t else 0) < E.W j
    split_ifs <;> linarith
  have hdotL : ∀ δ t k₀, dot q (fun j => E.W j + (-δ) - (if j = k₀ then t else 0)) =
      dot q E.W - δ * ∑ k, q k - q k₀ * t := by
    intro δ t k₀
    simp only [dot, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum]
    congr 1
    congr 1
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- q ≥ 0
  have hq0 : 0 ≤ q := by
    intro k₀
    show 0 ≤ q k₀
    by_contra hneg
    push_neg at hneg
    set c := dot q E.W - 1 * ∑ k, q k
    obtain ⟨t, htdef⟩ : ∃ t, t = max 0 ((u - c + 1) / (-q k₀)) := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := htdef ▸ le_max_left _ _
    have ht1 : (u - c + 1) / (-q k₀) ≤ t := htdef ▸ le_max_right _ _
    have ht2 : u - c + 1 ≤ t * (-q k₀) := by
      rwa [div_le_iff₀ (by linarith)] at ht1
    have h := hfL _ (hσ_mem 1 one_pos t ht0 k₀)
    rw [hf, hdotL] at h
    nlinarith
  have hσ : 0 ≤ ∑ k, q k := Finset.sum_nonneg fun k _ => hq0 k
  -- ⟨q|W⟩ ≤ u
  have hWu : dot q E.W ≤ u := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have h := hfL _ (hσ_mem (ε / (∑ k, q k + 1)) (by positivity) 0 le_rfl (Classical.arbitrary K))
    rw [hf, hdotL] at h
    have : ε / (∑ k, q k + 1) * ∑ k, q k ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  -- separation from Z
  have hZ : ∀ s ∈ Z, dot q E.W ≤ dot q s := fun s hs => by
    have := hfZ s hs
    rw [hf] at this
    linarith
  -- ⟨q|W⟩ > 0
  have hZne : (∑ i, fun k => x i k + 1) ∈ Z := by
    refine ⟨fun i => fun k => x i k + 1, fun i => ⟨fun k => ?_, ?_⟩, rfl⟩
    · have := hxF.1 i k
      simp only [Pi.zero_apply] at this ⊢
      linarith
    · exact (E.pref i).mono (x i) _ (hxF.1 i) fun k => by linarith
  have hqW : 0 < dot q E.W := by
    by_contra h
    push_neg at h
    have hqz : ∀ k, q k = 0 := by
      intro k
      have h1 := mul_le_dot hq0 E.W_nonneg k
      have h2 : q k * E.W k = 0 := le_antisymm (by linarith) (mul_nonneg (hq0 k) (E.W_nonneg k))
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact h3
      · exact absurd h3 (E.W_pos k).ne'
    have hdz : ∀ v, dot q v = 0 := fun v => by simp [dot, hqz]
    have h1 := hfL _ (hσ_mem 1 one_pos 0 le_rfl (Classical.arbitrary K))
    have h2 := hfZ _ hZne
    rw [hf, hdz] at h1 h2
    linarith
  -- normalize
  set p : K → ℝ := (dot q E.W)⁻¹ • q with hpdef
  have hp : p ∈ E.Prices := by
    refine ⟨fun k => ?_, ?_⟩
    · simp only [hpdef, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 hqW.le) (hq0 k)
    · rw [hpdef, dot_smul_left, inv_mul_cancel₀ hqW.ne']
  have hpZ : ∀ s ∈ Z, 1 ≤ dot p s := fun s hs => by
    rw [hpdef, dot_smul_left, ← div_eq_inv_mul, le_div_iff₀ hqW, one_mul]
    exact hZ s hs
  -- ∑ᵢ μᵢ(p, xᵢ) ≥ 1
  have hσp : 0 ≤ ∑ k, p k := Finset.sum_nonneg fun k _ => hp.1 k
  have hcardpos : (0 : ℝ) < Fintype.card N := by exact_mod_cast Fintype.card_pos
  have hsum : 1 ≤ ∑ i, mu (E.pref i) p (x i) := by
    apply le_of_forall_pos_le_add
    intro η hη
    have hη' : 0 < η / (2 * Fintype.card N) := by positivity
    choose z hz0 hzx hzc using fun i => exists_lt_of_mu_lt (P := E.pref i) (p := p) (hxF.1 i)
      (lt_add_of_pos_right (mu (E.pref i) p (x i)) hη')
    obtain ⟨ε, hεdef⟩ : ∃ ε, ε = η / (2 * Fintype.card N * (∑ k, p k + 1)) := ⟨_, rfl⟩
    have hε : 0 < ε := hεdef ▸ by positivity
    have hs : (∑ i, fun k => z i k + ε) ∈ Z := by
      refine ⟨fun i => fun k => z i k + ε, fun i => ⟨fun k => ?_, ?_⟩, rfl⟩
      · have := hz0 i k
        simp only [Pi.zero_apply] at this ⊢
        linarith
      · have hw0 : (0 : K → ℝ) ≤ fun k => z i k + ε := fun k => by
          have := hz0 i k
          simp only [Pi.zero_apply] at this ⊢
          linarith
        exact (E.pref i).strict_of_strict_weak (hxF.1 i) (hz0 i) hw0
          ((E.pref i).mono (z i) _ (hz0 i) fun k => by linarith) (hzx i)
    have h1 := hpZ _ hs
    rw [dot_sum_right, Finset.sum_congr rfl fun i _ => dot_add_const p (z i) ε,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    have h2 : ∑ i, dot p (z i) ≤ ∑ i, (mu (E.pref i) p (x i) + η / (2 * Fintype.card N)) :=
      Finset.sum_le_sum fun i _ => (hzc i).le
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    have h3 : (Fintype.card N : ℝ) * (η / (2 * Fintype.card N)) = η / 2 := by
      field_simp
    have hε2 : ε * (2 * Fintype.card N * (∑ k, p k + 1)) = η := by
      rw [hεdef]
      field_simp
    have h4 : (Fintype.card N : ℝ) * (ε * ∑ k, p k) ≤ (Fintype.card N : ℝ) * (ε * (∑ k, p k + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hε.le) hcardpos.le
    have h5 : (Fintype.card N : ℝ) * (ε * (∑ k, p k + 1)) = η / 2 := by linarith
    linarith
  -- (x,p) is a root
  have hY : E.Y x p = 0 := by
    have := E.Y_nonneg hxF hp
    simp only [Y] at this ⊢
    linarith
  have hroot : E.IsRoot x p := ⟨hxF, hp, hY⟩
  refine ⟨p, hroot, (E.root_pos_pareto hroot).1, ⟨hxF, hp, fun i => rfl⟩, ?_⟩
  intro x' p' h
  rw [hY]
  exact E.Y_nonneg h.1 h.2.1

/-- **Corollary 1(b)** (second welfare theorem): if preferences are convex, every
  Pareto-optimal allocation `x` is part of a root `(x,p)` with `p ≫ 0`, so `(x,p) ∈ 𝒴(m)` for
  `mᵢ = ⟨p|xᵢ⟩`. -/
theorem corollary1_b [Nonempty N] [Nonempty K] (hconv : ∀ i, (E.pref i).IsConvex)
    {x : N → K → ℝ} (hPO : E.ParetoOptimal x) :
    ∃ p, E.IsRoot x p ∧ (∀ k, 0 < p k) ∧ E.IsYqFor (fun i => dot p (x i)) x p :=
  E.corollary1_b_weak hconv ⟨hPO.1, fun ⟨x', hF, hs⟩ => hPO.2
    ⟨x', hF, fun i => (E.pref i).of_not (hPO.1.1 i) (hF.1 i) (hs i),
      Classical.arbitrary N, hs _⟩⟩

end Economy

end Yq
