/-
  Yquilibrium (Goeree, 21 Nov 2026), Remark 1: Debreu's coefficient of resource utilization
  and the dead loss.
-/
import Yquilibrium.Welfare2

open Finset Filter Topology Set

noncomputable section

namespace Yq

variable {K : Type*} [Fintype K]

/-- Separation of a convex set `S` from the open box `{w ≪ c}`: a non-negative, non-zero `q`
  with `⟨q|c⟩ ≤ ⟨q|s⟩` for all `s ∈ S`. -/
lemma separate_below [Nonempty K] {S : Set (K → ℝ)} (hS : Convex ℝ S) {s0 : K → ℝ}
    (hs0 : s0 ∈ S) (c : K → ℝ) (hdisj : ∀ s ∈ S, ¬ ∀ k, s k < c k) :
    ∃ q : K → ℝ, 0 ≤ q ∧ q ≠ 0 ∧ ∀ s ∈ S, dot q c ≤ dot q s := by
  classical
  set L : Set (K → ℝ) := {w | ∀ k, w k < c k} with hLdef
  have hLo : IsOpen L := by
    have : L = ⋂ k, {w : K → ℝ | w k < c k} := by ext w; simp [hLdef]
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_lt (continuous_apply k) continuous_const
  have hLc : Convex ℝ L := by
    intro w hw w' hw' a b ha hb hab
    have hw : ∀ k, w k < c k := hw
    have hw' : ∀ k, w' k < c k := hw'
    show ∀ k, (a • w + b • w') k < c k
    intro k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : a * w k ≤ a * c k := mul_le_mul_of_nonneg_left (hw k).le ha
    have h2 : b * w' k ≤ b * c k := mul_le_mul_of_nonneg_left (hw' k).le hb
    have hW : a * c k + b * c k = c k := by rw [← add_mul, hab, one_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · have : a * w k < a * c k := mul_lt_mul_of_pos_left (hw k) ha'
      linarith
    · have hb' : 0 < b := by linarith
      have : b * w' k < b * c k := mul_lt_mul_of_pos_left (hw' k) hb'
      linarith
  have hdisj' : Disjoint L S := by
    rw [Set.disjoint_left]
    intro w hwL hwS
    exact hdisj w hwS hwL
  obtain ⟨f, u, hfL, hfS⟩ := geometric_hahn_banach_open hLc hLo hS hdisj'
  set q : K → ℝ := fun k => f (fun j => if k = j then 1 else 0) with hqdef
  have hf : ∀ w, f w = dot q w := by
    intro w
    have := LinearMap.pi_apply_eq_sum_univ (f : (K → ℝ) →ₗ[ℝ] ℝ) w
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this, dot]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hmem : ∀ δ > 0, ∀ t ≥ 0, ∀ k₀,
      (fun j => c j + (-δ) - (if j = k₀ then t else 0)) ∈ L := by
    intro δ hδ t ht k₀ j
    show c j + -δ - (if j = k₀ then t else 0) < c j
    split_ifs <;> linarith
  have hdotL : ∀ δ t k₀, dot q (fun j => c j + (-δ) - (if j = k₀ then t else 0)) =
      dot q c - δ * ∑ k, q k - q k₀ * t := by
    intro δ t k₀
    simp only [dot, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum]
    congr 1
    congr 1
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hq0 : 0 ≤ q := by
    intro k₀
    show 0 ≤ q k₀
    by_contra hneg
    push_neg at hneg
    obtain ⟨c0, hc0⟩ : ∃ c0, c0 = dot q c - 1 * ∑ k, q k := ⟨_, rfl⟩
    obtain ⟨t, htdef⟩ : ∃ t, t = max 0 ((u - c0 + 1) / (-q k₀)) := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := htdef ▸ le_max_left _ _
    have ht1 : (u - c0 + 1) / (-q k₀) ≤ t := htdef ▸ le_max_right _ _
    have ht2 : u - c0 + 1 ≤ t * (-q k₀) := by
      rwa [div_le_iff₀ (by linarith)] at ht1
    have h := hfL _ (hmem 1 one_pos t ht0 k₀)
    rw [hf, hdotL] at h
    nlinarith
  have hσ : 0 ≤ ∑ k, q k := Finset.sum_nonneg fun k _ => hq0 k
  have hcu : dot q c ≤ u := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have h := hfL _ (hmem (ε / (∑ k, q k + 1)) (by positivity) 0 le_rfl (Classical.arbitrary K))
    rw [hf, hdotL] at h
    have : ε / (∑ k, q k + 1) * ∑ k, q k ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  refine ⟨q, hq0, ?_, fun s hs => ?_⟩
  · intro hq
    have h1 := hfL _ (hmem 1 one_pos 0 le_rfl (Classical.arbitrary K))
    have h2 := hfS _ hs0
    rw [hf, hq] at h1 h2
    simp [dot] at h1 h2
    linarith
  · have := hfS s hs
    rw [hf] at this
    linarith

namespace Economy

variable {N : Type*} [Fintype N] (E : Economy N K)

/-- `S(x) = ∑ᵢ Pᵢ(xᵢ)`: aggregate bundles that, suitably divided, make everyone at least as well
  off as at `x`. -/
def Ssum (x : N → K → ℝ) : Set (K → ℝ) :=
  {s | ∃ z : N → K → ℝ, (∀ i, 0 ≤ z i ∧ (E.pref i).R (z i) (x i)) ∧ s = ∑ i, z i}

/-- `{t | tW ∈ S(x) + ℝᴷ₊}`. -/
def Tset (x : N → K → ℝ) : Set ℝ := {t | ∃ s ∈ E.Ssum x, s ≤ t • E.W}

/-- Debreu's coefficient of resource utilization `t(x)`. -/
def tcoef (x : N → K → ℝ) : ℝ := sInf (E.Tset x)

lemma Tset_bdd [Nonempty N] [Nonempty K] (x : N → K → ℝ) : BddBelow (E.Tset x) := by
  refine ⟨0, ?_⟩
  rintro t ⟨s, ⟨z, hz, rfl⟩, hle⟩
  obtain ⟨k⟩ := ‹Nonempty K›
  have h1 : 0 ≤ (∑ i, z i) k := by
    rw [Finset.sum_apply]
    exact Finset.sum_nonneg fun i _ => (hz i).1 k
  have h2 : (∑ i, z i) k ≤ t * E.W k := hle k
  by_contra ht
  push_neg at ht
  have : t * E.W k < 0 := mul_neg_of_neg_of_pos ht (E.W_pos k)
  linarith

lemma one_mem_Tset {x : N → K → ℝ} (hx : E.Feasible x) : (1 : ℝ) ∈ E.Tset x := by
  refine ⟨∑ i, x i, ⟨x, fun i => ⟨hx.1 i, (E.pref i).refl (hx.1 i)⟩, rfl⟩, fun k => ?_⟩
  show (∑ i, x i) k ≤ (1 : ℝ) * E.W k
  rw [one_mul, Finset.sum_apply]
  exact hx.2 k

/-- **Remark 1**, inequality: `1 − t(x) ≤ Y(x,p)` for every `p ∈ Σ_K(W)`. -/
theorem remark1_lower [Nonempty N] [Nonempty K] {x : N → K → ℝ} (hx : E.Feasible x)
    {p : K → ℝ} (hp : p ∈ E.Prices) : 1 - E.tcoef x ≤ E.Y x p := by
  have : ∑ i, mu (E.pref i) p (x i) ≤ E.tcoef x := by
    apply le_csInf ⟨1, E.one_mem_Tset hx⟩
    rintro t ⟨s, ⟨z, hz, rfl⟩, hle⟩
    calc ∑ i, mu (E.pref i) p (x i) ≤ ∑ i, dot p (z i) :=
          Finset.sum_le_sum fun i _ => mu_le hp.1 (hz i).1 (hz i).2
      _ = dot p (∑ i, z i) := (dot_sum_right p z).symm
      _ ≤ dot p (t • E.W) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hle k) (hp.1 k)
      _ = t := by rw [dot_smul_right, hp.2, mul_one]
  simp only [Y]
  linarith

/-- The minimum of `Y(x,·)` over `Σ_K(W)` is attained. -/
theorem remark1_min_exists [Nonempty N] [Nonempty K] {x : N → K → ℝ} (hx : E.Feasible x) :
    ∃ p ∈ E.Prices, ∀ p' ∈ E.Prices, E.Y x p ≤ E.Y x p' := by
  obtain ⟨⟨x', p⟩, ⟨hx', hp⟩, hmin⟩ := E.exists_min_on ({x} ×ˢ E.Prices)
    (isCompact_singleton.prod E.isCompact_prices) ⟨(x, E.p0), Set.mem_singleton x, E.p0_mem⟩
    fun q hq => by
      rw [Set.mem_singleton_iff.1 hq.1]
      exact ⟨hx, hq.2⟩
  rw [Set.mem_singleton_iff.1 hx'] at hmin
  exact ⟨p, hp, fun p' hp' => hmin (x, p') ⟨Set.mem_singleton x, hp'⟩⟩

/-- **Remark 1**, equality: with convex preferences, `min_p Y(x,p) = 1 − t(x)`. -/
theorem remark1_eq [Nonempty N] [Nonempty K] (hconv : ∀ i, (E.pref i).IsConvex)
    {x : N → K → ℝ} (hx : E.Feasible x) : ∃ p ∈ E.Prices, E.Y x p = 1 - E.tcoef x := by
  classical
  have hSc : Convex ℝ (E.Ssum x) := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩ a b ha hb hab
    refine ⟨fun i => a • z i + b • z' i,
      fun i => hconv i (x i) (hx.1 i) (hz i) (hz' i) ha hb hab, ?_⟩
    simp [Finset.smul_sum, Finset.sum_add_distrib]
  have hs0 : (∑ i, x i) ∈ E.Ssum x :=
    ⟨x, fun i => ⟨hx.1 i, (E.pref i).refl (hx.1 i)⟩, rfl⟩
  -- no point of S(x) lies strictly below t(x) W
  have hdisj : ∀ s ∈ E.Ssum x, ¬ ∀ k, s k < E.tcoef x * E.W k := by
    rintro s hs hlt
    have ht' : Finset.univ.sup' Finset.univ_nonempty (fun k => s k / E.W k) < E.tcoef x :=
      (Finset.sup'_lt_iff _).2 fun k _ => by
        rw [div_lt_iff₀ (E.W_pos k)]
        exact hlt k
    have hmem : Finset.univ.sup' Finset.univ_nonempty (fun k => s k / E.W k) ∈ E.Tset x :=
      ⟨s, hs, fun k => by
        have : s k / E.W k ≤ Finset.univ.sup' Finset.univ_nonempty (fun k => s k / E.W k) :=
          Finset.le_sup' (fun k => s k / E.W k) (Finset.mem_univ k)
        rw [div_le_iff₀ (E.W_pos k)] at this
        exact this⟩
    have : E.tcoef x ≤ Finset.univ.sup' Finset.univ_nonempty (fun k => s k / E.W k) :=
      csInf_le (E.Tset_bdd x) hmem
    linarith
  -- supporting hyperplane at t(x) W
  obtain ⟨q, hq0, hqne, hqS⟩ := separate_below hSc hs0 (fun k => E.tcoef x * E.W k) hdisj
  have hqW : 0 < dot q E.W := by
    obtain ⟨k, hk⟩ : ∃ k, q k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hqne (funext h)
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hq0 j) (E.W_nonneg j))
      ⟨k, mem_univ k, mul_pos (lt_of_le_of_ne (hq0 k) (Ne.symm hk)) (E.W_pos k)⟩
  set p : K → ℝ := (dot q E.W)⁻¹ • q with hpdef
  have hp : p ∈ E.Prices := by
    refine ⟨fun k => ?_, ?_⟩
    · simp only [hpdef, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 hqW.le) (hq0 k)
    · rw [hpdef, dot_smul_left, inv_mul_cancel₀ hqW.ne']
  have hpS : ∀ s ∈ E.Ssum x, E.tcoef x ≤ dot p s := fun s hs => by
    have h := hqS s hs
    have hc : dot q (fun k => E.tcoef x * E.W k) = E.tcoef x * dot q E.W := by
      simp only [dot, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hc] at h
    rw [hpdef, dot_smul_left, ← div_eq_inv_mul, le_div_iff₀ hqW]
    exact h
  -- hence ∑ᵢ μᵢ(p,xᵢ) ≥ t(x)
  have hsum : E.tcoef x ≤ ∑ i, mu (E.pref i) p (x i) := by
    apply le_of_forall_pos_le_add
    intro η hη
    have hcardpos : (0 : ℝ) < Fintype.card N := by exact_mod_cast Fintype.card_pos
    have hη' : 0 < η / Fintype.card N := by positivity
    choose z hz0 hzx hzc using fun i => exists_lt_of_mu_lt (P := E.pref i) (p := p) (hx.1 i)
      (lt_add_of_pos_right (mu (E.pref i) p (x i)) hη')
    have h1 := hpS _ ⟨z, fun i => ⟨hz0 i, hzx i⟩, rfl⟩
    rw [dot_sum_right] at h1
    have h2 : ∑ i, dot p (z i) ≤ ∑ i, (mu (E.pref i) p (x i) + η / Fintype.card N) :=
      Finset.sum_le_sum fun i _ => (hzc i).le
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    have h3 : (Fintype.card N : ℝ) * (η / Fintype.card N) = η := by field_simp
    linarith
  refine ⟨p, hp, le_antisymm ?_ (E.remark1_lower hx hp)⟩
  simp only [Y]
  linarith

/-- **Remark 1**: at a Pareto-optimal allocation `t(x) = 1`, so the dead loss is zero. -/
theorem remark1_pareto [Nonempty N] [Nonempty K] {x : N → K → ℝ} (hPO : E.ParetoOptimal x) :
    E.tcoef x = 1 := by
  obtain ⟨hx, hnot⟩ := hPO
  have hle : E.tcoef x ≤ 1 := csInf_le (E.Tset_bdd x) (E.one_mem_Tset hx)
  by_contra hne
  have hlt : E.tcoef x < 1 := lt_of_le_of_ne hle hne
  obtain ⟨t', ⟨s, ⟨z, hz, rfl⟩, hsle⟩, ht'⟩ := exists_lt_of_csInf_lt ⟨1, E.one_mem_Tset hx⟩ hlt
  have hcard : (0 : ℝ) < Fintype.card N := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < (1 - t') / Fintype.card N := div_pos (by linarith) hcard
  -- divide z + (1 − t') W as zᵢ + (1 − t')/N · W
  set y : N → K → ℝ := fun i k => z i k + (1 - t') / Fintype.card N * E.W k with hydef
  have hy0 : ∀ i, 0 ≤ y i := fun i k => by
    show 0 ≤ z i k + (1 - t') / Fintype.card N * E.W k
    have h1 : 0 ≤ z i k := (hz i).1 k
    have h2 := mul_pos hpos (E.W_pos k)
    linarith
  have hyF : E.Feasible y := by
    refine ⟨hy0, fun k => ?_⟩
    show ∑ i, (z i k + (1 - t') / Fintype.card N * E.W k) ≤ E.W k
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h1 : (∑ i, z i) k ≤ t' * E.W k := hsle k
    rw [Finset.sum_apply] at h1
    have h2 : (Fintype.card N : ℝ) * ((1 - t') / Fintype.card N * E.W k) = (1 - t') * E.W k := by
      field_simp
    linarith
  have hstrict : ∀ i, ¬ (E.pref i).R (x i) (y i) := fun i =>
    (E.pref i).strict_of_strict_weak (hx.1 i) (hz i).1 (hy0 i)
      ((E.pref i).mono (z i) (y i) (hz i).1 fun k => by
        show z i k < z i k + (1 - t') / Fintype.card N * E.W k
        have := mul_pos hpos (E.W_pos k)
        linarith) (hz i).2
  exact hnot ⟨y, hyF, fun i => (E.pref i).of_not (hx.1 i) (hy0 i) (hstrict i),
    Classical.arbitrary N, hstrict _⟩

end Economy

end Yq
