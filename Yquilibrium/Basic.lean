/-
  Yquilibrium (Goeree, 21 Nov 2026), Appendix A.
  Setup, the minimum-income function μ, and Lemma 1.
-/
import Yquilibrium.Imports

open Finset Filter Topology Set

noncomputable section

namespace Yq

variable {K : Type*} [Fintype K]

/-! ### Inner product ⟨p|z⟩ -/

/-- `dot p z = ⟨p|z⟩ = ∑ₖ pₖ zₖ`. -/
def dot (p z : K → ℝ) : ℝ := ∑ k, p k * z k

lemma dot_nonneg {p z : K → ℝ} (hp : 0 ≤ p) (hz : 0 ≤ z) : 0 ≤ dot p z :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hp k) (hz k)

lemma dot_add_left (p q z : K → ℝ) : dot (p + q) z = dot p z + dot q z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_smul_left (t : ℝ) (p z : K → ℝ) : dot (t • p) z = t * dot p z := by
  simp [dot, Finset.mul_sum, mul_assoc]

lemma dot_smul_right (t : ℝ) (p z : K → ℝ) : dot p (t • z) = t * dot p z := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma dot_zero_right (p : K → ℝ) : dot p 0 = 0 := by simp [dot]

lemma mul_le_dot {p z : K → ℝ} (hp : 0 ≤ p) (hz : 0 ≤ z) (k : K) : p k * z k ≤ dot p z :=
  Finset.single_le_sum (f := fun k => p k * z k) (fun j _ => mul_nonneg (hp j) (hz j))
    (Finset.mem_univ k)

lemma dot_pos {p z : K → ℝ} (hp : ∀ k, 0 < p k) (hz : 0 ≤ z) (hne : z ≠ 0) : 0 < dot p z := by
  obtain ⟨k, hk⟩ : ∃ k, z k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hp j).le (hz j))
    ⟨k, Finset.mem_univ k, mul_pos (hp k) (lt_of_le_of_ne (hz k) (Ne.symm hk))⟩

lemma continuous_dot_left {α : Type*} [TopologicalSpace α] {P : α → K → ℝ} (hP : Continuous P)
    (z : K → ℝ) : Continuous fun a => dot (P a) z :=
  continuous_finsetSum _ fun k _ => ((continuous_apply k).comp hP).mul continuous_const

lemma continuous_dot_right (p : K → ℝ) : Continuous fun z : K → ℝ => dot p z :=
  continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k)

lemma tendsto_one_div_succ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  simpa [Function.comp_def, one_div] using h

/-! ### Preferences -/

/-- A preference relation on `ℝ^K_{≥0}`; `R z x` means `z ≿ x`.
  Complete, transitive, continuous (closed upper and lower contour sets), and monotone in the
  two senses of Section 2 of the paper. Strict preference `z ≻ x` is `¬ R x z`. -/
structure Pref (K : Type*) [Fintype K] where
  R : (K → ℝ) → (K → ℝ) → Prop
  total : ∀ x y, 0 ≤ x → 0 ≤ y → R x y ∨ R y x
  trans : ∀ x y z, 0 ≤ x → 0 ≤ y → 0 ≤ z → R x y → R y z → R x z
  upper_closed : ∀ x, 0 ≤ x → IsClosed {z | 0 ≤ z ∧ R z x}
  lower_closed : ∀ x, 0 ≤ x → IsClosed {z | 0 ≤ z ∧ R x z}
  /-- `y ≫ x` implies `y ≻ x`. -/
  mono : ∀ x y, 0 ≤ x → (∀ k, x k < y k) → ¬ R x y
  /-- if `x ≻ 0`, `y ≥ x` and `y ≠ x` then `y ≻ x`. -/
  mono' : ∀ x y, 0 ≤ x → ¬ R 0 x → x ≤ y → x ≠ y → ¬ R x y

namespace Pref

variable (P : Pref K)

lemma refl {x : K → ℝ} (hx : 0 ≤ x) : P.R x x := (P.total x x hx hx).elim id id

lemma of_not {x y : K → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : ¬ P.R x y) : P.R y x :=
  (P.total x y hx hy).resolve_left h

/-- `z ≻ y ≿ x ⟹ z ≻ x`. -/
lemma strict_of_strict_weak {x y z : K → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h1 : ¬ P.R y z) (h2 : P.R y x) : ¬ P.R x z :=
  fun h => h1 (P.trans y x z hy hx hz h2 h)

/-- `z ≿ y ≻ x ⟹ z ≻ x`. -/
lemma strict_of_weak_strict {x y z : K → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h1 : P.R z y) (h2 : ¬ P.R x y) : ¬ P.R x z :=
  fun h => h2 (P.trans x z y hx hz hy h h1)

lemma tendsto_add_eps (y : K → ℝ) :
    Tendsto (fun n : ℕ => fun k => y k + 1 / ((n : ℝ) + 1)) atTop (𝓝 y) := by
  rw [tendsto_pi_nhds]
  intro k
  simpa using (tendsto_const_nhds (x := y k)).add tendsto_one_div_succ

/-- Weak monotonicity: `y ≥ x ⟹ y ≿ x` (Appendix A, first paragraph). -/
lemma weak_mono {x y : K → ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : P.R y x := by
  have hy : 0 ≤ y := hx.trans hxy
  have hmem : ∀ n : ℕ, (fun k => y k + 1 / ((n : ℝ) + 1)) ∈ {z | 0 ≤ z ∧ P.R z x} := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hz : (0 : K → ℝ) ≤ fun k => y k + 1 / ((n : ℝ) + 1) := fun k => by
      have := hy k
      simp only [Pi.zero_apply] at this ⊢
      linarith
    refine ⟨hz, P.of_not hx hz (P.mono x _ hx fun k => ?_)⟩
    have := hxy k
    linarith
  exact ((P.upper_closed x hx).mem_of_tendsto (tendsto_add_eps y)
    (Eventually.of_forall hmem)).2

end Pref

/-! ### The minimum income μᵢ(p, x) = inf {⟨p|z⟩ | z ≿ x} -/

/-- `mu P p x = inf {⟨p|z⟩ | z ≥ 0, z ≿ x}`. -/
def mu (P : Pref K) (p x : K → ℝ) : ℝ :=
  sInf ((fun z => dot p z) '' {z | 0 ≤ z ∧ P.R z x})

variable {P : Pref K} {p x y z : K → ℝ} {c : ℝ}

lemma mu_bdd (hp : 0 ≤ p) : BddBelow ((fun z => dot p z) '' {z | 0 ≤ z ∧ P.R z x}) :=
  ⟨0, by rintro _ ⟨z, hz, rfl⟩; exact dot_nonneg hp hz.1⟩

lemma mu_set_nonempty (hx : 0 ≤ x) : ((fun z => dot p z) '' {z | 0 ≤ z ∧ P.R z x}).Nonempty :=
  ⟨_, x, ⟨hx, P.refl hx⟩, rfl⟩

lemma mu_le (hp : 0 ≤ p) (hz : 0 ≤ z) (h : P.R z x) : mu P p x ≤ dot p z :=
  csInf_le (mu_bdd hp) ⟨z, ⟨hz, h⟩, rfl⟩

lemma le_mu (hx : 0 ≤ x) (h : ∀ z, 0 ≤ z → P.R z x → c ≤ dot p z) : c ≤ mu P p x :=
  le_csInf (mu_set_nonempty hx) (by rintro _ ⟨z, hz, rfl⟩; exact h z hz.1 hz.2)

lemma exists_lt_of_mu_lt (hx : 0 ≤ x) (h : mu P p x < c) :
    ∃ z, 0 ≤ z ∧ P.R z x ∧ dot p z < c := by
  obtain ⟨_, ⟨z, hz, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (mu_set_nonempty hx) h
  exact ⟨z, hz.1, hz.2, hlt⟩

/-! ### Lemma 1 -/

/-- Lemma 1(a), lower bound. -/
theorem mu_nonneg (hp : 0 ≤ p) (hx : 0 ≤ x) : 0 ≤ mu P p x :=
  le_mu hx fun z hz _ => dot_nonneg hp hz

/-- Lemma 1(a), upper bound. -/
theorem mu_le_dot (hp : 0 ≤ p) (hx : 0 ≤ x) : mu P p x ≤ dot p x :=
  mu_le hp hx (P.refl hx)

/-- Lemma 1(b), concavity in `p`. -/
theorem mu_concave (hx : 0 ≤ x) : ConcaveOn ℝ {p : K → ℝ | 0 ≤ p} (fun p => mu P p x) := by
  refine ⟨?_, ?_⟩
  · intro p hp q hq a b ha hb _
    have hp' : 0 ≤ p := hp
    have hq' : 0 ≤ q := hq
    show (0 : K → ℝ) ≤ a • p + b • q
    intro k
    simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hp' k)) (mul_nonneg hb (hq' k))
  · intro p hp q hq a b ha hb _
    have hp' : 0 ≤ p := hp
    have hq' : 0 ≤ q := hq
    simp only [smul_eq_mul]
    apply le_mu hx
    intro z hz hzx
    rw [dot_add_left, dot_smul_left, dot_smul_left]
    exact add_le_add (mul_le_mul_of_nonneg_left (mu_le hp' hz hzx) ha)
      (mul_le_mul_of_nonneg_left (mu_le hq' hz hzx) hb)

lemma mul_mu_le {t : ℝ} (ht : 0 ≤ t) (hp : 0 ≤ p) (hx : 0 ≤ x) :
    t * mu P p x ≤ mu P (t • p) x :=
  le_mu hx fun z hz hzx => by
    rw [dot_smul_left]
    exact mul_le_mul_of_nonneg_left (mu_le hp hz hzx) ht

/-- Lemma 1(b), homogeneity of degree one in `p`. -/
theorem mu_smul {t : ℝ} (ht : 0 ≤ t) (hp : 0 ≤ p) (hx : 0 ≤ x) :
    mu P (t • p) x = t * mu P p x := by
  rcases ht.eq_or_lt with rfl | ht'
  · rw [zero_smul, zero_mul]
    refine le_antisymm ?_ (mu_nonneg le_rfl hx)
    have := mu_le (P := P) (p := 0) le_rfl hx (P.refl hx)
    simpa [dot] using this
  · apply le_antisymm
    · have htp : 0 ≤ t • p := fun k => by
        simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg ht (hp k)
      have h := mul_mu_le (P := P) (inv_nonneg.2 ht) htp hx
      rw [smul_smul, inv_mul_cancel₀ ht'.ne', one_smul] at h
      calc mu P (t • p) x = t * (t⁻¹ * mu P (t • p) x) := by field_simp
        _ ≤ t * mu P p x := mul_le_mul_of_nonneg_left h ht
    · exact mul_mu_le ht hp hx

/-- Lemma 1(c). -/
theorem mu_mono_pref (hp : 0 ≤ p) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : P.R y x) :
    mu P p x ≤ mu P p y :=
  le_mu hy fun z hz hzy => mu_le hp hz (P.trans z y x hz hy hx hzy h)

/-- Lemma 1(d): for `p ≫ 0`, `y ≻ x` implies `μ(p,y) > μ(p,x)`. -/
theorem mu_strict (hp : ∀ k, 0 < p k) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : ¬ P.R x y) :
    mu P p x < mu P p y := by
  have hp0 : 0 ≤ p := fun k => (hp k).le
  -- the set of cheap bundles at least as good as `y` is compact
  have hSc : IsCompact {z : K → ℝ | (0 ≤ z ∧ P.R z y) ∧ dot p z ≤ dot p y} := by
    refine (isCompact_univ_pi fun k =>
      isCompact_Icc (a := (0 : ℝ)) (b := dot p y / p k)).of_isClosed_subset ?_ ?_
    · exact (P.upper_closed y hy).inter (isClosed_le (continuous_dot_right p) continuous_const)
    · rintro z ⟨⟨hz, _⟩, hzc⟩ k _
      refine ⟨hz k, ?_⟩
      rw [le_div_iff₀ (hp k)]
      have := mul_le_dot hp0 hz k
      linarith
  obtain ⟨zs, ⟨⟨hzs0, hzsy⟩, _⟩, hmin⟩ :=
    hSc.exists_isMinOn ⟨y, ⟨hy, P.refl hy⟩, le_rfl⟩ (continuous_dot_right p).continuousOn
  rw [isMinOn_iff] at hmin
  -- `zs` is a cheapest bundle: ⟨p|zs⟩ ≤ μ(p,y)
  have hmuy : dot p zs ≤ mu P p y := le_mu hy fun z hz hzy => by
    by_cases hc : dot p z ≤ dot p y
    · exact hmin z ⟨⟨hz, hzy⟩, hc⟩
    · exact (hmin y ⟨⟨hy, P.refl hy⟩, le_rfl⟩).trans (not_le.1 hc).le
  have hxzs : ¬ P.R x zs := P.strict_of_weak_strict hx hy hzs0 hzsy h
  have hzs_ne : zs ≠ 0 := by
    rintro rfl
    exact hxzs (P.weak_mono le_rfl hx)
  have hpos := dot_pos hp hzs0 hzs_ne
  -- λ • zs ≻ x for some λ < 1, because the strict upper contour set is open
  have hlim : Tendsto (fun n : ℕ => (1 - 1 / ((n : ℝ) + 1)) • zs) atTop (𝓝 zs) := by
    have : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_succ
    simpa using this.smul_const zs
  obtain ⟨n, hn⟩ := (hlim.eventually
    ((P.lower_closed x hx).isOpen_compl.mem_nhds fun h' => hxzs h'.2)).exists
  have hn1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hn2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hlam0 : (0 : ℝ) ≤ 1 - 1 / ((n : ℝ) + 1) := by linarith
  have hz' : 0 ≤ (1 - 1 / ((n : ℝ) + 1)) • zs := fun k => by
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hlam0 (hzs0 k)
  have hR : P.R ((1 - 1 / ((n : ℝ) + 1)) • zs) x := P.of_not hx hz' (fun h' => hn ⟨hz', h'⟩)
  calc mu P p x ≤ dot p ((1 - 1 / ((n : ℝ) + 1)) • zs) := mu_le hp0 hz' hR
    _ = (1 - 1 / ((n : ℝ) + 1)) * dot p zs := dot_smul_right _ _ _
    _ < dot p zs := by nlinarith
    _ ≤ mu P p y := hmuy

/-- Lemma 1(e): `μ` is upper semicontinuous in `(p, x)`, stated for any continuous
  parametrization `a ↦ (P a, X a)` of non-negative prices and bundles. -/
theorem mu_usc {α : Type*} [TopologicalSpace α] {s : Set α} {Pf X : α → K → ℝ}
    (hP : Continuous Pf) (hX : Continuous X) (hPs : ∀ a ∈ s, 0 ≤ Pf a)
    (hXs : ∀ a ∈ s, 0 ≤ X a) :
    UpperSemicontinuousOn (fun a => mu P (Pf a) (X a)) s := by
  intro a ha c hc
  obtain ⟨z, hz, hzx, hzc⟩ := exists_lt_of_mu_lt (hXs a ha) hc
  have hσ : 0 ≤ ∑ k, Pf a k := Finset.sum_nonneg fun k _ => hPs a ha k
  have hδ : 0 < (c - dot (Pf a) z) / (2 * (∑ k, Pf a k + 1)) :=
    div_pos (by linarith) (by positivity)
  set δ := (c - dot (Pf a) z) / (2 * (∑ k, Pf a k + 1)) with hδdef
  have hw0 : (0 : K → ℝ) ≤ fun k => z k + δ := fun k => by
    have := hz k
    simp only [Pi.zero_apply] at this ⊢
    linarith
  have hdw : dot (Pf a) (fun k => z k + δ) < c := by
    have h1 : dot (Pf a) (fun k => z k + δ) = dot (Pf a) z + δ * ∑ k, Pf a k := by
      simp only [dot, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    have h2 : δ * (2 * (∑ k, Pf a k + 1)) = c - dot (Pf a) z := by
      rw [hδdef]
      field_simp
    rw [h1]
    nlinarith
  have hzw : ¬ P.R z (fun k => z k + δ) := P.mono z _ hz fun k => by linarith
  have hxw : ¬ P.R (X a) (fun k => z k + δ) :=
    P.strict_of_strict_weak (hXs a ha) hz hw0 hzw hzx
  have h1 : ∀ᶠ a' in 𝓝 a, X a' ∈ {v | 0 ≤ v ∧ P.R v (fun k => z k + δ)}ᶜ :=
    hX.continuousAt.preimage_mem_nhds
      ((P.upper_closed _ hw0).isOpen_compl.mem_nhds fun h' => hxw h'.2)
  have h2 : ∀ᶠ a' in 𝓝 a, dot (Pf a') (fun k => z k + δ) < c :=
    (continuous_dot_left hP _).continuousAt.eventually_lt continuousAt_const hdw
  filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, self_mem_nhdsWithin]
    with a' h1' h2' ha'
  have hR : P.R (fun k => z k + δ) (X a') :=
    P.of_not (hXs a' ha') hw0 fun h' => h1' ⟨hXs a' ha', h'⟩
  exact (mu_le (hPs a' ha') hw0 hR).trans_lt h2'

end Yq
