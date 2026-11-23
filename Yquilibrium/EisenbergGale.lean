/-
  Yquilibrium (Goeree, 21 Nov 2026), Appendix (computational aspects), Lemma 4.
  For concave, linearly homogeneous utilities (CES being the leading example) and incomes
  m ≫ 0, the Eisenberg–Gale objective ∑ᵢ mᵢ (log vᵢ(p,mᵢ) − log uᵢ(xᵢ)) is convex and
  non-negative, and its roots are the Walrasian equilibria for m.
-/
import Yquilibrium.Duality
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Filter Topology Set

noncomputable section

namespace Yq

variable {K : Type*} [Fintype K]

/-- Concavity of `log` in elementary form. -/
lemma log_comb {x y a b : ℝ} (hx : 0 < x) (hy : 0 < y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a * Real.log x + b * Real.log y ≤ Real.log (a * x + b * y) := by
  have hz : 0 < a * x + b * y := by
    rcases ha.lt_or_eq with ha' | ha'
    · have := mul_pos ha' hx
      have := mul_nonneg hb hy.le
      linarith
    · have hb1 : b = 1 := by linarith
      rw [← ha', hb1]
      simpa using hy
  have h1 := Real.log_le_sub_one_of_pos (div_pos hx hz)
  have h2 := Real.log_le_sub_one_of_pos (div_pos hy hz)
  rw [Real.log_div hx.ne' hz.ne'] at h1
  rw [Real.log_div hy.ne' hz.ne'] at h2
  have h3 : a * (x / (a * x + b * y)) + b * (y / (a * x + b * y)) = 1 := by
    field_simp
  have h4 : a * Real.log (a * x + b * y) + b * Real.log (a * x + b * y) =
      Real.log (a * x + b * y) := by rw [← add_mul, hab, one_mul]
  have h5 := mul_le_mul_of_nonneg_left h1 ha
  have h6 := mul_le_mul_of_nonneg_left h2 hb
  nlinarith

section Homog

variable {u : (K → ℝ) → ℝ}

lemma u_zero_of_homog (hh : ∀ t z, 0 ≤ t → 0 ≤ z → u (t • z) = t * u z) : u 0 = 0 := by
  have := hh 0 0 le_rfl le_rfl
  simpa using this

/-- `v(p,c) = c · v(p,1)` for linearly homogeneous utilities. -/
lemma vind_scale (hc : ContinuousOn u {z | 0 ≤ z})
    (hh : ∀ t z, 0 ≤ t → 0 ≤ z → u (t • z) = t * u z) {p : K → ℝ} (hp : ∀ k, 0 < p k)
    {c : ℝ} (hc0 : 0 ≤ c) : vind u p c = c * vind u p 1 := by
  obtain ⟨z1, hz1, hv1, hmax1⟩ := vind_attained hc hp zero_le_one
  obtain ⟨zc, hzc, hvc, hmaxc⟩ := vind_attained hc hp hc0
  rw [hvc, hv1]
  rcases hc0.lt_or_eq with hcpos | hc0'
  · apply le_antisymm
    · have hnn : 0 ≤ c⁻¹ • zc := fun k => by
        simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.2 hcpos.le) (hzc.1 k)
      have h := hmax1 (c⁻¹ • zc) hnn (by
        rw [dot_smul_right]
        calc c⁻¹ * dot p zc ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left hzc.2 (inv_nonneg.2 hcpos.le)
          _ = 1 := inv_mul_cancel₀ hcpos.ne')
      rw [hh c⁻¹ zc (inv_nonneg.2 hcpos.le) hzc.1] at h
      calc u zc = c * (c⁻¹ * u zc) := by field_simp
        _ ≤ c * u z1 := mul_le_mul_of_nonneg_left h hcpos.le
    · have hnn : 0 ≤ c • z1 := fun k => by
        simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg hcpos.le (hz1.1 k)
      have h := hmaxc (c • z1) hnn (by
        rw [dot_smul_right]
        linarith [mul_le_mul_of_nonneg_left hz1.2 hcpos.le])
      rwa [hh c z1 hcpos.le hz1.1] at h
  · subst hc0'
    have hz0 : zc = 0 := by
      funext k
      have h1 := mul_le_dot (fun k => (hp k).le) hzc.1 k
      have h2 := hzc.2
      have h3 : 0 ≤ zc k := hzc.1 k
      have h4 := mul_nonneg (hp k).le h3
      have h5 : p k * zc k = 0 := by linarith
      exact (mul_eq_zero.1 h5).resolve_left (hp k).ne'
    rw [hz0, u_zero_of_homog hh, zero_mul]

lemma vind_one_pos (hc : ContinuousOn u {z | 0 ≤ z})
    (hpos : ∀ z, (∀ k, 0 < z k) → 0 < u z) {p : K → ℝ} (hp : ∀ k, 0 < p k) :
    0 < vind u p 1 := by
  obtain ⟨z1, hz1, hv1, hmax1⟩ := vind_attained hc hp zero_le_one
  have hσ : 0 ≤ ∑ k, p k := Finset.sum_nonneg fun k _ => (hp k).le
  have hε : 0 < 1 / (∑ k, p k + 1) := by positivity
  have h1 : u (fun _ => 1 / (∑ k, p k + 1)) ≤ u z1 := hmax1 _ (fun k => hε.le) (by
    show ∑ k, p k * (1 / (∑ k, p k + 1)) ≤ 1
    rw [← Finset.sum_mul, mul_one_div, div_le_one (by positivity)]
    linarith)
  rw [hv1]
  exact (hpos _ fun k => hε).trans_le h1

/-- The expenditure needed to reach utility one, `e(p) = inf {⟨p|z⟩ | u(z) ≥ 1}`. -/
def expend (u : (K → ℝ) → ℝ) (p : K → ℝ) : ℝ :=
  sInf ((fun z => dot p z) '' {z | 0 ≤ z ∧ 1 ≤ u z})

lemma expend_nonempty (hh : ∀ t z, 0 ≤ t → 0 ≤ z → u (t • z) = t * u z)
    (hpos : ∀ z, (∀ k, 0 < z k) → 0 < u z) (p : K → ℝ) :
    ((fun z => dot p z) '' {z | 0 ≤ z ∧ 1 ≤ u z}).Nonempty := by
  have h1 : 0 < u (fun _ => (1 : ℝ)) := hpos _ fun _ => one_pos
  have hnn : (0 : K → ℝ) ≤ fun _ => (1 : ℝ) := fun _ => zero_le_one
  refine ⟨_, (u fun _ => (1 : ℝ))⁻¹ • (fun _ => (1 : ℝ)), ⟨fun k => ?_, ?_⟩, rfl⟩
  · simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    exact (inv_pos.2 h1).le
  · rw [hh _ _ (inv_pos.2 h1).le hnn, inv_mul_cancel₀ h1.ne']

lemma expend_bdd {p : K → ℝ} (hp : 0 ≤ p) :
    BddBelow ((fun z => dot p z) '' {z | 0 ≤ z ∧ 1 ≤ u z}) :=
  ⟨0, by rintro _ ⟨z, hz, rfl⟩; exact dot_nonneg hp hz.1⟩

/-- `v(p,1) = 1/e(p)` and `e(p) > 0` for `p ≫ 0`. -/
lemma vind_one_eq (hc : ContinuousOn u {z | 0 ≤ z})
    (hh : ∀ t z, 0 ≤ t → 0 ≤ z → u (t • z) = t * u z)
    (hpos : ∀ z, (∀ k, 0 < z k) → 0 < u z) {p : K → ℝ} (hp : ∀ k, 0 < p k) :
    vind u p 1 = (expend u p)⁻¹ ∧ 0 < expend u p := by
  have hV := vind_one_pos hc hpos hp
  obtain ⟨z1, hz1, hv1, hmax1⟩ := vind_attained hc hp zero_le_one
  have hu0 := u_zero_of_homog hh
  -- 1/v(p,1) ≤ e(p)
  have hge : (vind u p 1)⁻¹ ≤ expend u p := by
    apply le_csInf (expend_nonempty hh hpos p)
    rintro _ ⟨z, ⟨hz, hz1'⟩, rfl⟩
    have hzne : z ≠ 0 := by
      rintro rfl
      rw [hu0] at hz1'
      linarith
    have hd := dot_pos hp hz hzne
    have hnn : 0 ≤ (dot p z)⁻¹ • z := fun k => by
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 hd.le) (hz k)
    have h := hmax1 _ hnn (by rw [dot_smul_right, inv_mul_cancel₀ hd.ne'])
    rw [hh _ _ (inv_nonneg.2 hd.le) hz, ← hv1] at h
    have h2 : (dot p z)⁻¹ ≤ vind u p 1 :=
      (le_mul_of_one_le_right (inv_nonneg.2 hd.le) hz1').trans h
    have := inv_anti₀ (inv_pos.2 hd) h2
    rwa [inv_inv] at this
  have he : 0 < expend u p := lt_of_lt_of_le (inv_pos.2 hV) hge
  -- e(p) ≤ 1/v(p,1)
  have hle : expend u p ≤ (vind u p 1)⁻¹ := by
    have huz : 0 < u z1 := hv1 ▸ hV
    have hnn : 0 ≤ (u z1)⁻¹ • z1 := fun k => by
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 huz.le) (hz1.1 k)
    have h1 : 1 ≤ u ((u z1)⁻¹ • z1) := by
      rw [hh _ _ (inv_nonneg.2 huz.le) hz1.1, inv_mul_cancel₀ huz.ne']
    have h := csInf_le (expend_bdd (fun k => (hp k).le)) ⟨_, ⟨hnn, h1⟩, rfl⟩
    have h3 : dot p ((u z1)⁻¹ • z1) ≤ (u z1)⁻¹ := by
      rw [dot_smul_right]
      calc (u z1)⁻¹ * dot p z1 ≤ (u z1)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hz1.2 (inv_nonneg.2 huz.le)
        _ = (u z1)⁻¹ := mul_one _
    rw [hv1]
    exact h.trans h3
  refine ⟨le_antisymm ?_ ?_, he⟩
  · have := inv_anti₀ he hle
    rwa [inv_inv] at this
  · have := inv_anti₀ (inv_pos.2 hV) hge
    rwa [inv_inv] at this

/-- `e` is concave in `p`. -/
lemma expend_concave (hh : ∀ t z, 0 ≤ t → 0 ≤ z → u (t • z) = t * u z)
    (hpos : ∀ z, (∀ k, 0 < z k) → 0 < u z) {p p' : K → ℝ} (hp : 0 ≤ p) (hp' : 0 ≤ p')
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * expend u p + b * expend u p' ≤ expend u (a • p + b • p') := by
  apply le_csInf (expend_nonempty hh hpos _)
  rintro _ ⟨z, hz, rfl⟩
  simp only
  rw [dot_add_left, dot_smul_left, dot_smul_left]
  exact add_le_add (mul_le_mul_of_nonneg_left (csInf_le (expend_bdd hp) ⟨z, hz, rfl⟩) ha)
    (mul_le_mul_of_nonneg_left (csInf_le (expend_bdd hp') ⟨z, hz, rfl⟩) hb)

end Homog

namespace Economy

variable {N : Type*} [Fintype N] (E : Economy N K) (u : N → (K → ℝ) → ℝ)

/-- `u` represents the preferences of `E` by continuous, concave, linearly homogeneous utilities
  that are positive on strictly positive bundles (e.g. CES with positive weights). -/
structure HomogRep (E : Economy N K) (u : N → (K → ℝ) → ℝ) : Prop where
  rep : ∀ i z x, 0 ≤ z → 0 ≤ x → ((E.pref i).R z x ↔ u i x ≤ u i z)
  cont : ∀ i, ContinuousOn (u i) {z | 0 ≤ z}
  concave : ∀ i, ConcaveOn ℝ {z : K → ℝ | 0 ≤ z} (u i)
  homog : ∀ i t z, 0 ≤ t → 0 ≤ z → u i (t • z) = t * u i z
  pos : ∀ i z, (∀ k, 0 < z k) → 0 < u i z

/-- The objective of program (EG): `∑ᵢ mᵢ (log vᵢ(p,mᵢ) − log uᵢ(xᵢ))`. -/
def EG (m : N → ℝ) (x : N → K → ℝ) (p : K → ℝ) : ℝ :=
  ∑ i, m i * (Real.log (vind (u i) p (m i)) - Real.log (u i (x i)))

/-- The domain on which the objective is finite: feasible `x` with `uᵢ(xᵢ) > 0`, and `p ≫ 0`.
  (Elsewhere the objective is `+∞`.) -/
def EGDom : Set ((N → K → ℝ) × (K → ℝ)) :=
  {q | E.Feasible q.1 ∧ (∀ i, 0 < u i (q.1 i)) ∧ q.2 ∈ E.Prices ∧ ∀ k, 0 < q.2 k}

variable {E u}

/-- The decomposition behind the non-negativity and root parts of Lemma 4. -/
lemma EG_split (hu : E.HomogRep u) {m : N → ℝ} (hm : Incomes m) (hmpos : ∀ i, 0 < m i)
    {x : N → K → ℝ} {p : K → ℝ} (hq : (x, p) ∈ E.EGDom u) :
    EG u m x p = ∑ i, (m i * (Real.log (dot p (x i) * vind (u i) p 1) - Real.log (u i (x i)))
        + (dot p (x i) - m i - m i * Real.log (dot p (x i) / m i))) + (1 - ∑ i, dot p (x i)) ∧
      (∀ i, 0 ≤ m i * (Real.log (dot p (x i) * vind (u i) p 1) - Real.log (u i (x i)))) ∧
      (∀ i, 0 ≤ dot p (x i) - m i - m i * Real.log (dot p (x i) / m i)) ∧
      (∀ i, 0 < dot p (x i)) ∧ ∑ i, dot p (x i) ≤ 1 := by
  have hx : E.Feasible x := hq.1
  have hux : ∀ i, 0 < u i (x i) := hq.2.1
  have hp : p ∈ E.Prices := hq.2.2.1
  have hpos : ∀ k, 0 < p k := hq.2.2.2
  have hV : ∀ i, 0 < vind (u i) p 1 := fun i => vind_one_pos (hu.cont i) (hu.pos i) hpos
  have hc : ∀ i, 0 < dot p (x i) := by
    intro i
    refine dot_pos hpos (hx.1 i) fun h => ?_
    have := hux i
    rw [h, u_zero_of_homog (hu.homog i)] at this
    exact lt_irrefl _ this
  -- uᵢ(xᵢ) ≤ vᵢ(p,cᵢ) = cᵢ vᵢ(p,1)
  have hub : ∀ i, u i (x i) ≤ dot p (x i) * vind (u i) p 1 := by
    intro i
    rw [← vind_scale (hu.cont i) (hu.homog i) hpos (hc i).le]
    obtain ⟨zs, _, hv, hmax⟩ := vind_attained (hu.cont i) hpos (hc i).le
    rw [hv]
    exact hmax (x i) (hx.1 i) le_rfl
  have hsum : ∑ i, dot p (x i) ≤ 1 := by
    have := E.sum_dot_le hx hp.1
    rw [hp.2] at this
    exact this
  refine ⟨?_, fun i => ?_, fun i => ?_, hc, hsum⟩
  · have hterm : ∀ i, m i * (Real.log (vind (u i) p (m i)) - Real.log (u i (x i))) =
        (m i * (Real.log (dot p (x i) * vind (u i) p 1) - Real.log (u i (x i)))
          + (dot p (x i) - m i - m i * Real.log (dot p (x i) / m i))) + (m i - dot p (x i)) := by
      intro i
      rw [vind_scale (hu.cont i) (hu.homog i) hpos (hmpos i).le,
        Real.log_mul (hmpos i).ne' (hV i).ne', Real.log_mul (hc i).ne' (hV i).ne',
        Real.log_div (hc i).ne' (hmpos i).ne']
      ring
    rw [EG, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, hm.2]
  · exact mul_nonneg (hmpos i).le (sub_nonneg.2 (Real.log_le_log (hux i) (hub i)))
  · have h1 := Real.log_le_sub_one_of_pos (div_pos (hc i) (hmpos i))
    have h2 := mul_le_mul_of_nonneg_left h1 (hmpos i).le
    have h3 : m i * (dot p (x i) / m i - 1) = dot p (x i) - m i := by
      have hmne := (hmpos i).ne'
      field_simp
    linarith

/-- **Lemma 4**, non-negativity. -/
theorem lemma4_nonneg (hu : E.HomogRep u) {m : N → ℝ} (hm : Incomes m) (hmpos : ∀ i, 0 < m i)
    {x : N → K → ℝ} {p : K → ℝ} (hq : (x, p) ∈ E.EGDom u) : 0 ≤ EG u m x p := by
  obtain ⟨heq, hA, hB, -, hsum⟩ := EG_split hu hm hmpos hq
  rw [heq]
  have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => add_nonneg (hA i) (hB i)
  linarith

/-- **Lemma 4**, roots: the objective vanishes exactly at the Walrasian equilibria for `m`. -/
theorem lemma4_roots [Nonempty N] [Nonempty K] (hu : E.HomogRep u) {m : N → ℝ}
    (hm : Incomes m) (hmpos : ∀ i, 0 < m i) {x : N → K → ℝ} {p : K → ℝ} :
    ((x, p) ∈ E.EGDom u ∧ EG u m x p = 0) ↔ E.IsWalrasianFor m x p := by
  constructor
  · rintro ⟨hq, h0⟩
    obtain ⟨heq, hA, hB, hc, hsum⟩ := EG_split hu hm hmpos hq
    have hx : E.Feasible x := hq.1
    have hux : ∀ i, 0 < u i (x i) := hq.2.1
    have hp : p ∈ E.Prices := hq.2.2.1
    have hpos : ∀ k, 0 < p k := hq.2.2.2
    have hall : ∑ i, (m i * (Real.log (dot p (x i) * vind (u i) p 1) - Real.log (u i (x i)))
        + (dot p (x i) - m i - m i * Real.log (dot p (x i) / m i))) = 0 := by
      have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => add_nonneg (hA i) (hB i)
      linarith
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => add_nonneg (hA i) (hB i)).1 hall
    have hAi : ∀ i, m i * (Real.log (dot p (x i) * vind (u i) p 1) - Real.log (u i (x i))) = 0 :=
      fun i => by have := hzero i (mem_univ i); linarith [hA i, hB i]
    have hBi : ∀ i, dot p (x i) - m i - m i * Real.log (dot p (x i) / m i) = 0 :=
      fun i => by have := hzero i (mem_univ i); linarith [hA i, hB i]
    have hV : ∀ i, 0 < vind (u i) p 1 := fun i => vind_one_pos (hu.cont i) (hu.pos i) hpos
    -- cᵢ = mᵢ
    have hcm : ∀ i, dot p (x i) = m i := by
      intro i
      by_contra hne
      have hr : dot p (x i) / m i ≠ 1 := by
        intro h
        rw [div_eq_one_iff_eq (hmpos i).ne'] at h
        exact hne h
      have h1 := Real.log_lt_sub_one_of_pos (div_pos (hc i) (hmpos i)) hr
      have h2 := mul_lt_mul_of_pos_left h1 (hmpos i)
      have h3 : m i * (dot p (x i) / m i - 1) = dot p (x i) - m i := by
        have hmne := (hmpos i).ne'
        field_simp
      linarith [hBi i]
    -- uᵢ(xᵢ) = vᵢ(p,mᵢ)
    have huv : ∀ i, u i (x i) = vind (u i) p (m i) := by
      intro i
      have h1 : Real.log (dot p (x i) * vind (u i) p 1) = Real.log (u i (x i)) := by
        have := hAi i
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (hmpos i).ne'
        · linarith
      have h2 := Real.log_injOn_pos (Set.mem_Ioi.2 (mul_pos (hc i) (hV i)))
        (Set.mem_Ioi.2 (hux i)) h1
      rw [vind_scale (hu.cont i) (hu.homog i) hpos (hmpos i).le, ← hcm i]
      exact h2.symm
    refine ⟨hx, hp, fun i => ⟨hx.1 i, (hcm i).le, fun z hz hzm => ?_⟩⟩
    obtain ⟨zs, _, hv, hmax⟩ := vind_attained (hu.cont i) hpos (hmpos i).le
    rw [hu.rep i (x i) z (hx.1 i) hz, huv i, hv]
    exact hmax z hz hzm
  · intro hW
    have hpos := (E.root_pos_pareto (E.root_iff.2 ⟨m, hm, hW⟩)).1
    have huv : ∀ i, u i (x i) = vind (u i) p (m i) := by
      intro i
      obtain ⟨zs, hzs, hv, hmax⟩ := vind_attained (hu.cont i) hpos (hmpos i).le
      obtain ⟨hx0, hxm, hopt⟩ := hW.2.2 i
      rw [hv]
      exact le_antisymm (hmax (x i) hx0 hxm) ((hu.rep i (x i) zs hx0 hzs.1).1 (hopt zs hzs.1 hzs.2))
    have hvpos : ∀ i, 0 < vind (u i) p (m i) := fun i => by
      rw [vind_scale (hu.cont i) (hu.homog i) hpos (hmpos i).le]
      exact mul_pos (hmpos i) (vind_one_pos (hu.cont i) (hu.pos i) hpos)
    refine ⟨⟨hW.1, fun i => (huv i) ▸ hvpos i, hW.2.1, hpos⟩, ?_⟩
    simp only [EG]
    exact Finset.sum_eq_zero fun i _ => by rw [huv i, sub_self, mul_zero]

/-- On the domain, `log vᵢ(p,mᵢ) = log mᵢ − log eᵢ(p)`. -/
lemma EG_eq_expend (hu : E.HomogRep u) {m : N → ℝ} (hmpos : ∀ i, 0 < m i)
    {x : N → K → ℝ} {p : K → ℝ} (hpos : ∀ k, 0 < p k) :
    EG u m x p = ∑ i, m i * (Real.log (m i) - Real.log (expend (u i) p) -
      Real.log (u i (x i))) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨hv1, he⟩ := vind_one_eq (hu.cont i) (hu.homog i) (hu.pos i) hpos
  rw [vind_scale (hu.cont i) (hu.homog i) hpos (hmpos i).le, hv1,
    Real.log_mul (hmpos i).ne' (inv_pos.2 he).ne', Real.log_inv]
  ring

lemma EGDom_convex (hu : E.HomogRep u) : Convex ℝ (E.EGDom u) := by
  rintro ⟨x, p⟩ ⟨hx, hux, hp, hpos⟩ ⟨x', p'⟩ ⟨hx', hux', hp', hpos'⟩ a b ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk]
  refine ⟨⟨fun i k => ?_, fun k => ?_⟩, fun i => ?_, ⟨fun k => ?_, ?_⟩, fun k => ?_⟩
  · simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i k)) (mul_nonneg hb (hx'.1 i k))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hx.2 k) ha
    have h2 := mul_le_mul_of_nonneg_left (hx'.2 k) hb
    have h3 : a * E.W k + b * E.W k = E.W k := by rw [← add_mul, hab, one_mul]
    linarith
  · have hc := (hu.concave i).2 (show x i ∈ {z : K → ℝ | 0 ≤ z} from hx.1 i)
      (show x' i ∈ {z : K → ℝ | 0 ≤ z} from hx'.1 i) ha hb hab
    simp only [smul_eq_mul] at hc
    have h1 := hux i
    have h2 := hux' i
    show 0 < u i (a • x i + b • x' i)
    rcases ha.lt_or_eq with ha' | ha'
    · have := mul_pos ha' h1
      have := mul_nonneg hb h2.le
      linarith
    · have hb1 : b = 1 := by linarith
      rw [← ha', hb1, zero_smul, one_smul, zero_add]
      exact h2
  · simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hp.1 k)) (mul_nonneg hb (hp'.1 k))
  · rw [dot_add_left, dot_smul_left, dot_smul_left, hp.2, hp'.2, mul_one, mul_one, hab]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · have := mul_pos ha' (hpos k)
      have := mul_nonneg hb (hpos' k).le
      linarith
    · have hb1 : b = 1 := by linarith
      rw [← ha', hb1]
      simpa using hpos' k

/-- **Lemma 4**, convexity of the objective on its (convex) domain. -/
theorem lemma4_convex (hu : E.HomogRep u) {m : N → ℝ} (hmpos : ∀ i, 0 < m i) :
    ConvexOn ℝ (E.EGDom u) (fun q => EG u m q.1 q.2) := by
  refine ⟨EGDom_convex hu, ?_⟩
  rintro ⟨x, p⟩ hq ⟨x', p'⟩ hq' a b ha hb hab
  have hmix := EGDom_convex hu hq hq' ha hb hab
  obtain ⟨hx, hux, hp, hpos⟩ := hq
  obtain ⟨hx', hux', hp', hpos'⟩ := hq'
  simp only [Prod.smul_mk, Prod.mk_add_mk] at hmix ⊢
  obtain ⟨_, huxm, _, hposm⟩ := hmix
  rw [EG_eq_expend hu hmpos hpos, EG_eq_expend hu hmpos hpos', EG_eq_expend hu hmpos hposm,
    smul_eq_mul, smul_eq_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨-, he⟩ := vind_one_eq (hu.cont i) (hu.homog i) (hu.pos i) hpos
  obtain ⟨-, he'⟩ := vind_one_eq (hu.cont i) (hu.homog i) (hu.pos i) hpos'
  -- log e is concave in p
  have hE : a * Real.log (expend (u i) p) + b * Real.log (expend (u i) p') ≤
      Real.log (expend (u i) (a • p + b • p')) :=
    (log_comb he he' ha hb hab).trans (Real.log_le_log (by
      rcases ha.lt_or_eq with ha' | ha'
      · have := mul_pos ha' he
        have := mul_nonneg hb he'.le
        linarith
      · have hb1 : b = 1 := by linarith
        rw [← ha', hb1]
        simpa using he') (expend_concave (hu.homog i) (hu.pos i) hp.1 hp'.1 ha hb))
  -- log u is concave in x
  have hU : a * Real.log (u i (x i)) + b * Real.log (u i (x' i)) ≤
      Real.log (u i (a • x i + b • x' i)) := by
    have hc := (hu.concave i).2 (show x i ∈ {z : K → ℝ | 0 ≤ z} from hx.1 i)
      (show x' i ∈ {z : K → ℝ | 0 ≤ z} from hx'.1 i) ha hb hab
    simp only [smul_eq_mul] at hc
    refine (log_comb (hux i) (hux' i) ha hb hab).trans (Real.log_le_log ?_ hc)
    rcases ha.lt_or_eq with ha' | ha'
    · have := mul_pos ha' (hux i)
      have := mul_nonneg hb (hux' i).le
      linarith
    · have hb1 : b = 1 := by linarith
      rw [← ha', hb1]
      simpa using hux' i
  have hm0 := (hmpos i).le
  have h1 := mul_le_mul_of_nonneg_left hE hm0
  have h2 := mul_le_mul_of_nonneg_left hU hm0
  have h3 : a * (m i * Real.log (m i)) + b * (m i * Real.log (m i)) = m i * Real.log (m i) := by
    rw [← add_mul, hab, one_mul]
  show m i * (Real.log (m i) - Real.log (expend (u i) (a • p + b • p')) -
      Real.log (u i ((a • x + b • x') i))) ≤ _
  simp only [Pi.add_apply, Pi.smul_apply]
  nlinarith

end Economy

end Yq
