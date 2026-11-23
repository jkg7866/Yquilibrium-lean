/-
  Yquilibrium (Goeree, version of 23 Nov 2026), Section 2.3 and Appendix A.
  Theorem 3: duality between the utility possibility set (UPS) and the indirect utility
  possibility set (VPS). The VPS is taken over all prices in `Σ_K(W)`; where a price is zero,
  indirect utility can be infinite, and those points (never on the frontier) are left out.
-/
import Yquilibrium.Welfare2
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Topology.Order.IntermediateValue

open Finset Filter Topology Set

noncomputable section

namespace Yq

variable {K : Type*} [Fintype K]

/-- Indirect utility `v(p,m) = sup {u(z) | z ≥ 0, ⟨p|z⟩ ≤ m}`. -/
def vind (u : (K → ℝ) → ℝ) (p : K → ℝ) (m : ℝ) : ℝ :=
  sSup (u '' {z | 0 ≤ z ∧ dot p z ≤ m})

lemma isCompact_budget {p : K → ℝ} (hp : ∀ k, 0 < p k) (m : ℝ) :
    IsCompact {z : K → ℝ | 0 ≤ z ∧ dot p z ≤ m} := by
  refine (isCompact_univ_pi fun k =>
    isCompact_Icc (a := (0 : ℝ)) (b := m / p k)).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_const continuous_id).inter
      (isClosed_le (continuous_dot_right p) continuous_const)
  · rintro z ⟨hz, hzm⟩ k _
    refine ⟨hz k, ?_⟩
    rw [le_div_iff₀ (hp k)]
    have := mul_le_dot (fun k => (hp k).le) hz k
    linarith

/-- For `p ≫ 0` the indirect utility is attained. -/
lemma vind_attained {u : (K → ℝ) → ℝ} (hu : ContinuousOn u {z | 0 ≤ z}) {p : K → ℝ}
    (hp : ∀ k, 0 < p k) {m : ℝ} (hm : 0 ≤ m) :
    ∃ zs, (0 ≤ zs ∧ dot p zs ≤ m) ∧ vind u p m = u zs ∧
      ∀ z, 0 ≤ z → dot p z ≤ m → u z ≤ u zs := by
  obtain ⟨zs, hzs, hmax⟩ := (isCompact_budget hp m).exists_isMaxOn
    ⟨0, le_rfl, by rw [dot_zero_right]; exact hm⟩ (hu.mono fun z hz => hz.1)
  rw [isMaxOn_iff] at hmax
  refine ⟨zs, hzs, ?_, fun z hz hzm => hmax z ⟨hz, hzm⟩⟩
  exact IsGreatest.csSup_eq ⟨⟨zs, hzs, rfl⟩, by rintro _ ⟨z, hz, rfl⟩; exact hmax z hz⟩

/-- `w` is a maximal element of `S`. -/
def IsMaxIn {N : Type*} (S : Set (N → ℝ)) (w : N → ℝ) : Prop :=
  w ∈ S ∧ ∀ w' ∈ S, w ≤ w' → w' = w

/-- `w` is a minimal element of `S`. -/
def IsMinIn {N : Type*} (S : Set (N → ℝ)) (w : N → ℝ) : Prop :=
  w ∈ S ∧ ∀ w' ∈ S, w' ≤ w → w' = w

namespace Economy

variable {N : Type*} [Fintype N] (E : Economy N K) (u : N → (K → ℝ) → ℝ)

/-- `u` represents the preferences of `E` by continuous and quasiconcave utilities. Monotonicity
  is only that of Section 2 (part of `Pref`): `y ≫ x ⇒ y ≻ x`, and strict monotonicity at
  bundles `x ≻ 0`. -/
structure Represents (E : Economy N K) (u : N → (K → ℝ) → ℝ) : Prop where
  rep : ∀ i z x, 0 ≤ z → 0 ≤ x → ((E.pref i).R z x ↔ u i x ≤ u i z)
  cont : ∀ i, ContinuousOn (u i) {z | 0 ≤ z}
  qc : ∀ i, QuasiconcaveOn ℝ {z : K → ℝ | 0 ≤ z} (u i)

/-- The utility possibility set. -/
def UPS : Set (N → ℝ) := {w | ∃ x, E.Feasible x ∧ w = fun i => u i (x i)}

/-- The budget set `{z ≥ 0 | ⟨p|z⟩ ≤ m}`. -/
def budget (p : K → ℝ) (m : ℝ) : Set (K → ℝ) := {z | 0 ≤ z ∧ dot p z ≤ m}

/-- The indirect utility possibility set: indirect utilities `v(p,m)` for `p ∈ Σ_K(W)` and
  `m ∈ Σ_N`, keeping the vectors whose entries are finite (utility bounded on each budget set).
  Mathlib's `sSup` of a set that is unbounded above is a junk value, not `+∞`, so the infinite
  vectors must be excluded explicitly; they are never minimal in any case. -/
def VPS : Set (N → ℝ) :=
  {w | ∃ p m, p ∈ E.Prices ∧ Incomes m ∧ (∀ i, BddAbove (u i '' budget p (m i))) ∧
    w = fun i => vind (u i) p (m i)}

/-- The VPS over strictly positive prices only (used in the proofs). -/
def VPSpos : Set (N → ℝ) :=
  {w | ∃ p m, p ∈ E.Prices ∧ (∀ k, 0 < p k) ∧ Incomes m ∧ w = fun i => vind (u i) p (m i)}

variable {E u}

lemma isConvex_of_rep (hu : E.Represents u) (i : N) : (E.pref i).IsConvex := by
  intro y hy
  have h := hu.qc i (u i y)
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz, hR⟩
    exact ⟨hz, (hu.rep i z y hz hy).1 hR⟩
  · rintro ⟨hz, h'⟩
    exact ⟨hz, (hu.rep i z y hz hy).2 h'⟩

lemma u_zero_le (hu : E.Represents u) (i : N) {x : K → ℝ} (hx : 0 ≤ x) : u i 0 ≤ u i x :=
  (hu.rep i x 0 hx le_rfl).1 ((E.pref i).weak_mono le_rfl hx)

lemma vind_eq_of_optimal (hu : E.Represents u) (i : N) {p : K → ℝ} {m : ℝ} {x : K → ℝ}
    (hopt : Optimal (E.pref i) p m x) (hpos : ∀ k, 0 < p k) (hm : 0 ≤ m) :
    u i x = vind (u i) p m := by
  obtain ⟨zs, hzs, hv, hmax⟩ := vind_attained (hu.cont i) hpos hm
  rw [hv]
  exact le_antisymm (hmax x hopt.1 hopt.2.1)
    ((hu.rep i x zs hopt.1 hzs.1).1 (hopt.2.2 zs hzs.1 hzs.2))

/-- **Theorem 3, Step 1** (weak duality): if `u(x) ≥ v(p,m)` then `(x,p)` is a Walrasian
  equilibrium for `m` and `u(x) = v(p,m)`. -/
theorem step1 [Nonempty K] (hu : E.Represents u) {x : N → K → ℝ} {p : K → ℝ} {m : N → ℝ}
    (hx : E.Feasible x) (hp : p ∈ E.Prices) (hpos : ∀ k, 0 < p k) (hm : Incomes m)
    (hge : ∀ i, vind (u i) p (m i) ≤ u i (x i)) :
    E.IsWalrasianFor m x p ∧ ∀ i, u i (x i) = vind (u i) p (m i) := by
  have hp0 : 0 ≤ p := fun k => (hpos k).le
  choose zs hzs hv hmax using fun i => vind_attained (hu.cont i) hpos (hm.1 i)
  have hge' : ∀ i, m i ≤ dot p (x i) := by
    intro i
    by_contra h
    push_neg at h
    obtain ⟨δ, hδ, hδm⟩ := exists_shift_lt hp0 h
    have hw0 : (0 : K → ℝ) ≤ fun k => x i k + δ := fun k => by
      have := hx.1 i k
      simp only [Pi.zero_apply] at this ⊢
      linarith
    have h1 : u i (x i) < u i (fun k => x i k + δ) := by
      have hmono := (E.pref i).mono (x i) _ (hx.1 i) fun k => show x i k < x i k + δ by linarith
      exact lt_of_not_ge fun h => hmono ((hu.rep i (x i) _ (hx.1 i) hw0).2 h)
    have h2 := hmax i _ hw0 hδm.le
    have h3 := hge i
    rw [hv i] at h3
    linarith
  have hsum : ∑ i, dot p (x i) ≤ 1 := by
    have := E.sum_dot_le hx hp0
    rw [hp.2] at this
    exact this
  have heq : ∀ i, dot p (x i) = m i := by
    have hz : ∑ i, (dot p (x i) - m i) = 0 := by
      have : ∑ i, (dot p (x i) - m i) ≤ 0 := by
        rw [Finset.sum_sub_distrib, hm.2]
        linarith
      exact le_antisymm this (Finset.sum_nonneg fun i _ => sub_nonneg.2 (hge' i))
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sub_nonneg.2 (hge' i)).1 hz i
      (mem_univ i)
    linarith
  have hval : ∀ i, u i (x i) = vind (u i) p (m i) := by
    intro i
    have h1 := hmax i (x i) (hx.1 i) (heq i).le
    have h2 := hge i
    rw [hv i] at h2 ⊢
    linarith
  refine ⟨⟨hx, hp, fun i => ⟨hx.1 i, (heq i).le, fun z hz hzm => ?_⟩⟩, hval⟩
  rw [hu.rep i (x i) z (hx.1 i) hz, hval i, hv i]
  exact hmax i z hz hzm

/-- Consequence of Step 1: at a Walrasian equilibrium for `m` (with `p ≫ 0`), `u(x) = v(p,m)`
  is maximal in the UPS and minimal in the VPS. -/
theorem walrasian_extremal [Nonempty K] (hu : E.Represents u) {x : N → K → ℝ} {p : K → ℝ}
    {m : N → ℝ} (hW : E.IsWalrasianFor m x p) (hpos : ∀ k, 0 < p k) (hm : Incomes m) :
    (fun i => u i (x i)) = (fun i => vind (u i) p (m i)) ∧
      IsMaxIn (E.UPS u) (fun i => u i (x i)) ∧ IsMinIn (E.VPSpos u) (fun i => u i (x i)) := by
  have hval : ∀ i, u i (x i) = vind (u i) p (m i) :=
    fun i => vind_eq_of_optimal hu i (hW.2.2 i) hpos (hm.1 i)
  refine ⟨funext hval, ⟨⟨x, hW.1, rfl⟩, ?_⟩, ⟨⟨p, m, hW.2.1, hpos, hm, funext hval⟩, ?_⟩⟩
  · rintro _ ⟨y, hy, rfl⟩ hle
    have := (step1 hu hy hW.2.1 hpos hm fun i => (hval i).symm.le.trans (hle i)).2
    funext i
    show u i (y i) = u i (x i)
    rw [this i, hval i]
  · rintro _ ⟨p', m', hp', hpos', hm', rfl⟩ hle
    have := (step1 hu hW.1 hp' hpos' hm' fun i => hle i).2
    funext i
    exact (this i).symm

/-- **Theorem 3, Step 2**: below every point `v(p,m)` of the VPS lies a maximal point of the UPS. -/
theorem step2 [Nonempty N] [Nonempty K] (hu : E.Represents u) {p : K → ℝ} {m : N → ℝ}
    (hp : p ∈ E.Prices) (hm : Incomes m) (hbdd : ∀ i, BddAbove (u i '' budget p (m i))) :
    ∃ x, E.Feasible x ∧ (∀ i, u i (x i) ≤ vind (u i) p (m i)) ∧
      IsMaxIn (E.UPS u) (fun i => u i (x i)) := by
  classical
  have hle_v : ∀ i z, 0 ≤ z → dot p z ≤ m i → u i z ≤ vind (u i) p (m i) :=
    fun i z hz hzm => le_csSup (hbdd i) ⟨z, ⟨hz, hzm⟩, rfl⟩
  have hu0 : ∀ i, u i 0 ≤ vind (u i) p (m i) := fun i =>
    hle_v i 0 le_rfl (by rw [dot_zero_right]; exact hm.1 i)
  have hcontF : ∀ i, ContinuousOn (fun x : N → K → ℝ => u i (x i)) {x | E.Feasible x} :=
    fun i => (hu.cont i).comp (continuous_apply i).continuousOn fun x hx => hx.1 i
  -- the compact set A = {x ∈ F(W) | u(x) ≤ v(p,m)}
  set A := {x : N → K → ℝ | E.Feasible x ∧ ∀ i, u i (x i) ≤ vind (u i) p (m i)} with hAdef
  have hAc : IsCompact A := by
    refine E.isCompact_feasible.of_isClosed_subset ?_ fun x hx => hx.1
    have : A = {x | E.Feasible x} ∩ ⋂ i, ({x | E.Feasible x} ∩
        (fun x : N → K → ℝ => u i (x i)) ⁻¹' Iic (vind (u i) p (m i))) := by
      ext x
      simp only [hAdef, mem_inter_iff, mem_iInter, Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hF, h⟩
        exact ⟨hF, fun i => ⟨hF, h i⟩⟩
      · rintro ⟨hF, h⟩
        exact ⟨hF, fun i => (h i).2⟩
    rw [this]
    exact E.isClosed_feasible.inter (isClosed_iInter fun i =>
      (hcontF i).preimage_isClosed_of_isClosed E.isClosed_feasible isClosed_Iic)
  have h0A : (0 : N → K → ℝ) ∈ A := by
    refine ⟨⟨fun i => le_rfl, fun k => ?_⟩, fun i => ?_⟩
    · simp only [Pi.zero_apply, Finset.sum_const_zero]
      exact E.W_nonneg k
    · exact hu0 i
  obtain ⟨xs, hxsA, hxmax⟩ := hAc.exists_isMaxOn ⟨0, h0A⟩
    (continuousOn_finsetSum Finset.univ fun i _ => (hcontF i).mono fun x hx => hx.1)
  rw [isMaxOn_iff] at hxmax
  refine ⟨xs, hxsA.1, hxsA.2, ?_⟩
  -- x* is weakly Pareto optimal
  have hWPO : E.WeaklyParetoOptimal xs := by
    refine ⟨hxsA.1, ?_⟩
    rintro ⟨y, hyF, hy⟩
    have hy0 : ∀ i, 0 ≤ y i := hyF.1
    have hyimp : ∀ i, u i (xs i) < u i (y i) := fun i => lt_of_not_ge fun h =>
      hy i ((hu.rep i (xs i) (y i) (hxsA.1.1 i) (hy0 i)).2 h)
    by_cases hS : ∃ i0, u i0 (xs i0) < vind (u i0) p (m i0)
    swap
    · -- u(x*) = v(p,m): every yᵢ costs more than mᵢ, so y is not feasible
      push_neg at hS
      have hcost : ∀ i, m i < dot p (y i) := fun i => lt_of_not_ge fun h =>
        absurd (hle_v i (y i) (hy0 i) h)
          (not_le.2 (lt_of_le_of_lt (hS i) (hyimp i)))
      have h1 : ∑ i, m i < ∑ i, dot p (y i) := Finset.sum_lt_sum_of_nonempty
        Finset.univ_nonempty fun i _ => hcost i
      have h2 : ∑ i, dot p (y i) ≤ dot p E.W := by
        rw [← dot_sum_right]
        exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
          (by rw [Finset.sum_apply]; exact hyF.2 k) (hp.1 k)
      rw [hm.2, hp.2] at *
      linarith
    obtain ⟨i0, hi0⟩ := hS
    -- scale each yᵢ down to the level set u = vᵢ when necessary
    have hscale : ∀ i, ∃ t ∈ Icc (0 : ℝ) 1,
        u i (t • y i) = min (u i (y i)) (vind (u i) p (m i)) := by
      intro i
      by_cases hle' : u i (y i) ≤ vind (u i) p (m i)
      · exact ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [one_smul, min_eq_left hle']⟩
      · push_neg at hle'
        have hcont : ContinuousOn (fun t : ℝ => u i (t • y i)) (Icc 0 1) :=
          (hu.cont i).comp (continuous_id.smul continuous_const).continuousOn fun t ht => by
            show (0 : K → ℝ) ≤ _
            intro k
            simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
            exact mul_nonneg ht.1 (hy0 i k)
        have hmem : vind (u i) p (m i) ∈ Icc (u i ((0 : ℝ) • y i)) (u i ((1 : ℝ) • y i)) := by
          rw [zero_smul, one_smul]
          exact ⟨hu0 i, hle'.le⟩
        obtain ⟨t, ht, htv⟩ := intermediate_value_Icc zero_le_one hcont hmem
        have htv' : u i (t • y i) = vind (u i) p (m i) := htv
        exact ⟨t, ht, by rw [htv', min_eq_right hle'.le]⟩
    choose t ht htv using hscale
    have hz0 : ∀ i, 0 ≤ t i • y i := fun i k => by
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (ht i).1 (hy0 i k)
    have hzA : (fun i => t i • y i) ∈ A := by
      refine ⟨⟨hz0, fun k => ?_⟩, fun i => ?_⟩
      · calc ∑ i, (t i • y i) k ≤ ∑ i, y i k := Finset.sum_le_sum fun i _ => by
              simp only [Pi.smul_apply, smul_eq_mul]
              have h1 : 0 ≤ y i k := hy0 i k
              have h2 := (ht i).2
              nlinarith [mul_nonneg (sub_nonneg.2 h2) h1]
          _ ≤ E.W k := hyF.2 k
      · show u i (t i • y i) ≤ _
        rw [htv i]
        exact min_le_right _ _
    have hlt : ∑ i, u i (xs i) < ∑ i, u i (t i • y i) := by
      apply Finset.sum_lt_sum
      · intro i _
        rw [htv i]
        exact le_min (hyimp i).le (hxsA.2 i)
      · exact ⟨i0, mem_univ _, by rw [htv i0]; exact lt_min (hyimp i0) hi0⟩
    have := hxmax _ hzA
    linarith
  -- hence a root, a Walrasian equilibrium, and a maximal point of the UPS
  obtain ⟨p', hroot, hpos', -⟩ := E.corollary1_b_weak (fun i => isConvex_of_rep hu i) hWPO
  obtain ⟨m', hm', hW'⟩ := E.root_iff.1 hroot
  exact (walrasian_extremal hu hW' hpos' hm').2.1

/-- A maximal element of the UPS comes from a Pareto-optimal allocation. -/
lemma pareto_of_max (hu : E.Represents u) {x : N → K → ℝ} (hx : E.Feasible x)
    (hmax : IsMaxIn (E.UPS u) (fun i => u i (x i))) : E.ParetoOptimal x := by
  refine ⟨hx, ?_⟩
  rintro ⟨x', hx', hge, j, hj⟩
  have hle : (fun i => u i (x i)) ≤ fun i => u i (x' i) :=
    fun i => (hu.rep i (x' i) (x i) (hx'.1 i) (hx.1 i)).1 (hge i)
  have heq := hmax.2 _ ⟨x', hx', rfl⟩ hle
  have := congrFun heq j
  exact hj ((hu.rep j (x j) (x' j) (hx.1 j) (hx'.1 j)).2 this.le)

/-- For `p ≫ 0`, utility is bounded on every budget set. -/
lemma bdd_of_pos (hu : E.Represents u) {p : K → ℝ} (hpos : ∀ k, 0 < p k) {m : N → ℝ}
    (hm : Incomes m) (i : N) : BddAbove (u i '' budget p (m i)) := by
  obtain ⟨zs, -, -, hmax⟩ := vind_attained (hu.cont i) hpos (hm.1 i)
  exact ⟨u i zs, by rintro _ ⟨z, ⟨hz, hzm⟩, rfl⟩; exact hmax z hz hzm⟩

lemma max_to_min [Nonempty N] [Nonempty K] (hu : E.Represents u) {w : N → ℝ}
    (h : IsMaxIn (E.UPS u) w) : IsMinIn (E.VPS u) w := by
  obtain ⟨⟨x, hx, rfl⟩, hmax⟩ := h
  have hPO := pareto_of_max hu hx ⟨⟨x, hx, rfl⟩, hmax⟩
  obtain ⟨p, hroot, hpos, _⟩ := E.corollary1_b (fun i => isConvex_of_rep hu i) hPO
  obtain ⟨m, hm, hW⟩ := E.root_iff.1 hroot
  obtain ⟨hval, -, -⟩ := walrasian_extremal hu hW hpos hm
  refine ⟨⟨p, m, hW.2.1, hm, bdd_of_pos hu hpos hm, hval⟩, ?_⟩
  -- below any `v(p',m') ≤ u(x)` lies a maximal point of the UPS, which must be `u(x)`
  rintro _ ⟨p', m', hp', hm', hbdd', rfl⟩ hle
  obtain ⟨xs, -, hxsle, hxsmax⟩ := step2 hu hp' hm' hbdd'
  have heq : (fun i => u i (x i)) = fun i => u i (xs i) :=
    hxsmax.2 _ ⟨x, hx, rfl⟩ fun i => (hxsle i).trans (hle i)
  funext i
  refine le_antisymm (hle i) ?_
  have := congrFun heq i
  rw [this]
  exact hxsle i

/-- **Theorem 3** (duality): with continuous, quasiconcave utilities (monotone as in Section 2),
  `w` is a maximal element of the UPS iff it is a minimal element of the VPS. -/
theorem theorem3 [Nonempty N] [Nonempty K] (hu : E.Represents u) (w : N → ℝ) :
    IsMaxIn (E.UPS u) w ↔ IsMinIn (E.VPS u) w := by
  constructor
  · exact max_to_min hu
  · rintro ⟨⟨p, m, hp, hm, hbdd, rfl⟩, hmin⟩
    obtain ⟨xs, _, hxsle, hxsmax⟩ := step2 hu hp hm hbdd
    have heq := hmin _ (max_to_min hu hxsmax).1 fun i => hxsle i
    rw [← heq]
    exact hxsmax

/-- **Theorem 3**, second part: for `p ≫ 0`, `(p,m)` attains a minimal element of the VPS iff
  `p` is a Walrasian equilibrium price for the income distribution `m`. -/
theorem theorem3_attain [Nonempty N] [Nonempty K] (hu : E.Represents u) {p : K → ℝ}
    {m : N → ℝ} (hp : p ∈ E.Prices) (hpos : ∀ k, 0 < p k) (hm : Incomes m) :
    IsMinIn (E.VPS u) (fun i => vind (u i) p (m i)) ↔ ∃ x, E.IsWalrasianFor m x p := by
  constructor
  · rintro ⟨_, hmin⟩
    obtain ⟨xs, hxsF, hxsle, hxsmax⟩ := step2 hu hp hm (bdd_of_pos hu hpos hm)
    have heq := hmin _ (max_to_min hu hxsmax).1 fun i => hxsle i
    refine ⟨xs, (step1 hu hxsF hp hpos hm fun i => ?_).1⟩
    have := congrFun heq i
    exact this.symm.le
  · rintro ⟨x, hW⟩
    obtain ⟨hval, hmaxx, -⟩ := walrasian_extremal hu hW hpos hm
    rw [← hval]
    exact max_to_min hu hmaxx

end Economy

end Yq
