/-
  Yquilibrium (Goeree, version of 23 Nov 2026), Theorem 4, part 2: the deterministic half of convergence.
  If every limit point of the path is Pareto optimal, the path converges, and its limit is an
  individually-rational Yquilibrium (Steps 2–3 of the proof, minus the probabilistic part).
-/
import Yquilibrium.Dynamic

open Finset Set Filter Topology

noncomputable section

namespace Yq

namespace Economy

variable {K N : Type*} [Fintype K] [Fintype N] [DecidableEq N] {E : Economy N K}
  {u : N → (K → ℝ) → ℝ}

/-- Strictly quasiconcave utilities give convex preferences. -/
lemma DynRep.isConvex (hu : E.DynRep u) (i : N) : (E.pref i).IsConvex := by
  intro y hy z hz z' hz' a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hz0 : 0 ≤ z := hz.1
  have hz0' : 0 ≤ z' := hz'.1
  have hmix0 : 0 ≤ a • z + (1 - a) • z' := fun k => by
    simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hz0 k)) (mul_nonneg hb (hz0' k))
  refine ⟨hmix0, (hu.rep i _ y hmix0 hy).2 ?_⟩
  have h1 := (hu.rep i z y hz0 hy).1 hz.2
  have h2 := (hu.rep i z' y hz0' hy).1 hz'.2
  exact (le_min h1 h2).trans (hu.qc i hz0 hz0' ha (by linarith))

lemma Exact.feasible {x : N → K → ℝ} (h : E.Exact x) : E.Feasible x :=
  ⟨h.1, fun k => (h.2 k).le⟩

/-- The closed set of exact, individually-rational states, which contains the whole path. -/
def pathSet (E : Economy N K) : Set (N → K → ℝ) :=
  {x | E.Exact x} ∩ ⋂ i, (fun x : N → K → ℝ => x i) ⁻¹' {z | 0 ≤ z ∧ (E.pref i).R z (E.ω i)}

lemma isClosed_pathSet : IsClosed E.pathSet := by
  have h1 : IsClosed {x : N → K → ℝ | E.Exact x} := by
    have ha : IsClosed {x : N → K → ℝ | ∀ i, 0 ≤ x i} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have hb : IsClosed {x : N → K → ℝ | ∀ k, ∑ i, x i k = E.W k} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun k => isClosed_eq
        (continuous_finsetSum _ fun i _ => (continuous_apply k).comp (continuous_apply i))
        continuous_const
    exact ha.inter hb
  exact h1.inter (isClosed_iInter fun i =>
    ((E.pref i).upper_closed _ (E.ω_nonneg i)).preimage (continuous_apply i))

lemma isCompact_pathSet : IsCompact E.pathSet :=
  E.isCompact_feasible.of_isClosed_subset isClosed_pathSet fun _ hx => hx.1.feasible

lemma path_mem (hu : E.DynRep u) (ω : ℕ → Draw N K) (hω : ∀ t, (ω t).Valid E) (t : ℕ) :
    E.path ω t ∈ E.pathSet := by
  refine ⟨path_exact hu ω hω t, Set.mem_iInter.2 fun i => ?_⟩
  exact ⟨(path_exact hu ω hω t).1 i, path_IR hu ω hω t i⟩

/-- Along the path, each utility converges (it is non-decreasing and bounded). -/
lemma utility_tendsto (hu : E.DynRep u) (ω : ℕ → Draw N K) (hω : ∀ t, (ω t).Valid E) (i : N) :
    Tendsto (fun t => u i (E.path ω t i)) atTop (𝓝 (⨆ t, u i (E.path ω t i))) := by
  apply tendsto_atTop_ciSup (path_monotone hu ω hω i)
  have hcont : ContinuousOn (fun x : N → K → ℝ => u i (x i)) E.pathSet :=
    (hu.cont i).comp (continuous_apply i).continuousOn fun x hx => hx.1.1 i
  obtain ⟨b, hb⟩ := isCompact_pathSet.bddAbove_image hcont
  exact ⟨b, by rintro _ ⟨t, rfl⟩; exact hb ⟨_, path_mem hu ω hω t, rfl⟩⟩

/-- Every limit point of the path has the limiting utilities. -/
lemma cluster_utility (hu : E.DynRep u) (ω : ℕ → Draw N K) (hω : ∀ t, (ω t).Valid E)
    {x : N → K → ℝ} (hx : MapClusterPt x atTop (E.path ω)) :
    x ∈ E.pathSet ∧ ∀ i, u i (x i) = ⨆ t, u i (E.path ω t i) := by
  obtain ⟨ψ, hψ, hlim⟩ := hx.tendsto_subseq
  have hxS : x ∈ E.pathSet :=
    isClosed_pathSet.mem_of_tendsto hlim (Eventually.of_forall fun n => path_mem hu ω hω _)
  refine ⟨hxS, fun i => ?_⟩
  have h1 : Tendsto (fun n => u i (E.path ω (ψ n) i)) atTop (𝓝 (u i (x i))) := by
    apply ((hu.cont i) (x i) (hxS.1.1 i)).tendsto.comp
    rw [tendsto_nhdsWithin_iff]
    exact ⟨((continuous_apply i).tendsto (x)).comp hlim,
      Eventually.of_forall fun n => (path_exact hu ω hω (ψ n)).1 i⟩
  have h2 := (utility_tendsto hu ω hω i).comp hψ.tendsto_atTop
  exact tendsto_nhds_unique h1 h2

/-- Two Pareto-optimal limit points coincide (they have the same utilities, and strict
  quasiconcavity would otherwise make their midpoint a Pareto improvement). -/
lemma cluster_unique (hu : E.DynRep u) (ω : ℕ → Draw N K) (hω : ∀ t, (ω t).Valid E)
    {x y : N → K → ℝ} (hx : MapClusterPt x atTop (E.path ω))
    (hy : MapClusterPt y atTop (E.path ω)) (hxPO : E.ParetoOptimal x) : x = y := by
  obtain ⟨hxS, hxu⟩ := cluster_utility hu ω hω hx
  obtain ⟨hyS, hyu⟩ := cluster_utility hu ω hω hy
  have hequ : ∀ i, u i (x i) = u i (y i) := fun i => (hxu i).trans (hyu i).symm
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hx0 : ∀ i, 0 ≤ x i := hxS.1.1
  have hy0 : ∀ i, 0 ≤ y i := hyS.1.1
  set z : N → K → ℝ := fun i => (1 / 2 : ℝ) • x i + (1 - 1 / 2 : ℝ) • y i with hzdef
  have hz0 : ∀ i, 0 ≤ z i := fun i k => by
    simp only [hzdef, Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx0 i k
    have := hy0 i k
    simp only [Pi.zero_apply] at *
    linarith
  have hzF : E.Feasible z := by
    refine ⟨hz0, fun k => ?_⟩
    simp only [hzdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hxS.1.2 k, hyS.1.2 k]
    linarith
  have hzge : ∀ i, u i (x i) ≤ u i (z i) := fun i => by
    have := hu.qc i (hx0 i) (hy0 i) (a := 1 / 2) (by norm_num) (by norm_num)
    rwa [← hequ i, min_self] at this
  have hzj : u j (x j) < u j (z j) := by
    have := hu.sqc j (x j) (y j) (hx0 j) (hy0 j) hj (1 / 2) (by norm_num) (by norm_num)
    rwa [← hequ j, min_self] at this
  exact hxPO.2 ⟨z, hzF, fun i => (hu.rep i (z i) (x i) (hz0 i) (hx0 i)).2 (hzge i),
    j, fun h => absurd ((hu.rep j (x j) (z j) (hx0 j) (hz0 j)).1 h) (not_le.2 hzj)⟩

/-- **Theorem 4, deterministic part**: if every limit point of the path is Pareto optimal, the
  path converges to a Pareto-optimal allocation `x*`, and `(x*, p*)` is a root and an
  individually-rational Yquilibrium for some `p* ≫ 0`. -/
theorem converges_of_cluster_PO [Nonempty N] [Nonempty K] (hu : E.DynRep u)
    (ω : ℕ → Draw N K) (hω : ∀ t, (ω t).Valid E)
    (hPO : ∀ x, MapClusterPt x atTop (E.path ω) → E.ParetoOptimal x) :
    ∃ xs, Tendsto (E.path ω) atTop (𝓝 xs) ∧ E.ParetoOptimal xs ∧
      ∃ p, (∀ k, 0 < p k) ∧ E.IsRoot xs p ∧ E.IsYqIR xs p := by
  obtain ⟨x0, hx0S, hx0⟩ := isCompact_pathSet.exists_mapClusterPt
    (f := atTop) (tendsto_principal.2 (Eventually.of_forall (path_mem hu ω hω)))
  have hlim : Tendsto (E.path ω) atTop (𝓝 x0) :=
    isCompact_pathSet.tendsto_nhds_of_unique_mapClusterPt
      (Eventually.of_forall (path_mem hu ω hω))
      fun x _ hx => (cluster_unique hu ω hω hx hx0 (hPO x hx))
  have hPO0 := hPO x0 hx0
  obtain ⟨p, hroot, hpos, -⟩ := E.corollary1_b (fun i => hu.isConvex i) hPO0
  have hIR : E.IR x0 := fun i => (Set.mem_iInter.1 hx0S.2 i).2
  refine ⟨x0, hlim, hPO0, p, hpos, hroot, hroot.1, hIR, hroot.2.1, fun x' p' hx' _ hp' => ?_⟩
  rw [hroot.2.2]
  exact E.Y_nonneg hx' hp'

end Economy

end Yq
