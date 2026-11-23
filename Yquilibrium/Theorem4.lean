/-
  Yquilibrium (Goeree, 21 Nov 2026), Theorem 4: almost-sure convergence of the stochastic
  dynamic to an individually-rational Yquilibrium.

  Draws are i.i.d. with law `ν` (the infinite product `Measure.infinitePi`). The paper assumes
  that the proposer and the order are random, that the price has full support on the interior
  of `Σ_K(W)`, and that the trade size is drawn independently of the price with full support
  on `(0,1]`. All that the proof uses is `FullSupport` below: every proposer–first-responder
  pair `i ≠ j`, every open set of prices that meets the interior of the simplex and every
  interval of trade sizes in `(0,1]` occur together with positive probability. This follows
  from the paper's assumptions (see `fullSupport_of_indep`), so the theorem below is at least
  as general as Theorem 4.
-/
import Yquilibrium.Measurable
import Yquilibrium.ProbLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ConditionalExpectation

open Finset Set Filter Topology MeasureTheory ProbabilityTheory

noncomputable section

namespace Yq

namespace Economy

variable {K N : Type*} [Fintype K] [Fintype N] [DecidableEq N] {E : Economy N K}
  {u : N → (K → ℝ) → ℝ}

/-- The joint full-support condition on the law of one draw. -/
def FullSupport (E : Economy N K) (ν : Measure (Draw N K)) : Prop :=
  ∀ i j : N, i ≠ j → ∀ V : Set (K → ℝ), IsOpen V → (∃ p ∈ V, (∀ k, 0 < p k) ∧ dot p E.W = 1) →
    ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
      0 < ν {d | d.P = i ∧ d.p ∈ V ∧ d.Δ ∈ Icc a b ∧ d.order.head? = some j}

/-- The information after `t` periods: the σ-algebra of the first `t` draws. -/
def drawFiltration : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → Draw N K)) where
  seq t := ⨆ s ∈ Set.Iio t, MeasurableSpace.comap (fun ω : ℕ → Draw N K => ω s) inferInstance
  mono' a b hab := iSup₂_mono' fun s hs => ⟨s, Set.mem_Iio.2 (lt_of_lt_of_le hs hab), le_rfl⟩
  le' _ := iSup₂_le fun s _ => (measurable_pi_apply s).comap_le

lemma measurable_draw_le (t : ℕ) :
    Measurable[(drawFiltration (N := N) (K := K)) (t + 1)] fun ω : ℕ → Draw N K => ω t :=
  Measurable.of_comap_le (le_iSup₂ (f := fun s (_ : s ∈ Set.Iio (t + 1)) =>
    MeasurableSpace.comap (fun ω : ℕ → Draw N K => ω s) inferInstance) t (Nat.lt_succ_self t))

/-- The state after `t` periods depends only on the first `t` draws. -/
lemma measurable_pathM (hu : E.DynRep u) :
    ∀ t, Measurable[(drawFiltration (N := N) (K := K)) t] fun ω => E.pathM ω t
  | 0 => measurable_const
  | t + 1 => by
    have h1 : Measurable[(drawFiltration (N := N) (K := K)) (t + 1)] fun ω => E.pathM ω t :=
      (measurable_pathM hu t).mono (drawFiltration.mono (Nat.le_succ t)) le_rfl
    exact (measurable_stepM hu).comp (h1.prodMk (measurable_draw_le t))

variable (ν : Measure (Draw N K)) [IsProbabilityMeasure ν]

/-- Almost surely every draw is admissible. -/
lemma ae_valid (hvalid : ∀ᵐ d ∂ν, d.Valid E) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => ν), ∀ t, (ω t).Valid E :=
  ae_all_iff.2 fun t =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) t).quasiMeasurePreserving.ae hvalid

/-- The draw in period `t` is independent of the first `t` draws. -/
lemma indep_draw (t : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : ℕ → Draw N K => ω t) inferInstance)
      ((drawFiltration (N := N) (K := K)) t) (Measure.infinitePi fun _ : ℕ => ν) := by
  have h := (iIndepFun_iff_iIndep _ _ _).1
    (iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ (d : Draw N K) => d)
      fun _ => measurable_id')
  have := indep_iSup_of_disjoint (fun s => (measurable_pi_apply s).comap_le) h
    (S := {t}) (T := Set.Iio t) (by simp)
  simp only [Set.mem_singleton_iff, iSup_iSup_eq_left] at this
  exact this

/-- **Step 2 near one point**: around a non-Pareto-optimal `x̂`, there is an open set that the
  path visits only finitely often, almost surely. -/
theorem finitely_often_near [Nonempty N] [Nonempty K] (hu : E.DynRep u) (hs : E.Smooth u)
    (hvalid : ∀ᵐ d ∂ν, d.Valid E) (hfull : E.FullSupport ν) {xh : N → K → ℝ}
    (hxh : xh ∈ E.pathSet) (hnPO : ¬ E.ParetoOptimal xh) :
    ∃ U : Set (N → K → ℝ), IsOpen U ∧ xh ∈ U ∧
      ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => ν), ∀ᶠ t in atTop, E.pathM ω t ∉ U := by
  classical
  obtain ⟨i, j, hij, ph, hph, hphW, Δ₁, hΔ0, hΔ1, ε, hε, hev⟩ := step1_progress hu hs hxh hnPO
  obtain ⟨U0, hU0, V0, hV0, hUV⟩ := mem_nhds_prod_iff.1 hev
  obtain ⟨U, hUU0, hUo, hxU⟩ := mem_nhds_iff.1 hU0
  obtain ⟨V, hVV0, hVo, hpV⟩ := mem_nhds_iff.1 hV0
  set D : Set (Draw N K) :=
    {d | d.P = i ∧ d.p ∈ V ∧ d.Δ ∈ Icc (Δ₁ / 2) Δ₁ ∧ d.order.head? = some j} with hDdef
  have hD : MeasurableSet D := by
    have : D = {d : Draw N K | d.P ∈ ({i} : Set N)} ∩ (Draw.p ⁻¹' V ∩
        (Draw.Δ ⁻¹' Icc (Δ₁ / 2) Δ₁ ∩ {d : Draw N K | d.order ∈ {l : List N | l.head? = some j}}))
        := by
      ext d
      simp [hDdef]
    rw [this]
    exact (Draw.measurableSet_P _).inter ((Draw.measurable_p hVo.measurableSet).inter
      ((Draw.measurable_Δ measurableSet_Icc).inter (Draw.measurableSet_order _)))
  have hνD : 0 < ν D := hfull i j hij V hVo ⟨ph, hpV, hph, hphW⟩ (Δ₁ / 2) Δ₁ (by linarith)
    (by linarith) hΔ1
  set η := (ν D).toReal with hηdef
  have hη : 0 < η := ENNReal.toReal_pos hνD.ne' (measure_ne_top _ _)
  set μ := Measure.infinitePi fun _ : ℕ => ν with hμdef
  set ℱ := drawFiltration (N := N) (K := K) with hℱdef
  set A : ℕ → Set (ℕ → Draw N K) := fun t => {ω | E.pathM ω t ∈ U} with hAdef
  set B : ℕ → Set (ℕ → Draw N K) := fun t => (fun ω => ω t) ⁻¹' D with hBdef
  have hA : ∀ t, MeasurableSet[ℱ t] (A t) := fun t =>
    measurable_pathM hu t hUo.measurableSet
  have hB : ∀ t, MeasurableSet[ℱ (t + 1)] (B t) := fun t => measurable_draw_le t hD
  refine ⟨U, hUo, hxU, ?_⟩
  apply finitely_often_of_progress (ℱ := ℱ) (fun t ω => totalU u (E.pathM ω t)) A
    (fun t => A t ∩ B t) hA (fun t => ((ℱ.mono (Nat.le_succ t)) _ (hA t)).inter (hB t)) hε hη
  · -- along almost every path, `S` is non-decreasing, bounded, and jumps on `G`
    filter_upwards [ae_valid ν hvalid] with ω hv
    have heq := pathM_eq_path hu hv
    simp only [heq]
    refine ⟨fun a b hab => Finset.sum_le_sum fun i _ => path_monotone hu ω hv i hab, ?_, ?_⟩
    · have hcont : ContinuousOn (totalU u) E.pathSet :=
        continuousOn_finsetSum _ fun i _ =>
          (hu.cont i).comp (continuous_apply i).continuousOn fun x hx => hx.1.1 i
      obtain ⟨b, hb⟩ := isCompact_pathSet.bddAbove_image hcont
      exact ⟨b, by rintro _ ⟨t, rfl⟩; exact hb ⟨_, path_mem hu ω hv t, rfl⟩⟩
    · rintro t ⟨hAt, hBt⟩
      have hAt' : E.path ω t ∈ U := by
        have : E.pathM ω t ∈ U := hAt
        rwa [heq] at this
      obtain ⟨hP, hp, hΔ, hhead⟩ := hBt
      have hr := hUV (show (E.path ω t, (ω t).p) ∈ U0 ×ˢ V0 from ⟨hUU0 hAt', hVV0 hp⟩)
      exact hr (ω t) (hv t) hP rfl hΔ hhead (path_mem hu ω hv t)
  · -- the conditional probability of `G t` given the past is `η` on `A t`
    intro t
    have hAm : MeasurableSet (A t) := (ℱ.le t) _ (hA t)
    have hBm : MeasurableSet (B t) := (measurable_pi_apply t) hD
    have hBm' : MeasurableSet[MeasurableSpace.comap (fun ω : ℕ → Draw N K => ω t)
        inferInstance] (B t) := ⟨D, hD, rfl⟩
    have h1 := condExp_indep_eq (μ := μ) (f := (B t).indicator (1 : (ℕ → Draw N K) → ℝ))
      ((measurable_pi_apply t).comap_le) (ℱ.le t)
      ((stronglyMeasurable_one (α := ℕ → Draw N K) (β := ℝ)).indicator hBm') (indep_draw ν t)
    have h2 := condExp_mul_of_stronglyMeasurable_left (m := ℱ t) (μ := μ)
      (f := (A t).indicator (1 : (ℕ → Draw N K) → ℝ))
      (g := (B t).indicator (1 : (ℕ → Draw N K) → ℝ))
      (stronglyMeasurable_one.indicator (hA t))
      (by
        rw [← Set.inter_indicator_one]
        exact (integrable_const (1 : ℝ)).indicator (hAm.inter hBm))
      ((integrable_const (1 : ℝ)).indicator hBm)
    have hint : ∫ ω, (B t).indicator (1 : (ℕ → Draw N K) → ℝ) ω ∂μ = η := by
      rw [integral_indicator_one hBm, measureReal_def, hηdef,
        (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) t).measure_preimage
          hD.nullMeasurableSet]
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [Set.inter_indicator_one, hω2, Pi.mul_apply, hω1, hint, mul_comm]

/-- **Theorem 4 (convergence).** With i.i.d. draws satisfying the full-support condition, the
  path of the stochastic dynamic converges almost surely to a Pareto-optimal allocation `x*`,
  and `(x*, p*)` is a root and an individually-rational Yquilibrium for some `p* ≫ 0`. -/
theorem theorem4 [Nonempty N] [Nonempty K] (hu : E.DynRep u) (hs : E.Smooth u)
    (hvalid : ∀ᵐ d ∂ν, d.Valid E) (hfull : E.FullSupport ν) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => ν), ∃ xs, Tendsto (E.path ω) atTop (𝓝 xs) ∧
      E.ParetoOptimal xs ∧ ∃ p, (∀ k, 0 < p k) ∧ E.IsRoot xs p ∧ E.IsYqIR xs p := by
  classical
  set I := {xh : N → K → ℝ // xh ∈ E.pathSet ∧ ¬ E.ParetoOptimal xh}
  have hU : ∀ xh : I, ∃ U : Set (N → K → ℝ), IsOpen U ∧ xh.1 ∈ U ∧
      ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => ν), ∀ᶠ t in atTop, E.pathM ω t ∉ U :=
    fun xh => finitely_often_near ν hu hs hvalid hfull xh.2.1 xh.2.2
  choose U hUo hxU hfin using hU
  -- countably many of these open sets cover the non-Pareto-optimal states (Lindelöf)
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  have hallT : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => ν),
      ∀ xh ∈ T, ∀ᶠ t in atTop, E.pathM ω t ∉ U xh :=
    (ae_ball_iff hTc).2 fun xh _ => hfin xh
  filter_upwards [ae_valid ν hvalid, hallT] with ω hv hT
  apply converges_of_cluster_PO hu ω hv
  intro x hx
  by_contra hnPO
  have hxS := (cluster_utility hu ω hv hx).1
  have hxmem : x ∈ ⋃ xh ∈ T, U xh := by
    rw [hTU]
    exact mem_iUnion.2 ⟨⟨x, hxS, hnPO⟩, hxU _⟩
  obtain ⟨xh, hxhT, hxUxh⟩ := mem_iUnion₂.1 hxmem
  have hfreq := mapClusterPt_iff_frequently.1 hx (U xh) ((hUo xh).mem_nhds hxUxh)
  have hev := hT xh hxhT
  simp only [pathM_eq_path hu hv] at hev
  obtain ⟨t, ht1, ht2⟩ := (hfreq.and_eventually hev).exists
  exact ht2 ht1

/-- **The paper's assumptions imply `FullSupport`.** Suppose that, under `ν`, the pair
  (proposer, order), the price and the trade size are independent; that every proposer `i`
  asks any other consumer `j` first with positive probability; that the price has full support
  on the interior of `Σ_K(W)` (every open set meeting it has positive probability); and that
  the trade size has full support on `(0,1]`. Then `ν` satisfies `FullSupport`. -/
theorem fullSupport_of_indep
    (hind1 : Indep (MeasurableSpace.comap (fun d : Draw N K => (d.P, d.order)) ⊤)
      (MeasurableSpace.comap Draw.p inferInstance ⊔ MeasurableSpace.comap Draw.Δ inferInstance)
      ν)
    (hind2 : Indep (MeasurableSpace.comap (Draw.p (N := N) (K := K)) inferInstance)
      (MeasurableSpace.comap Draw.Δ inferInstance) ν)
    (hPO : ∀ i j : N, i ≠ j → 0 < ν {d | d.P = i ∧ d.order.head? = some j})
    (hp : ∀ V : Set (K → ℝ), IsOpen V → (∃ p ∈ V, (∀ k, 0 < p k) ∧ dot p E.W = 1) →
      0 < ν (Draw.p ⁻¹' V))
    (hΔ : ∀ O : Set ℝ, IsOpen O → (O ∩ Ioc 0 1).Nonempty → 0 < ν (Draw.Δ ⁻¹' O)) :
    E.FullSupport ν := by
  intro i j hij V hV hVne a b ha hab hb1
  have hset : {d : Draw N K | d.P = i ∧ d.p ∈ V ∧ d.Δ ∈ Icc a b ∧ d.order.head? = some j} =
      {d | d.P = i ∧ d.order.head? = some j} ∩ (Draw.p ⁻¹' V ∩ Draw.Δ ⁻¹' Icc a b) := by
    ext d
    simp only [mem_setOf_eq, mem_inter_iff, Set.mem_preimage]
    tauto
  have hA : MeasurableSet[MeasurableSpace.comap (fun d : Draw N K => (d.P, d.order)) ⊤]
      {d | d.P = i ∧ d.order.head? = some j} :=
    ⟨{q | q.1 = i ∧ q.2.head? = some j}, MeasurableSpace.measurableSet_top, rfl⟩
  have hB : MeasurableSet[MeasurableSpace.comap (Draw.p (N := N) (K := K)) inferInstance]
      (Draw.p ⁻¹' V) := ⟨V, hV.measurableSet, rfl⟩
  have hC : MeasurableSet[MeasurableSpace.comap (Draw.Δ (N := N) (K := K)) inferInstance]
      (Draw.Δ ⁻¹' Icc a b) := ⟨Icc a b, measurableSet_Icc, rfl⟩
  rw [hset, (Indep_iff _ _ ν).1 hind1 _ _ hA
    ((le_sup_left : _ ≤ _ ⊔ MeasurableSpace.comap Draw.Δ inferInstance) _ hB |>.inter
      ((le_sup_right : _ ≤ MeasurableSpace.comap Draw.p inferInstance ⊔ _) _ hC)),
    (Indep_iff _ _ ν).1 hind2 _ _ hB hC]
  have hC0 : 0 < ν (Draw.Δ ⁻¹' Icc a b) := by
    refine lt_of_lt_of_le (hΔ (Ioo a b) isOpen_Ioo ⟨(a + b) / 2, ⟨by linarith, by linarith⟩,
      by linarith, by linarith⟩) (measure_mono ?_)
    exact preimage_mono Ioo_subset_Icc_self
  exact ENNReal.mul_pos (hPO i j hij).ne' (ENNReal.mul_pos (hp V hV hVne).ne' hC0.ne').ne'

end Economy

end Yq
