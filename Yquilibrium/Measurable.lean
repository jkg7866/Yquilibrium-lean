/-
  Yquilibrium (Goeree, 21 Nov 2026), Theorem 4: measurability of the stochastic dynamic.
  Draws carry the σ-algebra that is discrete on the proposer and the order and Borel on the
  price and the trade size. One period of trade is then a measurable map of the state and the
  draw (on non-negative states and strictly positive prices, which is all the path visits),
  so the path at time `t` is measurable with respect to the first `t` draws.
-/
import Yquilibrium.Step1
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

open Finset Set Filter Topology MeasureTheory

noncomputable section

namespace Yq

namespace Economy

variable {K N : Type*} [Fintype K] [Fintype N]

/-! ### The σ-algebra on draws -/

/-- Discrete on the proposer and the order, Borel on the price and the trade size. -/
instance Draw.instMeasurableSpace : MeasurableSpace (Draw N K) :=
  MeasurableSpace.comap Draw.P ⊤ ⊔ MeasurableSpace.comap Draw.p inferInstance ⊔
    MeasurableSpace.comap Draw.Δ inferInstance ⊔ MeasurableSpace.comap Draw.order ⊤

lemma Draw.measurableSet_P (s : Set N) : MeasurableSet {d : Draw N K | d.P ∈ s} :=
  (le_sup_left.trans (le_sup_left.trans le_sup_left) :
    MeasurableSpace.comap (Draw.P (N := N) (K := K)) ⊤ ≤ Draw.instMeasurableSpace) _
    ⟨s, MeasurableSpace.measurableSet_top, rfl⟩

lemma Draw.measurableSet_order (s : Set (List N)) :
    MeasurableSet {d : Draw N K | d.order ∈ s} :=
  (le_sup_right : MeasurableSpace.comap (Draw.order (N := N) (K := K)) ⊤ ≤
    Draw.instMeasurableSpace) _ ⟨s, MeasurableSpace.measurableSet_top, rfl⟩

lemma Draw.measurable_p : Measurable (Draw.p (N := N) (K := K)) :=
  Measurable.of_comap_le (le_sup_right.trans (le_sup_left.trans le_sup_left))

lemma Draw.measurable_Δ : Measurable (Draw.Δ (N := N) (K := K)) :=
  Measurable.of_comap_le (le_sup_right.trans le_sup_left)

/-! ### Two measurability tools -/

/-- A map that, on each fibre of a countable classifier, agrees with a measurable map is
  measurable. -/
lemma measurable_cases {α γ ι : Type*} [MeasurableSpace α] [MeasurableSpace γ] [Countable ι]
    (c : α → ι) (hc : ∀ i, MeasurableSet {a | c a = i}) (F : ι → α → γ)
    (hF : ∀ i, Measurable (F i)) : Measurable fun a => F (c a) a := by
  intro T hT
  have : (fun a => F (c a) a) ⁻¹' T = ⋃ i, {a | c a = i} ∩ F i ⁻¹' T := by
    ext a
    simp only [Set.mem_preimage, mem_iUnion, mem_inter_iff, mem_setOf_eq]
    exact ⟨fun h => ⟨c a, rfl, h⟩, fun ⟨i, hi, h⟩ => by rw [hi]; exact h⟩
  rw [this]
  exact MeasurableSet.iUnion fun i => (hc i).inter (hF i hT)

lemma measurable_update_fun [DecidableEq N] {α : Type*} [MeasurableSpace α]
    {f : α → N → K → ℝ} {g : α → K → ℝ} (hf : Measurable f) (hg : Measurable g) (i : N) :
    Measurable fun a => Function.update (f a) i (g a) := by
  rw [measurable_pi_iff]
  intro j
  by_cases h : j = i
  · subst h
    simp only [Function.update_self]
    exact hg
  · simp only [Function.update_of_ne h]
    exact (measurable_pi_apply j).comp hf

/-! ### Measurable versions of demand and utility -/

variable {E : Economy N K} {u : N → (K → ℝ) → ℝ}

open Classical in
/-- Demand, set to zero outside `p ≫ 0, m ≥ 0` (where the dynamic never evaluates it). -/
def demandM (E : Economy N K) (i : N) (q : (K → ℝ) × ℝ) : K → ℝ :=
  if (∀ k, 0 < q.1 k) ∧ 0 ≤ q.2 then E.demand i q.1 q.2 else 0

lemma demandM_eq {i : N} {p : K → ℝ} {m : ℝ} (hp : ∀ k, 0 < p k) (hm : 0 ≤ m) :
    E.demandM i (p, m) = E.demand i p m := by
  simp only [demandM, if_pos (And.intro hp hm)]

omit [Fintype N] in
/-- At zero income and strictly positive prices, the only affordable bundle is zero. -/
lemma optimal_zero {P : Pref K} {p z : K → ℝ} (hp : ∀ k, 0 < p k) (h : Optimal P p 0 z) :
    z = 0 := by
  obtain ⟨hz0, hzm, -⟩ := h
  have hterm : ∀ k ∈ (univ : Finset K), 0 ≤ p k * z k := fun k _ =>
    mul_nonneg (hp k).le (hz0 k)
  have hsum : ∑ k, p k * z k = 0 := le_antisymm hzm (Finset.sum_nonneg hterm)
  funext k
  have := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 hsum k (mem_univ k)
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (hp k).ne'
  · exact h

lemma measurable_demandM (hu : E.DynRep u) (i : N) : Measurable (E.demandM i) := by
  classical
  set O : Set ((K → ℝ) × ℝ) := {q | (∀ k, 0 < q.1 k) ∧ 0 < q.2} with hOdef
  have hO : IsOpen O := by
    have : O = (⋂ k, {q : (K → ℝ) × ℝ | 0 < q.1 k}) ∩ {q | 0 < q.2} := by
      ext q
      simp [hOdef]
    rw [this]
    exact (isOpen_iInter_of_finite fun k =>
      isOpen_lt continuous_const ((continuous_apply k).comp
        (continuous_fst : Continuous fun q : (K → ℝ) × ℝ => q.1))).inter
      (isOpen_lt continuous_const continuous_snd)
  have heq : E.demandM i = O.piecewise (fun q => E.demand i q.1 q.2) 0 := by
    funext q
    by_cases hq : q ∈ O
    · rw [piecewise_eq_of_mem _ _ _ hq, demandM, if_pos ⟨hq.1, hq.2.le⟩]
    · rw [piecewise_eq_of_notMem _ _ _ hq, demandM]
      split_ifs with h
      · have hm0 : q.2 = 0 := le_antisymm (not_lt.1 fun h' => hq ⟨h.1, h'⟩) h.2
        have hopt := demand_spec hu i h.1 h.2
        rw [hm0] at hopt
        rw [hm0]
        exact optimal_zero h.1 hopt
      · rfl
  rw [heq]
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hO.measurableSet
  intro q hq
  exact (demand_continuousAt hu i hq.1 hq.2).continuousWithinAt

/-- A globally continuous version of the utility, equal to `u i` on non-negative bundles. -/
def uM (u : N → (K → ℝ) → ℝ) (i : N) (z : K → ℝ) : ℝ := u i (z ⊔ 0)

omit [Fintype N] in
lemma uM_eq {i : N} {z : K → ℝ} (hz : 0 ≤ z) : uM u i z = u i z := by
  simp [uM, sup_eq_left.2 hz]

lemma continuous_uM (hu : E.DynRep u) (i : N) : Continuous (uM u i) :=
  (hu.cont i).comp_continuous (continuous_id.sup continuous_const) fun z =>
    (le_sup_right : (0 : K → ℝ) ≤ z ⊔ 0)

/-! ### One period of trade as a measurable map -/

/-- The proposer's excess demand, computed with `demandM`. -/
def excM (E : Economy N K) (s : (N → K → ℝ) × Draw N K) : K → ℝ :=
  E.demandM s.2.P (s.2.p, dot s.2.p (s.1 s.2.P)) - s.1 s.2.P

/-- The responder's bundle after the trade. -/
def bM (E : Economy N K) (s : (N → K → ℝ) × Draw N K) (j : N) : K → ℝ :=
  s.1 j - s.2.Δ • E.excM s

/-- States with non-negative bundles and strictly positive prices. -/
def G0 : Set ((N → K → ℝ) × Draw N K) := {s | (∀ i, 0 ≤ s.1 i) ∧ ∀ k, 0 < s.2.p k}

lemma measurableSet_P_eq (i : N) : MeasurableSet {s : (N → K → ℝ) × Draw N K | s.2.P = i} :=
  measurable_snd (Draw.measurableSet_P {i})

lemma measurable_snd_p : Measurable fun s : (N → K → ℝ) × Draw N K => s.2.p :=
  Draw.measurable_p.comp measurable_snd

lemma measurable_snd_Δ : Measurable fun s : (N → K → ℝ) × Draw N K => s.2.Δ :=
  Draw.measurable_Δ.comp measurable_snd

lemma measurableSet_G0 : MeasurableSet (G0 : Set ((N → K → ℝ) × Draw N K)) := by
  have : (G0 : Set ((N → K → ℝ) × Draw N K)) =
      (⋂ i, {s | 0 ≤ s.1 i}) ∩ ⋂ k, {s | 0 < s.2.p k} := by
    ext s
    simp [G0]
  rw [this]
  exact (MeasurableSet.iInter fun i => measurableSet_le measurable_const
    ((measurable_pi_apply i).comp measurable_fst)).inter
    (MeasurableSet.iInter fun k => measurableSet_lt measurable_const
      ((measurable_pi_apply k).comp (measurable_snd_p (N := N) (K := K))))

lemma measurable_excM (hu : E.DynRep u) : Measurable E.excM := by
  have h := measurable_cases (fun s : (N → K → ℝ) × Draw N K => s.2.P) measurableSet_P_eq
    (fun i s => E.demandM i (s.2.p, dot s.2.p (s.1 i)) - s.1 i) fun i => by
      have hx : Measurable fun s : (N → K → ℝ) × Draw N K => s.1 i :=
        (measurable_pi_apply i).comp measurable_fst
      exact ((measurable_demandM hu i).comp (measurable_snd_p.prodMk
        (dot_continuous_pair.measurable.comp (measurable_snd_p.prodMk hx)))).sub hx
  exact h

lemma measurable_bM (hu : E.DynRep u) (j : N) : Measurable fun s => E.bM s j :=
  ((measurable_pi_apply j).comp measurable_fst).sub
    (measurable_snd_Δ.smul (measurable_excM hu))

lemma excess_eq_excM {s : (N → K → ℝ) × Draw N K} (hs : s ∈ G0) :
    E.excess s.1 s.2 = E.excM s := by
  simp only [excess, excM]
  rw [demandM_eq hs.2 (dot_nonneg (fun k => (hs.2 k).le) (hs.1 _))]

/-- Acceptance, written with the continuous utilities. -/
def AccM (E : Economy N K) (u : N → (K → ℝ) → ℝ) (s : (N → K → ℝ) × Draw N K) (j : N) :
    Prop :=
  j ≠ s.2.P ∧ 0 ≤ E.bM s j ∧ uM u j (s.1 j) < uM u j (E.bM s j)

lemma accepts_iff (hu : E.DynRep u) {s : (N → K → ℝ) × Draw N K} (hs : s ∈ G0) (j : N) :
    E.Accepts s.1 s.2 j = true ↔ E.AccM u s j := by
  simp only [Accepts, decide_eq_true_eq, excess_eq_excM hs, AccM, bM]
  have hx : 0 ≤ s.1 j := hs.1 j
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [uM_eq hx, uM_eq h2]
    exact not_le.1 fun h => h3 ((hu.rep j (s.1 j) _ hx h2).2 h)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [uM_eq hx, uM_eq h2] at h3
    exact fun h => absurd ((hu.rep j (s.1 j) _ hx h2).1 h) (not_le.2 h3)

lemma measurableSet_AccM (hu : E.DynRep u) (j : N) : MeasurableSet {s | E.AccM u s j} := by
  have : {s | E.AccM u s j} = {s : (N → K → ℝ) × Draw N K | s.2.P = j}ᶜ ∩
      ({s | 0 ≤ E.bM s j} ∩ {s | uM u j (s.1 j) < uM u j (E.bM s j)}) := by
    ext s
    simp only [AccM, mem_setOf_eq, mem_inter_iff, mem_compl_iff]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨fun h => h1 h.symm, h2, h3⟩,
      fun ⟨h1, h2, h3⟩ => ⟨fun h => h1 h.symm, h2, h3⟩⟩
  rw [this]
  exact (measurableSet_P_eq j).compl.inter
    ((measurableSet_le measurable_const (measurable_bM hu j)).inter
      (measurableSet_lt ((continuous_uM hu j).measurable.comp
        ((measurable_pi_apply j).comp measurable_fst))
        ((continuous_uM hu j).measurable.comp (measurable_bM hu j))))

lemma measurableSet_find (hu : E.DynRep u) (l : List N) (o : Option N) :
    MeasurableSet {s : (N → K → ℝ) × Draw N K |
      s ∈ G0 ∧ l.find? (E.Accepts s.1 s.2) = o} := by
  induction l generalizing o with
  | nil =>
    rcases o with _ | r
    · simpa using measurableSet_G0
    · simp
  | cons a l ih =>
    have : {s : (N → K → ℝ) × Draw N K | s ∈ G0 ∧ (a :: l).find? (E.Accepts s.1 s.2) = o} =
        (({s | s ∈ G0} ∩ {s | E.AccM u s a}) ∩ {_s | some a = o}) ∪
          (({s | s ∈ G0} ∩ {s | E.AccM u s a}ᶜ) ∩
            {s | s ∈ G0 ∧ l.find? (E.Accepts s.1 s.2) = o}) := by
      ext s
      simp only [mem_setOf_eq, mem_union, mem_inter_iff, mem_compl_iff]
      by_cases hs : s ∈ G0
      · by_cases ha : E.AccM u s a
        · have hacc := (accepts_iff hu hs a).2 ha
          simp [List.find?_cons, hacc, hs, ha]
        · have hacc : E.Accepts s.1 s.2 a = false := by
            rw [← Bool.not_eq_true]
            exact fun h => ha ((accepts_iff hu hs a).1 h)
          simp [List.find?_cons, hacc, hs, ha]
      · simp [hs]
    rw [this]
    exact ((measurableSet_G0.inter (measurableSet_AccM hu a)).inter (MeasurableSet.const _)).union
      ((measurableSet_G0.inter (measurableSet_AccM hu a).compl).inter (ih o))

lemma measurableSet_responder (hu : E.DynRep u) (o : Option N) :
    MeasurableSet {s : (N → K → ℝ) × Draw N K | s ∈ G0 ∧ E.responder s.1 s.2 = o} := by
  have : {s : (N → K → ℝ) × Draw N K | s ∈ G0 ∧ E.responder s.1 s.2 = o} =
      ⋃ l : List N, {s | s.2.order = l} ∩ {s | s ∈ G0 ∧ l.find? (E.Accepts s.1 s.2) = o} := by
    ext s
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff, responder]
    exact ⟨fun h => ⟨s.2.order, rfl, h⟩, fun ⟨l, hl, h⟩ => hl ▸ h⟩
  rw [this]
  exact MeasurableSet.iUnion fun l =>
    (measurable_snd (Draw.measurableSet_order {l})).inter (measurableSet_find hu l o)

variable [DecidableEq N]

open Classical in
/-- One period of trade on states with non-negative bundles and positive prices; elsewhere
  (never reached along the path) nothing happens. -/
def stepM (E : Economy N K) (s : (N → K → ℝ) × Draw N K) : N → K → ℝ :=
  if s ∈ G0 then E.step s.1 s.2 else s.1

/-- The bundles after the trade, written with `excM`. -/
def tradeM (E : Economy N K) (r : N) (s : (N → K → ℝ) × Draw N K) : N → K → ℝ :=
  Function.update (Function.update s.1 s.2.P (s.1 s.2.P + s.2.Δ • E.excM s)) r
    (s.1 r - s.2.Δ • E.excM s)

lemma measurable_tradeM (hu : E.DynRep u) (r : N) : Measurable (E.tradeM r) := by
  have hinner := measurable_cases (fun s : (N → K → ℝ) × Draw N K => s.2.P)
    measurableSet_P_eq (fun i s => Function.update s.1 i (s.1 i + s.2.Δ • E.excM s)) fun i =>
      measurable_update_fun measurable_fst
        (((measurable_pi_apply i).comp measurable_fst).add
          (measurable_snd_Δ.smul (measurable_excM hu))) i
  exact measurable_update_fun hinner (measurable_bM hu r) r

open Classical in
lemma measurable_stepM (hu : E.DynRep u) : Measurable E.stepM := by
  set c : (N → K → ℝ) × Draw N K → Option N :=
    fun s => if s ∈ G0 then E.responder s.1 s.2 else none with hcdef
  set F : Option N → (N → K → ℝ) × Draw N K → N → K → ℝ :=
    fun o s => match o with
      | none => s.1
      | some r => E.tradeM r s with hFdef
  have heq : E.stepM = fun s => F (c s) s := by
    funext s
    by_cases hs : s ∈ G0
    · rcases hr : E.responder s.1 s.2 with _ | r
      · simp only [stepM, if_pos hs, hcdef, hFdef, step, hr]
      · simp only [stepM, if_pos hs, hcdef, hFdef, step, hr, tradeM, excess_eq_excM hs]
    · simp only [stepM, if_neg hs, hcdef, hFdef]
  rw [heq]
  refine measurable_cases c (fun o => ?_) F fun o => ?_
  · have : {s | c s = o} = {s | s ∈ G0 ∧ E.responder s.1 s.2 = o} ∪
        ((G0 : Set ((N → K → ℝ) × Draw N K))ᶜ ∩ {_s | none = o}) := by
      ext s
      by_cases hs : s ∈ G0 <;> simp [hcdef, hs]
    rw [this]
    exact (measurableSet_responder hu o).union
      (measurableSet_G0.compl.inter (MeasurableSet.const _))
  · rcases o with _ | r
    · exact measurable_fst
    · exact measurable_tradeM hu r

/-- The path computed with `stepM`. -/
def pathM (E : Economy N K) (ω : ℕ → Draw N K) : ℕ → N → K → ℝ
  | 0 => E.ω
  | t + 1 => E.stepM (E.pathM ω t, ω t)

lemma pathM_eq_path (hu : E.DynRep u) {ω : ℕ → Draw N K} (hω : ∀ t, (ω t).Valid E) :
    ∀ t, E.pathM ω t = E.path ω t
  | 0 => rfl
  | t + 1 => by
    have hG : (E.path ω t, ω t) ∈ (G0 : Set ((N → K → ℝ) × Draw N K)) :=
      ⟨(path_exact hu ω hω t).1, (hω t).1⟩
    show E.stepM (E.pathM ω t, ω t) = E.step (E.path ω t) (ω t)
    rw [pathM_eq_path hu hω t]
    exact if_pos hG

end Economy

end Yq
