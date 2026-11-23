/-
  Yquilibrium (Goeree, 21 Nov 2026), Theorem 2(c): with convex preferences, the potential has a
  root at every income distribution `m ∈ Σ_N`.

  The paper derives this from the Arrow–Debreu existence theorem. Mathlib has no fixed-point
  theorem of Brouwer or Kakutani type, so we take **Kakutani's fixed-point theorem** as an
  explicit hypothesis (`Kakutani V`, a true theorem for every finite-dimensional real vector
  space `V`) and prove the rest. Since incomes `mᵢ` are fixed, the economy is a Fisher market:
  consumers choose from budget sets truncated to a box, a "price player" maximizes the value of
  aggregate demand, and a fixed point of the joint best response is a Walrasian equilibrium for
  `m`, hence a root with `⟨p|xᵢ⟩ = mᵢ`.
-/
import Yquilibrium.Welfare2

open Finset Set Filter Topology

noncomputable section

namespace Yq

/-- **Kakutani's fixed-point theorem** for the space `V`: a correspondence on a non-empty
  compact convex set with non-empty convex values and a closed graph has a fixed point. -/
def Kakutani (V : Type*) [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] : Prop :=
  ∀ (S : Set V) (φ : V → Set V), S.Nonempty → IsCompact S → Convex ℝ S →
    (∀ x ∈ S, (φ x).Nonempty ∧ φ x ⊆ S ∧ Convex ℝ (φ x)) →
    IsClosed {q : V × V | q.1 ∈ S ∧ q.2 ∈ φ q.1} → ∃ x ∈ S, x ∈ φ x

variable {K : Type*} [Fintype K]

lemma continuous_dot_fun {α : Type*} [TopologicalSpace α] {f g : α → K → ℝ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun a => dot (f a) (g a) :=
  continuous_finsetSum _ fun k _ => ((continuous_apply k).comp hf).mul ((continuous_apply k).comp hg)

lemma dot_add_right (p z w : K → ℝ) : dot p (z + w) = dot p z + dot p w := by
  simp [dot, mul_add, Finset.sum_add_distrib]

/-- A preference attains a maximum on a non-empty compact set of bundles. -/
lemma Pref.exists_max (P : Pref K) {C : Set (K → ℝ)} (hC : IsCompact C) (hne : C.Nonempty)
    (h0 : ∀ z ∈ C, 0 ≤ z) : ∃ z ∈ C, ∀ w ∈ C, P.R z w := by
  classical
  have hfin : ∀ u : Finset C, ∃ z ∈ C, ∀ w ∈ u, P.R z w.1 := by
    intro u
    induction u using Finset.induction_on with
    | empty => obtain ⟨c, hc⟩ := hne; exact ⟨c, hc, by simp⟩
    | insert a u _ ih =>
      obtain ⟨z, hz, hzu⟩ := ih
      rcases P.total z a.1 (h0 z hz) (h0 a.1 a.2) with h | h
      · refine ⟨z, hz, fun w hw => ?_⟩
        rcases Finset.mem_insert.1 hw with rfl | hw
        · exact h
        · exact hzu w hw
      · refine ⟨a.1, a.2, fun w hw => ?_⟩
        rcases Finset.mem_insert.1 hw with rfl | hw
        · exact P.refl (h0 _ w.2)
        · exact P.trans _ _ _ (h0 _ a.2) (h0 z hz) (h0 _ w.2) h (hzu w hw)
  obtain ⟨z, hzC, hz⟩ := hC.inter_iInter_nonempty (fun w : C => {z | 0 ≤ z ∧ P.R z w.1})
    (fun w => P.upper_closed _ (h0 _ w.2)) fun u => by
      obtain ⟨z, hz, hzu⟩ := hfin u
      exact ⟨z, hz, Set.mem_iInter₂.2 fun w hw => ⟨h0 z hz, hzu w hw⟩⟩
  exact ⟨z, hzC, fun w hw => (Set.mem_iInter.1 hz ⟨w, hw⟩).2⟩

namespace Economy

variable {N : Type*} [Fintype N] (E : Economy N K)

lemma convex_prices : Convex ℝ E.Prices := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun k => ?_, ?_⟩
  · have := hp.1 k
    have := hq.1 k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at *
    positivity
  · rw [dot_add_left, dot_smul_left, dot_smul_left, hp.2, hq.2]
    linarith

/-- The box `0 ≤ z ≤ 2W` to which budget sets are truncated. -/
def box : Set (K → ℝ) := Icc 0 ((2 : ℝ) • E.W)

open Classical in
/-- Consumer `i`'s truncated demand: for `mᵢ > 0`, the best bundles in the box among those
  costing at most `mᵢ` (compared with all bundles costing strictly less); for `mᵢ = 0`, zero. -/
def tdem (m : N → ℝ) (i : N) (p : K → ℝ) : Set (K → ℝ) :=
  {z | if 0 < m i then z ∈ E.box ∧ dot p z ≤ m i ∧
      ∀ w ∈ E.box, dot p w < m i → (E.pref i).R z w else z = 0}

/-- The price player's best response: prices maximizing the value of aggregate demand. -/
def pbest (x : N → K → ℝ) : Set (K → ℝ) :=
  {p | p ∈ E.Prices ∧ ∀ p' ∈ E.Prices, dot p' (∑ i, x i) ≤ dot p (∑ i, x i)}

/-- The joint best-response correspondence. -/
def bestResp (m : N → ℝ) (q : (N → K → ℝ) × (K → ℝ)) : Set ((N → K → ℝ) × (K → ℝ)) :=
  (Set.univ.pi fun i => E.tdem m i q.2) ×ˢ E.pbest q.1

/-- The domain: allocations in the box and normalized prices. -/
def dom : Set ((N → K → ℝ) × (K → ℝ)) := Icc 0 (fun _ => (2 : ℝ) • E.W) ×ˢ E.Prices

lemma mem_box_of_dom {x : N → K → ℝ} (hx : x ∈ Icc (0 : N → K → ℝ) (fun _ => (2 : ℝ) • E.W))
    (i : N) : x i ∈ E.box := ⟨hx.1 i, hx.2 i⟩

lemma zero_mem_box : (0 : K → ℝ) ∈ E.box :=
  ⟨le_rfl, fun k => by
    have := E.W_nonneg k
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith⟩

lemma tdem_nonempty (hm : Incomes m) (i : N) {p : K → ℝ} (hp : 0 ≤ p) :
    (E.tdem m i p).Nonempty := by
  classical
  by_cases hmi : 0 < m i
  · set C := E.box ∩ {z | dot p z ≤ m i}
    have hC : IsCompact C := isCompact_Icc.inter_right
      (isClosed_le (continuous_dot_right p) continuous_const)
    obtain ⟨z, hzC, hz⟩ := (E.pref i).exists_max hC
      ⟨0, E.zero_mem_box, by simp only [mem_setOf_eq, dot_zero_right]; exact hm.1 i⟩
      fun z hz => hz.1.1
    exact ⟨z, by
      simp only [tdem, mem_setOf_eq, if_pos hmi]
      exact ⟨hzC.1, hzC.2, fun w hw hwm => hz w ⟨hw, hwm.le⟩⟩⟩
  · exact ⟨0, by simp only [tdem, mem_setOf_eq, if_neg hmi]⟩

lemma tdem_sub_box (i : N) (p : K → ℝ) : E.tdem m i p ⊆ E.box := by
  classical
  intro z hz
  simp only [tdem, mem_setOf_eq] at hz
  split_ifs at hz with hmi
  · exact hz.1
  · rw [hz]
    exact E.zero_mem_box

lemma tdem_convex (hconv : ∀ i, (E.pref i).IsConvex) (i : N) (p : K → ℝ) :
    Convex ℝ (E.tdem m i p) := by
  classical
  by_cases hmi : 0 < m i
  · intro z hz z' hz' a b ha hb hab
    simp only [tdem, mem_setOf_eq, if_pos hmi] at hz hz' ⊢
    refine ⟨convex_Icc _ _ hz.1 hz'.1 ha hb hab, ?_, fun w hw hwm => ?_⟩
    · rw [dot_add_right, dot_smul_right, dot_smul_right]
      nlinarith [hz.2.1, hz'.2.1]
    · exact (hconv i w hw.1 ⟨hz.1.1, hz.2.2 w hw hwm⟩ ⟨hz'.1.1, hz'.2.2 w hw hwm⟩ ha hb hab).2
  · have : E.tdem m i p = {0} := by
      ext z
      simp only [tdem, mem_setOf_eq, if_neg hmi, mem_singleton_iff]
    rw [this]
    exact convex_singleton 0

variable [Nonempty N] [Nonempty K]

lemma pbest_nonempty (x : N → K → ℝ) : (E.pbest x).Nonempty := by
  obtain ⟨p, hp, hmax⟩ := E.isCompact_prices.exists_isMaxOn ⟨E.p0, E.p0_mem⟩
    (continuous_dot_left continuous_id (∑ i, x i)).continuousOn
  exact ⟨p, hp, fun p' hp' => hmax hp'⟩

lemma pbest_convex (x : N → K → ℝ) : Convex ℝ (E.pbest x) := by
  intro p hp q hq a b ha hb hab
  refine ⟨E.convex_prices hp.1 hq.1 ha hb hab, fun p' hp' => ?_⟩
  rw [dot_add_left, dot_smul_left, dot_smul_left]
  have h1 := mul_le_mul_of_nonneg_left (hp.2 p' hp') ha
  have h2 := mul_le_mul_of_nonneg_left (hq.2 p' hp') hb
  have h3 : dot p' (∑ i, x i) = a * dot p' (∑ i, x i) + b * dot p' (∑ i, x i) := by
    rw [← add_mul, hab, one_mul]
  linarith

/-- The graph of the joint best response is closed. -/
lemma isClosed_graph (m : N → ℝ) :
    IsClosed {q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) |
      q.1 ∈ E.dom ∧ q.2 ∈ E.bestResp m q.1} := by
  classical
  have hx : Continuous fun q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) => q.1.1 :=
    continuous_fst.comp continuous_fst
  have hp : Continuous fun q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) => q.1.2 :=
    continuous_snd.comp continuous_fst
  have hx' : Continuous fun q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) => q.2.1 :=
    continuous_fst.comp continuous_snd
  have hp' : Continuous fun q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) => q.2.2 :=
    continuous_snd.comp continuous_snd
  have hsum : Continuous fun q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) =>
      ∑ i, q.1.1 i := continuous_finsetSum _ fun i _ => (continuous_apply i).comp hx
  -- each consumer's condition
  have hG : ∀ i, IsClosed {q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) |
      q.2.1 i ∈ E.tdem m i q.1.2} := by
    intro i
    have hxi : Continuous fun q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) =>
        q.2.1 i := (continuous_apply i).comp hx'
    by_cases hmi : 0 < m i
    · have : {q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) |
          q.2.1 i ∈ E.tdem m i q.1.2} =
          ((fun q => q.2.1 i) ⁻¹' E.box ∩ {q | dot q.1.2 (q.2.1 i) ≤ m i}) ∩
            ⋂ w : E.box, ({q | m i ≤ dot q.1.2 w.1} ∪
              (fun q => q.2.1 i) ⁻¹' {z | 0 ≤ z ∧ (E.pref i).R z w.1}) := by
        ext q
        simp only [tdem, mem_setOf_eq, if_pos hmi, mem_inter_iff, Set.mem_preimage, mem_iInter,
          Set.mem_union, Subtype.forall]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨⟨h1, h2⟩, fun w hw => ?_⟩
          by_cases hlt : dot q.1.2 w < m i
          · exact Or.inr ⟨h1.1, h3 w hw hlt⟩
          · exact Or.inl (not_lt.1 hlt)
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, h2, fun w hw hlt => ?_⟩
          rcases h3 w hw with h | h
          · exact absurd hlt (not_lt.2 h)
          · exact h.2
      rw [this]
      refine ((isClosed_Icc.preimage hxi).inter
        (isClosed_le (continuous_dot_fun hp hxi) continuous_const)).inter
        (isClosed_iInter fun w => (isClosed_le continuous_const
          (continuous_dot_fun hp continuous_const)).union
          (((E.pref i).upper_closed _ w.2.1).preimage hxi))
    · have : {q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) |
          q.2.1 i ∈ E.tdem m i q.1.2} = {q | q.2.1 i = 0} := by
        ext q
        simp only [tdem, mem_setOf_eq, if_neg hmi]
      rw [this]
      exact isClosed_eq hxi continuous_const
  have hP : IsClosed {q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) |
      q.2.2 ∈ E.pbest q.1.1} := by
    have : {q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) | q.2.2 ∈ E.pbest q.1.1} =
        (fun q => q.2.2) ⁻¹' E.Prices ∩ ⋂ p'' : E.Prices,
          {q | dot p''.1 (∑ i, q.1.1 i) ≤ dot q.2.2 (∑ i, q.1.1 i)} := by
      ext q
      simp only [pbest, mem_setOf_eq, mem_inter_iff, Set.mem_preimage, mem_iInter, Subtype.forall]
    rw [this]
    exact (E.isCompact_prices.isClosed.preimage hp').inter (isClosed_iInter fun p'' =>
      isClosed_le (continuous_dot_fun continuous_const hsum) (continuous_dot_fun hp' hsum))
  have hdom : IsClosed (E.dom : Set ((N → K → ℝ) × (K → ℝ))) :=
    (isCompact_Icc.prod E.isCompact_prices).isClosed
  have : {q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) |
      q.1 ∈ E.dom ∧ q.2 ∈ E.bestResp m q.1} =
      (Prod.fst ⁻¹' E.dom ∩ ⋂ i, {q | q.2.1 i ∈ E.tdem m i q.1.2}) ∩
        {q | q.2.2 ∈ E.pbest q.1.1} := by
    ext q
    simp only [bestResp, mem_setOf_eq, mem_prod, mem_univ_pi, mem_inter_iff, Set.mem_preimage,
      mem_iInter]
    tauto
  rw [this]
  exact ((hdom.preimage continuous_fst).inter (isClosed_iInter hG)).inter hP

/-! ### From the fixed point to a Walrasian equilibrium for `m` -/

/-- At a fixed point, a consumer with positive income holds an optimal bundle (the box does not
  bind, since her bundle is at most `W`). -/
lemma fixed_optimal (hconv : ∀ i, (E.pref i).IsConvex) {m : N → ℝ} {i : N} (hmi : 0 < m i)
    {p z : K → ℝ} (hp : 0 ≤ p) (hz : z ∈ E.tdem m i p) (hzW : z ≤ E.W) :
    ∀ y, 0 ≤ y → dot p y ≤ m i → (E.pref i).R z y := by
  classical
  simp only [tdem, mem_setOf_eq, if_pos hmi] at hz
  obtain ⟨hzbox, hzm, hzopt⟩ := hz
  have hz0 : 0 ≤ z := hzbox.1
  intro y hy hym
  by_contra hR
  -- a slightly cheaper bundle `y'` that is still strictly better than `z`
  obtain ⟨y', hy'0, hy'R, hy'm⟩ : ∃ y', 0 ≤ y' ∧ ¬ (E.pref i).R z y' ∧ dot p y' < m i := by
    set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    have ht0 : ∀ n, 0 < t n := fun n => by positivity
    have ht1 : ∀ n, t n ≤ 1 := fun n => by
      simp only [t]
      rw [div_le_one (by positivity)]
      linarith [n.cast_nonneg (α := ℝ)]
    have hlim : Tendsto (fun n => (1 - t n) • y) atTop (𝓝 y) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_succ
      rw [sub_zero] at h
      have h2 := h.smul_const y
      rw [one_smul] at h2
      exact h2
    have hnot : ¬ ∀ᶠ n in atTop, (1 - t n) • y ∈ {w | 0 ≤ w ∧ (E.pref i).R z w} :=
      fun hev => hR ((E.pref i).lower_closed z hz0 |>.mem_of_tendsto hlim hev).2
    obtain ⟨n, hn⟩ := (not_eventually.1 hnot).exists
    have hny : 0 ≤ (1 - t n) • y := smul_nonneg (by linarith [ht1 n]) hy
    refine ⟨_, hny, fun h => hn ⟨hny, h⟩, ?_⟩
    rw [dot_smul_right]
    have := ht0 n
    nlinarith [ht1 n]
  -- mix `y'` with `z + ε·1`; the mixture is strictly better, cheaper than `mᵢ`, and in the box
  set g := m i - dot p y' with hg
  have hgpos : 0 < g := by rw [hg]; linarith
  set one : K → ℝ := fun _ => 1
  set S1 := dot p one
  have hS1 : 0 ≤ S1 := dot_nonneg hp fun _ => zero_le_one
  set c := g / (2 * (S1 + 1)) with hc
  have hcpos : 0 < c := by positivity
  have hev : ∀ᶠ l in 𝓝[>] (0 : ℝ), l < 1 ∧ ∀ k, l * (y' k + c) < E.W k := by
    apply nhdsWithin_le_nhds
    refine (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).and (eventually_all.2 fun k => ?_)
    have hcont : Continuous fun l : ℝ => l * (y' k + c) := continuous_id.mul continuous_const
    have h0 : (fun l : ℝ => l * (y' k + c)) 0 < E.W k := by
      simp only [zero_mul]
      exact E.W_pos k
    exact hcont.continuousAt.eventually (gt_mem_nhds h0)
  obtain ⟨l, ⟨hl1, hlW⟩, hl0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hl0' : (0 : ℝ) < l := hl0
  set ε := l * c with hε
  have hεpos : 0 < ε := mul_pos hl0' hcpos
  set v := z + ε • one with hv
  have hv0 : 0 ≤ v := fun k => by
    simp only [hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, one]
    have := hz0 k
    simp only [Pi.zero_apply] at this
    linarith
  have hvR : ¬ (E.pref i).R z v := (E.pref i).mono z v hz0 fun k => by
    simp only [hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one]
    linarith
  set w := l • y' + (1 - l) • v with hw
  have hwS := (E.pref i |>.convex_strict (hconv i) hz0) ⟨hy'0, hy'R⟩ ⟨hv0, hvR⟩ hl0'.le
    (show (0 : ℝ) ≤ 1 - l by linarith) (show l + (1 - l) = 1 by ring)
  have hwbox : w ∈ E.box := by
    refine ⟨hwS.1, fun k => ?_⟩
    have h1 := hlW k
    have h2 := hzW k
    have h3 := hz0 k
    simp only [hw, hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one, Pi.zero_apply] at h3 ⊢
    nlinarith
  have hwm : dot p w < m i := by
    have hdv : dot p v = dot p z + ε * S1 := by
      rw [hv, dot_add_right, dot_smul_right]
    rw [hw, dot_add_right, dot_smul_right, dot_smul_right, hdv]
    have h1 : ε * S1 < l * g := by
      rw [hε, hc]
      have : S1 / (S1 + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
      have : l * (g / (2 * (S1 + 1))) * S1 = l * g * (S1 / (S1 + 1)) / 2 := by
        field_simp
      rw [this]
      have := mul_pos hl0' hgpos
      nlinarith
    have a1 := mul_le_mul_of_nonneg_left hzm (show (0 : ℝ) ≤ 1 - l by linarith)
    have a2 : (1 - l) * (ε * S1) ≤ ε * S1 := by
      have := mul_nonneg hεpos.le hS1
      nlinarith
    have a3 : (1 - l) * (dot p z + ε * S1) = (1 - l) * dot p z + (1 - l) * (ε * S1) := by ring
    rw [a3]
    have a4 : l * g = l * m i - l * dot p y' := by rw [hg]; ring
    linarith
  exact hwS.2 (hzopt w hwbox hwm)

/-- **Theorem 2(c).** With convex preferences, and assuming Kakutani's fixed-point theorem, for
  every income distribution `m ∈ Σ_N` there is a Walrasian equilibrium for `m` with `p ≫ 0`. -/
theorem walrasianFor_exists (hconv : ∀ i, (E.pref i).IsConvex)
    (hK : Kakutani ((N → K → ℝ) × (K → ℝ))) {m : N → ℝ} (hm : Incomes m) :
    ∃ x p, E.IsWalrasianFor m x p ∧ ∀ k, 0 < p k := by
  classical
  obtain ⟨⟨x, p⟩, hS, hfix⟩ := hK E.dom (E.bestResp m)
    ⟨(0, E.p0), ⟨le_rfl, fun i => (E.zero_mem_box).2⟩, E.p0_mem⟩
    (isCompact_Icc.prod E.isCompact_prices) ((convex_Icc _ _).prod E.convex_prices)
    (fun q hq => ⟨(univ_pi_nonempty_iff.2 fun i => E.tdem_nonempty hm i hq.2.1).prod
        (E.pbest_nonempty q.1),
      prod_mono (fun x hx => ⟨fun i => (E.tdem_sub_box i q.2 (hx i trivial)).1,
        fun i => (E.tdem_sub_box i q.2 (hx i trivial)).2⟩) fun p hp => hp.1,
      (convex_pi fun i _ => E.tdem_convex hconv i q.2).prod (E.pbest_convex q.1)⟩)
    (E.isClosed_graph m)
  obtain ⟨hxd, hpb⟩ := hfix
  have hxd : ∀ i, x i ∈ E.tdem m i p := fun i => hxd i trivial
  have hp : p ∈ E.Prices := hS.2
  have hx0 : ∀ i, 0 ≤ x i := fun i => (E.tdem_sub_box i p (hxd i)).1
  have hm0 : ∀ i, ¬ 0 < m i → m i = 0 := fun i h => le_antisymm (not_lt.1 h) (hm.1 i)
  have hx_zero : ∀ i, ¬ 0 < m i → x i = 0 := fun i h => by
    have := hxd i
    simp only [tdem, mem_setOf_eq, if_neg h] at this
    exact this
  -- budgets
  have hbud : ∀ i, dot p (x i) ≤ m i := fun i => by
    by_cases hmi : 0 < m i
    · have := hxd i
      simp only [tdem, mem_setOf_eq, if_pos hmi] at this
      exact this.2.1
    · rw [hx_zero i hmi, dot_zero_right, hm0 i hmi]
  -- market clearing: the price player's best response forces `∑ xᵢ ≤ W`
  have hfeas : ∀ k, ∑ i, x i k ≤ E.W k := by
    intro k
    set ek : K → ℝ := fun l => if l = k then 1 / E.W k else 0
    have hek : ek ∈ E.Prices := by
      refine ⟨fun l => ?_, ?_⟩
      · simp only [ek, Pi.zero_apply]
        split_ifs
        · exact (one_div_pos.2 (E.W_pos k)).le
        · exact le_rfl
      · simp only [dot, ek, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact one_div_mul_cancel (E.W_pos k).ne'
    have h1 := hpb.2 ek hek
    have h2 : dot p (∑ i, x i) ≤ 1 := by
      rw [dot_sum_right, ← hm.2]
      exact Finset.sum_le_sum fun i _ => hbud i
    have h3 : dot ek (∑ i, x i) = (∑ i, x i k) / E.W k := by
      simp only [dot, ek, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Finset.sum_apply]
      ring
    have h4 : (∑ i, x i k) / E.W k ≤ 1 := by linarith
    rwa [div_le_one (E.W_pos k)] at h4
  have hxW : ∀ i, x i ≤ E.W := fun i k =>
    (Finset.single_le_sum (fun j _ => hx0 j k) (mem_univ i)).trans (hfeas k)
  have hopt : ∀ i, 0 < m i → ∀ y, 0 ≤ y → dot p y ≤ m i → (E.pref i).R (x i) y :=
    fun i hmi => E.fixed_optimal hconv hmi hp.1 (hxd i) (hxW i)
  -- strictly positive prices
  obtain ⟨i₀, hi₀⟩ : ∃ i, 0 < m i := by
    by_contra h
    push_neg at h
    have : ∑ i, m i ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith [hm.2]
  have hpos : ∀ k, 0 < p k := by
    intro k
    by_contra hk
    have hpk : p k = 0 := le_antisymm (not_lt.1 hk) (hp.1 k)
    set z := x i₀
    -- `z ≻ 0`, comparing with a small affordable bundle `δ·1`
    set S1 := dot p (fun _ => (1 : ℝ))
    have hS1 : 0 ≤ S1 := dot_nonneg hp.1 fun _ => zero_le_one
    set δ := m i₀ / (S1 + 1)
    have hδ : 0 < δ := by positivity
    have hδm : dot p (fun _ => δ) ≤ m i₀ := by
      have : dot p (fun _ => δ) = δ * S1 := by
        rw [show (fun _ : K => δ) = δ • (fun _ : K => (1 : ℝ)) by funext; simp,
          dot_smul_right]
      rw [this]
      simp only [δ]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    have hz0 : ¬ (E.pref i₀).R 0 z := fun h =>
      (E.pref i₀).mono 0 (fun _ => δ) le_rfl (fun _ => hδ)
        ((E.pref i₀).trans _ _ _ le_rfl (hx0 i₀) (fun _ => hδ.le) h
          (hopt i₀ hi₀ _ (fun _ => hδ.le) hδm))
    -- adding the free good `k` is affordable and strictly better
    set e : K → ℝ := fun l => if l = k then 1 else 0
    have he0 : 0 ≤ e := fun l => by simp only [e, Pi.zero_apply]; split_ifs <;> norm_num
    have hpe : dot p e = 0 := by
      simp only [dot, e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hpk]
    have hne : z ≠ z + e := fun h => by
      have := congrFun h k
      simp [e] at this
    have hle : z ≤ z + e := fun l => by
      have := he0 l
      simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
      linarith
    exact (E.pref i₀).mono' z (z + e) (hx0 i₀) hz0 hle hne
      (hopt i₀ hi₀ _ ((hx0 i₀).trans hle) (by rw [dot_add_right, hpe, add_zero]; exact hbud i₀))
  refine ⟨x, p, ⟨⟨hx0, hfeas⟩, hp, fun i => ⟨hx0 i, hbud i, fun y hy hym => ?_⟩⟩, hpos⟩
  by_cases hmi : 0 < m i
  · exact hopt i hmi y hy hym
  · -- zero income: only the zero bundle is affordable at `p ≫ 0`
    rw [hx_zero i hmi]
    have hy0 : y = 0 := by
      rw [hm0 i hmi] at hym
      have hterm : ∀ k ∈ (univ : Finset K), 0 ≤ p k * y k := fun k _ =>
        mul_nonneg (hpos k).le (hy k)
      funext k
      have := (Finset.sum_eq_zero_iff_of_nonneg hterm).1
        (le_antisymm hym (Finset.sum_nonneg hterm)) k (mem_univ k)
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (hpos k).ne'
      · exact h
    rw [hy0]
    exact (E.pref i).refl le_rfl

/-- **Theorem 2(c)**, as stated in the paper: the potential has a root at every `m ∈ Σ_N`, and
  so (Theorem 2(a)) the Yquilibria for `m` are exactly the roots in `C_m`. -/
theorem theorem2_c (hconv : ∀ i, (E.pref i).IsConvex)
    (hK : Kakutani ((N → K → ℝ) × (K → ℝ))) {m : N → ℝ} (hm : Incomes m) :
    ∃ x p, (x, p) ∈ E.CSet m ∧ E.Y x p = 0 := by
  obtain ⟨x, p, hW, -⟩ := E.walrasianFor_exists hconv hK hm
  have hroot : E.IsRoot x p := E.root_iff.2 ⟨m, hm, hW⟩
  exact ⟨x, p, ⟨hW.1, hW.2.1, E.walrasianFor_income hW⟩, hroot.2.2⟩

/-! ### Price-dependent incomes, and Walrasian equilibrium for the endowments

  The same argument works when incomes depend continuously on the price, provided they are
  positive and add up to one on `Σ_K(W)`. Fixed incomes `m ≫ 0` and endowment incomes
  `⟨p|ωᵢ⟩` are special cases. -/

/-- Truncated demand at the price-dependent income `inc p i`. -/
def tdemV (inc : (K → ℝ) → N → ℝ) (i : N) (p : K → ℝ) : Set (K → ℝ) :=
  {z | z ∈ E.box ∧ dot p z ≤ inc p i ∧ ∀ w ∈ E.box, dot p w < inc p i → (E.pref i).R z w}

lemma tdemV_eq {inc : (K → ℝ) → N → ℝ} {i : N} {p : K → ℝ} (h : 0 < inc p i) :
    E.tdemV inc i p = E.tdem (inc p) i p := by
  classical
  ext z
  simp only [tdemV, tdem, mem_setOf_eq, if_pos h]

/-- **Existence of Walrasian equilibrium with price-dependent incomes** (assuming Kakutani). -/
theorem walrasianV_exists (hconv : ∀ i, (E.pref i).IsConvex)
    (hK : Kakutani ((N → K → ℝ) × (K → ℝ))) (inc : (K → ℝ) → N → ℝ)
    (hcont : ∀ i, Continuous fun p => inc p i) (hpos : ∀ p ∈ E.Prices, ∀ i, 0 < inc p i)
    (hsum : ∀ p ∈ E.Prices, ∑ i, inc p i = 1) :
    ∃ x p, E.IsWalrasianFor (inc p) x p ∧ ∀ k, 0 < p k := by
  classical
  set φ : (N → K → ℝ) × (K → ℝ) → Set ((N → K → ℝ) × (K → ℝ)) :=
    fun q => (Set.univ.pi fun i => E.tdemV inc i q.2) ×ˢ E.pbest q.1 with hφ
  -- closed graph
  have hgraph : IsClosed {q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) |
      q.1 ∈ E.dom ∧ q.2 ∈ φ q.1} := by
    have hx : Continuous fun q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) =>
        q.1.1 := continuous_fst.comp continuous_fst
    have hp : Continuous fun q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) =>
        q.1.2 := continuous_snd.comp continuous_fst
    have hx' : Continuous fun q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) =>
        q.2.1 := continuous_fst.comp continuous_snd
    have hp' : Continuous fun q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) =>
        q.2.2 := continuous_snd.comp continuous_snd
    have hsumx : Continuous fun q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) =>
        ∑ i, q.1.1 i := continuous_finsetSum _ fun i _ => (continuous_apply i).comp hx
    have hG : ∀ i, IsClosed {q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) |
        q.2.1 i ∈ E.tdemV inc i q.1.2} := by
      intro i
      have hxi : Continuous fun q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) =>
          q.2.1 i := (continuous_apply i).comp hx'
      have hinc : Continuous fun q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) =>
          inc q.1.2 i := (hcont i).comp hp
      have : {q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) |
          q.2.1 i ∈ E.tdemV inc i q.1.2} =
          ((fun q => q.2.1 i) ⁻¹' E.box ∩ {q | dot q.1.2 (q.2.1 i) ≤ inc q.1.2 i}) ∩
            ⋂ w : E.box, ({q | inc q.1.2 i ≤ dot q.1.2 w.1} ∪
              (fun q => q.2.1 i) ⁻¹' {z | 0 ≤ z ∧ (E.pref i).R z w.1}) := by
        ext q
        simp only [tdemV, mem_setOf_eq, mem_inter_iff, Set.mem_preimage, mem_iInter,
          Set.mem_union, Subtype.forall]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨⟨h1, h2⟩, fun w hw => ?_⟩
          by_cases hlt : dot q.1.2 w < inc q.1.2 i
          · exact Or.inr ⟨h1.1, h3 w hw hlt⟩
          · exact Or.inl (not_lt.1 hlt)
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, h2, fun w hw hlt => ?_⟩
          rcases h3 w hw with h | h
          · exact absurd hlt (not_lt.2 h)
          · exact h.2
      rw [this]
      exact ((isClosed_Icc.preimage hxi).inter
        (isClosed_le (continuous_dot_fun hp hxi) hinc)).inter
        (isClosed_iInter fun w => (isClosed_le hinc
          (continuous_dot_fun hp continuous_const)).union
          (((E.pref i).upper_closed _ w.2.1).preimage hxi))
    have hP : IsClosed {q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) |
        q.2.2 ∈ E.pbest q.1.1} := by
      have : {q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) |
          q.2.2 ∈ E.pbest q.1.1} = (fun q => q.2.2) ⁻¹' E.Prices ∩ ⋂ p'' : E.Prices,
            {q | dot p''.1 (∑ i, q.1.1 i) ≤ dot q.2.2 (∑ i, q.1.1 i)} := by
        ext q
        simp only [pbest, mem_setOf_eq, mem_inter_iff, Set.mem_preimage, mem_iInter,
          Subtype.forall]
      rw [this]
      exact (E.isCompact_prices.isClosed.preimage hp').inter (isClosed_iInter fun p'' =>
        isClosed_le (continuous_dot_fun continuous_const hsumx) (continuous_dot_fun hp' hsumx))
    have hdom : IsClosed (E.dom : Set ((N → K → ℝ) × (K → ℝ))) :=
      (isCompact_Icc.prod E.isCompact_prices).isClosed
    have : {q : ((N → K → ℝ) × (K → ℝ)) × ((N → K → ℝ) × (K → ℝ)) |
        q.1 ∈ E.dom ∧ q.2 ∈ φ q.1} =
        (Prod.fst ⁻¹' E.dom ∩ ⋂ i, {q | q.2.1 i ∈ E.tdemV inc i q.1.2}) ∩
          {q | q.2.2 ∈ E.pbest q.1.1} := by
      ext q
      simp only [hφ, mem_setOf_eq, mem_prod, mem_univ_pi, mem_inter_iff, Set.mem_preimage,
        mem_iInter]
      tauto
    rw [this]
    exact ((hdom.preimage continuous_fst).inter (isClosed_iInter hG)).inter hP
  obtain ⟨⟨x, p⟩, hS, hfix⟩ := hK E.dom φ
    ⟨(0, E.p0), ⟨le_rfl, fun i => (E.zero_mem_box).2⟩, E.p0_mem⟩
    (isCompact_Icc.prod E.isCompact_prices) ((convex_Icc _ _).prod E.convex_prices)
    (fun q hq => by
      have hi := fun i => E.tdemV_eq (hpos q.2 hq.2 i)
      refine ⟨(univ_pi_nonempty_iff.2 fun i => ?_).prod (E.pbest_nonempty q.1),
        prod_mono (fun x hx => ⟨fun i => ?_, fun i => ?_⟩) fun p hp => hp.1, ?_⟩
      · rw [hi i]
        exact E.tdem_nonempty ⟨fun j => (hpos q.2 hq.2 j).le, hsum q.2 hq.2⟩ i hq.2.1
      · have : x i ∈ E.tdemV inc i q.2 := hx i trivial
        rw [hi i] at this
        exact (E.tdem_sub_box i q.2 this).1
      · have : x i ∈ E.tdemV inc i q.2 := hx i trivial
        rw [hi i] at this
        exact (E.tdem_sub_box i q.2 this).2
      · refine (convex_pi fun i _ => ?_).prod (E.pbest_convex q.1)
        rw [hi i]
        exact E.tdem_convex hconv i q.2)
    hgraph
  obtain ⟨hxd, hpb⟩ := hfix
  have hp : p ∈ E.Prices := hS.2
  set m := inc p with hmdef
  have hmpos : ∀ i, 0 < m i := hpos p hp
  have hxd : ∀ i, x i ∈ E.tdem m i p := fun i => by
    rw [← E.tdemV_eq (hmpos i)]
    exact hxd i trivial
  have hx0 : ∀ i, 0 ≤ x i := fun i => (E.tdem_sub_box i p (hxd i)).1
  have hbud : ∀ i, dot p (x i) ≤ m i := fun i => by
    have := hxd i
    simp only [tdem, mem_setOf_eq, if_pos (hmpos i)] at this
    exact this.2.1
  have hfeas : ∀ k, ∑ i, x i k ≤ E.W k := by
    intro k
    set ek : K → ℝ := fun l => if l = k then 1 / E.W k else 0
    have hek : ek ∈ E.Prices := by
      refine ⟨fun l => ?_, ?_⟩
      · simp only [ek, Pi.zero_apply]
        split_ifs
        · exact (one_div_pos.2 (E.W_pos k)).le
        · exact le_rfl
      · simp only [dot, ek, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact one_div_mul_cancel (E.W_pos k).ne'
    have h1 := hpb.2 ek hek
    have h2 : dot p (∑ i, x i) ≤ 1 := by
      rw [dot_sum_right, ← hsum p hp]
      exact Finset.sum_le_sum fun i _ => hbud i
    have h3 : dot ek (∑ i, x i) = (∑ i, x i k) / E.W k := by
      simp only [dot, ek, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Finset.sum_apply]
      ring
    have h4 : (∑ i, x i k) / E.W k ≤ 1 := by
      have : dot ek (∑ i, x i) ≤ dot p (∑ i, x i) := h1
      linarith
    rwa [div_le_one (E.W_pos k)] at h4
  have hxW : ∀ i, x i ≤ E.W := fun i k =>
    (Finset.single_le_sum (fun j _ => hx0 j k) (Finset.mem_univ i)).trans (hfeas k)
  have hopt : ∀ i, ∀ y, 0 ≤ y → dot p y ≤ m i → (E.pref i).R (x i) y :=
    fun i => E.fixed_optimal hconv (hmpos i) hp.1 (hxd i) (hxW i)
  obtain ⟨i₀⟩ := ‹Nonempty N›
  have hppos : ∀ k, 0 < p k := by
    intro k
    by_contra hk
    have hpk : p k = 0 := le_antisymm (not_lt.1 hk) (hp.1 k)
    set z := x i₀
    set S1 := dot p (fun _ => (1 : ℝ))
    have hS1 : 0 ≤ S1 := dot_nonneg hp.1 fun _ => zero_le_one
    set δ := m i₀ / (S1 + 1)
    have hδ : 0 < δ := div_pos (hmpos i₀) (by linarith)
    have hδm : dot p (fun _ => δ) ≤ m i₀ := by
      have : dot p (fun _ => δ) = δ * S1 := by
        rw [show (fun _ : K => δ) = δ • (fun _ : K => (1 : ℝ)) by funext; simp,
          dot_smul_right]
      rw [this]
      simp only [δ]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith [hmpos i₀]
    have hz0 : ¬ (E.pref i₀).R 0 z := fun h =>
      (E.pref i₀).mono 0 (fun _ => δ) le_rfl (fun _ => hδ)
        ((E.pref i₀).trans _ _ _ le_rfl (hx0 i₀) (fun _ => hδ.le) h
          (hopt i₀ _ (fun _ => hδ.le) hδm))
    set e : K → ℝ := fun l => if l = k then 1 else 0
    have he0 : 0 ≤ e := fun l => by simp only [e, Pi.zero_apply]; split_ifs <;> norm_num
    have hpe : dot p e = 0 := by
      simp only [dot, e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, hpk]
    have hne : z ≠ z + e := fun h => by
      have := congrFun h k
      simp [e] at this
    have hle : z ≤ z + e := fun l => by
      have := he0 l
      simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
      linarith
    exact (E.pref i₀).mono' z (z + e) (hx0 i₀) hz0 hle hne
      (hopt i₀ _ ((hx0 i₀).trans hle) (by rw [dot_add_right, hpe, add_zero]; exact hbud i₀))
  exact ⟨x, p, ⟨⟨hx0, hfeas⟩, hp, fun i => ⟨hx0 i, hbud i, hopt i⟩⟩, hppos⟩

/-- **Existence of Walrasian equilibrium** for the endowments `ωᵢ ≫ 0` (assuming Kakutani):
  the classical Arrow–Debreu result in this setting. -/
theorem walrasian_exists (hconv : ∀ i, (E.pref i).IsConvex)
    (hK : Kakutani ((N → K → ℝ) × (K → ℝ))) :
    ∃ x p, E.IsWalrasian x p ∧ ∀ k, 0 < p k := by
  refine E.walrasianV_exists hconv hK (fun p i => dot p (E.ω i))
    (fun i => continuous_dot_left continuous_id _) (fun p hp i => ?_) fun p hp => ?_
  · have hpne : p ≠ 0 := fun h => by
      have := hp.2
      rw [h] at this
      simp [dot] at this
    obtain ⟨k, hk⟩ : ∃ k, p k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hpne (funext h)
    have hk' : 0 < p k := lt_of_le_of_ne (hp.1 k) (Ne.symm hk)
    exact lt_of_lt_of_le (mul_pos hk' (E.ω_pos i k)) (mul_le_dot hp.1 (E.ω_nonneg i) k)
  · rw [E.sum_dot_ω]
    exact hp.2

end Economy

end Yq
