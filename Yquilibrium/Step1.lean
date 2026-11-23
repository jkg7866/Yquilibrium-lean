/-
  Yquilibrium (Goeree, 21 Nov 2026), Theorem 4, Step 1: near any non-Pareto-optimal state, a
  fixed proposer–responder pair, a neighbourhood of prices and a range of trade sizes make the
  sum of utilities rise by a fixed amount.
-/
import Yquilibrium.Calculus
import Yquilibrium.Replica

open Finset Set Filter Topology

noncomputable section

namespace Yq

namespace Economy

variable {K N : Type*} [Fintype K] [Fintype N] [DecidableEq N] {E : Economy N K}
  {u : N → (K → ℝ) → ℝ}

/-- Theorem 4's additional assumptions: a differentiable representation with strictly positive
  gradient at interior bundles, and essential goods (a bundle with all goods is strictly
  preferred to any bundle lacking some good). -/
structure Smooth (E : Economy N K) (u : N → (K → ℝ) → ℝ) : Prop where
  grad : ∀ i (x : K → ℝ), (∀ k, 0 < x k) → ∃ (L : (K → ℝ) →L[ℝ] ℝ) (g : K → ℝ),
    HasFDerivAt (u i) L x ∧ (∀ v, L v = dot g v) ∧ ∀ k, 0 < g k
  essential : ∀ i (x y : K → ℝ), 0 ≤ y → (∀ k, 0 < x k) → (∃ k, y k = 0) →
    ¬ (E.pref i).R y x

/-- The sum of utilities `S(x) = ∑ᵢ uᵢ(xᵢ)`. -/
def totalU (u : N → (K → ℝ) → ℝ) (x : N → K → ℝ) : ℝ := ∑ i, u i (x i)

/-- With essential goods, individually-rational bundles are interior. -/
lemma pathSet_interior (hs : E.Smooth u) {x : N → K → ℝ} (hx : x ∈ E.pathSet) (i : N) (k : K) :
    0 < x i k := by
  have hIR : (E.pref i).R (x i) (E.ω i) := (Set.mem_iInter.1 hx.2 i).2
  have h0 : 0 ≤ x i k := hx.1.1 i k
  by_contra h
  exact hs.essential i (E.ω i) (x i) (hx.1.1 i) (E.ω_pos i)
    ⟨k, le_antisymm (not_lt.1 h) h0⟩ hIR

omit [DecidableEq N] in
/-- Proportional vectors with the same normalization coincide. -/
lemma eq_smul_of_prop {a b W : K → ℝ} (h : ∀ k l, a k * b l = a l * b k) (hb : dot b W = 1) :
    a = dot a W • b := by
  funext k
  simp only [Pi.smul_apply, smul_eq_mul]
  have : a k * dot b W = dot a W * b k := by
    simp only [dot, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, h k l]; ring
  rwa [hb, mul_one] at this

omit [DecidableEq N] in
lemma dot_neg_right (p z : K → ℝ) : dot p (-z) = -dot p z := by
  simp [dot, Finset.sum_neg_distrib]

omit [DecidableEq N] in
lemma dot_sub_right (p z w : K → ℝ) : dot p (z - w) = dot p z - dot p w := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

omit [Fintype N] [DecidableEq N] in
lemma interior_mem_nhds {x : K → ℝ} (hx : ∀ k, 0 < x k) : {z : K → ℝ | 0 ≤ z} ∈ 𝓝 x := by
  have hopen : IsOpen {y : K → ℝ | ∀ k, 0 < y k} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun k => isOpen_lt continuous_const (continuous_apply k)
  exact Filter.mem_of_superset (hopen.mem_nhds hx) fun y hy k => (hy k).le

/-- **Theorem 4, Step 1.** -/
theorem step1_progress [Nonempty N] [Nonempty K] (hu : E.DynRep u) (hs : E.Smooth u)
    {xh : N → K → ℝ} (hxh : xh ∈ E.pathSet) (hnPO : ¬ E.ParetoOptimal xh) :
    ∃ i j : N, i ≠ j ∧ ∃ ph : K → ℝ, (∀ k, 0 < ph k) ∧ dot ph E.W = 1 ∧
      ∃ Δ₁ : ℝ, 0 < Δ₁ ∧ Δ₁ ≤ 1 ∧ ∃ ε > 0, ∀ᶠ r in 𝓝 (xh, ph),
        ∀ ω : Draw N K, ω.Valid E → ω.P = i → ω.p = r.2 → ω.Δ ∈ Icc (Δ₁ / 2) Δ₁ →
          ω.order.head? = some j → r.1 ∈ E.pathSet →
            totalU u r.1 + ε ≤ totalU u (E.step r.1 ω) := by
  classical
  have hint : ∀ i k, 0 < xh i k := pathSet_interior hs hxh
  have hxF : E.Exact xh := hxh.1
  have hWne : E.W ≠ 0 := fun h => by
    obtain ⟨k⟩ := ‹Nonempty K›
    have := E.W_pos k
    rw [h] at this
    exact lt_irrefl _ this
  choose L g hL hLg hg using fun i => hs.grad i (xh i) (hint i)
  have hgW : ∀ i, 0 < dot (g i) E.W := fun i => dot_pos (hg i) E.W_nonneg hWne
  -- normalized gradients qᵢ
  set q : N → K → ℝ := fun i => (dot (g i) E.W)⁻¹ • g i with hqdef
  have hqpos : ∀ i k, 0 < q i k := fun i k => by
    simp only [hqdef, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.2 (hgW i)) (hg i k)
  have hqW : ∀ i, dot (q i) E.W = 1 := fun i => by
    simp only [hqdef]
    rw [dot_smul_left, inv_mul_cancel₀ (hgW i).ne']
  have hgq : ∀ i, g i = dot (g i) E.W • q i := fun i => by
    simp only [hqdef]
    rw [smul_smul, mul_inv_cancel₀ (hgW i).ne', one_smul]
  have hoptq : ∀ i, Optimal (E.pref i) (q i) (dot (q i) (xh i)) (xh i) := fun i =>
    optimal_of_foc hu i (hint i) (hL i) (hLg i) (hqpos i) (hgW i) (hgq i)
  -- if all normalized gradients were equal, xh would be a root, hence Pareto optimal
  obtain ⟨i, j, hij⟩ : ∃ i j, q i ≠ q j := by
    by_contra hall
    push_neg at hall
    obtain ⟨i0⟩ := ‹Nonempty N›
    apply hnPO
    have hroot : E.IsRoot xh (q i0) := by
      rw [E.root_iff_optimal]
      refine ⟨hxF.feasible, ⟨fun k => (hqpos i0 k).le, hqW i0⟩, hqpos i0, fun i => ?_, ?_⟩
      · rw [← hall i i0]
        exact hoptq i
      · rw [sum_dot_eq']
        simp only [hxF.2]
        exact hqW i0
    exact (E.root_pos_pareto hroot).2
  have hij' : i ≠ j := fun h => hij (h ▸ rfl)
  -- the midpoint price
  set ph : K → ℝ := (1 / 2 : ℝ) • (q i + q j) with hphdef
  have hph : ∀ k, 0 < ph k := fun k => by
    simp only [hphdef, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have := hqpos i k
    have := hqpos j k
    positivity
  have hphW : dot ph E.W = 1 := by
    rw [hphdef, dot_smul_left, dot_add_left, hqW, hqW]
    norm_num
  have hxi0 : 0 ≤ xh i := fun k => (hint i k).le
  have hxj0 : 0 ≤ xh j := fun k => (hint j k).le
  have hxine : xh i ≠ 0 := fun h => by
    obtain ⟨k⟩ := ‹Nonempty K›
    have := hint i k
    rw [h] at this
    exact lt_irrefl _ this
  set mh := dot ph (xh i) with hmhdef
  have hmh : 0 < mh := dot_pos hph hxi0 hxine
  set dh := E.demand i ph mh with hdhdef
  have hdh : Optimal (E.pref i) ph mh dh := demand_spec hu i hph hmh.le
  set zh := dh - xh i with hzhdef
  -- i's demand differs from its bundle
  have hne : dh ≠ xh i := by
    intro h
    have hopt' : Optimal (E.pref i) ph mh (xh i) := by rw [← h]; exact hdh
    have h1 := eq_smul_of_prop (foc_of_optimal hu i (hint i) hopt' (hL i) (hLg i)) hphW
    have h2 : q i = ph := by
      simp only [hqdef]
      conv_lhs => arg 2; rw [h1]
      rw [smul_smul, inv_mul_cancel₀ (hgW i).ne', one_smul]
    apply hij
    funext k
    have := congrFun h2 k
    simp only [hphdef, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
    linarith
  have hge : u i (xh i) ≤ u i dh := (hu.rep i dh (xh i) hdh.1 hxi0).1 (hdh.2.2 _ hxi0 le_rfl)
  have hgt : u i (xh i) < u i dh := by
    refine lt_of_le_of_ne hge fun heq => hne ?_
    have hopt2 : Optimal (E.pref i) ph mh (xh i) :=
      ⟨hxi0, le_rfl, fun z hz hzm => (hu.rep i (xh i) z hxi0 hz).2
        (heq ▸ (hu.rep i dh z hdh.1 hz).1 (hdh.2.2 z hz hzm))⟩
    exact optimal_unique hu i hdh hopt2
  -- ⟨qᵢ|z⟩ > 0, ⟨p̂|z⟩ = 0, so ⟨qⱼ|z⟩ < 0
  have hqiz : 0 < dot (q i) zh := by
    by_contra hle
    push_neg at hle
    rw [hzhdef, dot_sub_right] at hle
    have := (hu.rep i (xh i) dh hxi0 hdh.1).1 ((hoptq i).2.2 dh hdh.1 (by linarith))
    linarith
  have hphz : dot ph zh = 0 := by
    rw [hzhdef, dot_sub_right, (optimal_mu (fun k => (hph k).le) hdh).2, hmhdef, sub_self]
  have hqjz : dot (q j) zh < 0 := by
    have h := hphz
    rw [hphdef, dot_smul_left, dot_add_left] at h
    linarith
  have hLj : 0 < L j (-zh) := by
    rw [hLg j, hgq j, dot_smul_left, dot_neg_right]
    exact mul_pos (hgW j) (by linarith)
  -- choose Δ₁: small steps along −z strictly improve j and keep j's bundle interior
  have hev1 := eventually_gt_of_deriv_pos (hasDerivAt_line (hL j) (-zh)) hLj
  have hopenI : IsOpen {y : K → ℝ | ∀ k, 0 < y k} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun k => isOpen_lt continuous_const (continuous_apply k)
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), xh j + t • -zh ∈ {y : K → ℝ | ∀ k, 0 < y k} := by
    apply nhdsWithin_le_nhds
    have hc : Continuous fun t : ℝ => xh j + t • -zh :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact hc.continuousAt.preimage_mem_nhds (hopenI.mem_nhds (by simpa using hint j))
  obtain ⟨a, ha, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hev1.and hev2)
  have ha0 : (0 : ℝ) < a := ha
  set Δ₁ := min (a / 2) 1 with hΔ₁
  have hΔ₁0 : 0 < Δ₁ := lt_min (by linarith) one_pos
  have hΔ₁1 : Δ₁ ≤ 1 := min_le_right _ _
  have hΔ₁a : Δ₁ < a := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hgood : ∀ t ∈ Icc (Δ₁ / 2) Δ₁, u j (xh j) < u j (xh j - t • zh) ∧
      ∀ k, 0 < (xh j - t • zh) k := by
    intro t ht
    have ht' : t ∈ Ioo 0 a := ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hΔ₁a⟩
    obtain ⟨h1, h2⟩ := hsub ht'
    have heq : xh j + t • -zh = xh j - t • zh := by rw [smul_neg, ← sub_eq_add_neg]
    simp only [zero_smul, add_zero] at h1
    rw [heq] at h1 h2
    exact ⟨h1, h2⟩
  -- the gain of j as a function of the state, the price and the trade size
  set Z : (N → K → ℝ) × (K → ℝ) → K → ℝ := fun r => E.demand i r.2 (dot r.2 (r.1 i)) - r.1 i
    with hZdef
  set B : ((N → K → ℝ) × (K → ℝ)) × ℝ → K → ℝ := fun s => s.1.1 j - s.2 • Z s.1 with hBdef
  set F : ((N → K → ℝ) × (K → ℝ)) × ℝ → ℝ := fun s => u j (B s) - u j (s.1.1 j) with hFdef
  have hZc : ContinuousAt Z (xh, ph) := by
    have h1 : ContinuousAt (fun r : (N → K → ℝ) × (K → ℝ) => (r.2, dot r.2 (r.1 i))) (xh, ph) :=
      (continuous_snd.prodMk (dot_continuous_pair.comp
        (continuous_snd.prodMk ((continuous_apply i).comp continuous_fst)))).continuousAt
    have h2 := demand_continuousAt hu i hph hmh
    have h3 : ContinuousAt (fun r : (N → K → ℝ) × (K → ℝ) => E.demand i r.2 (dot r.2 (r.1 i)))
        (xh, ph) := ContinuousAt.comp_of_eq (g := fun q : (K → ℝ) × ℝ => E.demand i q.1 q.2)
          (f := fun r : (N → K → ℝ) × (K → ℝ) => (r.2, dot r.2 (r.1 i))) h2 h1 rfl
    exact h3.sub ((continuous_apply i).comp continuous_fst).continuousAt
  have hBc : ∀ t : ℝ, ContinuousAt B ((xh, ph), t) := fun t => by
    have hZc' : ContinuousAt (fun s : ((N → K → ℝ) × (K → ℝ)) × ℝ => Z s.1) ((xh, ph), t) :=
      ContinuousAt.comp (f := Prod.fst) (g := Z) hZc continuous_fst.continuousAt
    have hj : ContinuousAt (fun s : ((N → K → ℝ) × (K → ℝ)) × ℝ => s.1.1 j) ((xh, ph), t) :=
      ((continuous_apply j).comp (continuous_fst.comp continuous_fst)).continuousAt
    exact hj.sub (continuous_snd.continuousAt.smul hZc')
  have hBval : ∀ t, B ((xh, ph), t) = xh j - t • zh := fun t => rfl
  have hFc : ∀ t ∈ Icc (Δ₁ / 2) Δ₁, ContinuousAt F ((xh, ph), t) := by
    intro t ht
    have hu1 : ContinuousAt (u j) (B ((xh, ph), t)) :=
      (hu.cont j).continuousAt (interior_mem_nhds (by rw [hBval]; exact (hgood t ht).2))
    have hu2 : ContinuousAt (u j) (xh j) := (hu.cont j).continuousAt (interior_mem_nhds (hint j))
    have hc1 : ContinuousAt (fun s : ((N → K → ℝ) × (K → ℝ)) × ℝ => u j (B s)) ((xh, ph), t) :=
      ContinuousAt.comp (f := B) (g := u j) hu1 (hBc t)
    have hc2 : ContinuousAt (fun s : ((N → K → ℝ) × (K → ℝ)) × ℝ => u j (s.1.1 j))
        ((xh, ph), t) :=
      ContinuousAt.comp (f := fun s : ((N → K → ℝ) × (K → ℝ)) × ℝ => s.1.1 j) (g := u j) hu2
        ((continuous_apply j).comp (continuous_fst.comp continuous_fst)).continuousAt
    exact hc1.sub hc2
  have hFpos : ∀ t ∈ Icc (Δ₁ / 2) Δ₁, 0 < F ((xh, ph), t) := fun t ht => by
    simp only [hFdef, hBval]
    linarith [(hgood t ht).1]
  -- a uniform positive gain ε on the compact range of trade sizes
  have hIne : (Icc (Δ₁ / 2) Δ₁).Nonempty := ⟨Δ₁, by constructor <;> linarith, le_rfl⟩
  obtain ⟨tmin, htmin, hmin⟩ := (isCompact_Icc (a := Δ₁ / 2) (b := Δ₁)).exists_isMinOn hIne
    (fun t ht => ((hFc t ht).comp (Continuous.prodMk_right (xh, ph)).continuousAt).continuousWithinAt)
  rw [isMinOn_iff] at hmin
  set ε := F ((xh, ph), tmin) / 2 with hεdef
  have hε : 0 < ε := by have := hFpos tmin htmin; rw [hεdef]; linarith
  -- tube lemma: the gain stays above ε and j's bundle stays interior near (xh, ph)
  have htube : ∀ᶠ r in 𝓝 (xh, ph), ∀ t ∈ Icc (Δ₁ / 2) Δ₁,
      ε < F (r, t) ∧ B (r, t) ∈ {y : K → ℝ | ∀ k, 0 < y k} := by
    refine (isCompact_Icc).eventually_forall_of_forall_eventually fun t ht => ?_
    have hF := (hFc t ht).eventually (lt_mem_nhds (show ε < F ((xh, ph), t) by
      have := hmin t ht
      have := hFpos tmin htmin
      simp only [Function.comp_apply] at *
      linarith))
    have hB := (hBc t).preimage_mem_nhds (hopenI.mem_nhds ((hgood t ht).2))
    filter_upwards [hF, hB] with s hs1 hs2
    exact ⟨hs1, hs2⟩
  refine ⟨i, j, hij', ph, hph, hphW, Δ₁, hΔ₁0, hΔ₁1, ε, hε, ?_⟩
  filter_upwards [htube] with r hr
  intro ω hωv hP hp hΔ hhead hrS
  obtain ⟨hFr, hBr⟩ := hr ω.Δ hΔ
  have hexc : E.excess r.1 ω = Z r := by
    simp only [excess, hZdef, hP, hp]
  have hbundle : r.1 j - ω.Δ • E.excess r.1 ω = B (r, ω.Δ) := by
    rw [hexc]
  have hr0 : ∀ i, 0 ≤ r.1 i := hrS.1.1
  -- j accepts, so j is the responder
  have hacc : E.Accepts r.1 ω j = true := by
    simp only [Accepts, decide_eq_true_eq]
    refine ⟨by rw [hP]; exact hij'.symm, by rw [hbundle]; exact fun k => (hBr k).le, ?_⟩
    rw [hbundle]
    intro hR
    have := (hu.rep j (r.1 j) (B (r, ω.Δ)) (hr0 j) fun k => (hBr k).le).1 hR
    simp only [hFdef] at hFr
    linarith
  obtain ⟨rest, hrest⟩ : ∃ rest, ω.order = j :: rest := by
    cases h : ω.order with
    | nil => rw [h] at hhead; simp at hhead
    | cons a rest =>
      rw [h] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      exact ⟨rest, by rw [hhead]⟩
  have hresp : E.responder r.1 ω = some j := by
    simp [responder, hrest, List.find?_cons, hacc]
  have hstepj : E.step r.1 ω j = r.1 j - ω.Δ • E.excess r.1 ω := by
    simp only [step, hresp, Function.update_self]
  -- the sum of utilities rises by at least ε
  have hall : ∀ k ∈ (univ : Finset N), 0 ≤ u k (E.step r.1 ω k) - u k (r.1 k) := fun k _ =>
    sub_nonneg.2 (step_improves hu hr0 hωv k)
  have hj := Finset.single_le_sum hall (mem_univ j)
  rw [hstepj, hbundle] at hj
  simp only [hFdef] at hFr
  simp only [totalU]
  have : ∑ k, (u k (E.step r.1 ω k) - u k (r.1 k)) =
      ∑ k, u k (E.step r.1 ω k) - ∑ k, u k (r.1 k) := Finset.sum_sub_distrib _ _
  linarith

end Economy

end Yq
