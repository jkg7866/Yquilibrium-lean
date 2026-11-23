/-
  Continuity of demand (Berge's maximum theorem, strictly quasiconcave case), used in Step 1
  of the proof of Theorem 4.
-/
import Yquilibrium.Convergence

open Finset Set Filter Topology

noncomputable section

namespace Yq

namespace Economy

variable {K N : Type*} [Fintype K] [Fintype N] {E : Economy N K} {u : N → (K → ℝ) → ℝ}

lemma dot_continuous_pair : Continuous fun q : (K → ℝ) × (K → ℝ) => dot q.1 q.2 := by
  unfold dot
  exact continuous_finsetSum _ fun k _ =>
    ((continuous_apply k).comp continuous_fst).mul ((continuous_apply k).comp continuous_snd)

lemma u_zero_le_of_dynRep (hu : E.DynRep u) (i : N) {x : K → ℝ} (hx : 0 ≤ x) :
    u i 0 ≤ u i x :=
  (hu.rep i x 0 hx le_rfl).1 ((E.pref i).weak_mono le_rfl hx)

/-- **Berge**: demand is continuous at every `(p, m)` with `p ≫ 0` and `m > 0`. -/
theorem demand_continuousAt (hu : E.DynRep u) (i : N) {p₀ : K → ℝ} (hp₀ : ∀ k, 0 < p₀ k)
    {m₀ : ℝ} (hm₀ : 0 < m₀) :
    ContinuousAt (fun q : (K → ℝ) × ℝ => E.demand i q.1 q.2) (p₀, m₀) := by
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro s hs
  -- eventually the prices are bounded below and the incomes above
  have hp1 : ∀ k, ∀ᶠ n in atTop, p₀ k / 2 < (s n).1 k := fun k =>
    ((continuous_apply k).tendsto p₀).comp ((continuous_fst.tendsto _).comp hs)
      |>.eventually (lt_mem_nhds (by linarith [hp₀ k]))
  have hp1' : ∀ᶠ n in atTop, ∀ k, p₀ k / 2 < (s n).1 k := eventually_all.2 hp1
  have hm1 : ∀ᶠ n in atTop, (s n).2 < 2 * m₀ :=
    ((continuous_snd.tendsto _).comp hs).eventually (gt_mem_nhds (by linarith))
  have hm2 : ∀ᶠ n in atTop, 0 < (s n).2 :=
    ((continuous_snd.tendsto _).comp hs).eventually (lt_mem_nhds hm₀)
  have hspec : ∀ᶠ n in atTop, Optimal (E.pref i) (s n).1 (s n).2 (E.demand i (s n).1 (s n).2) := by
    filter_upwards [hp1', hm2] with n hn hn2
    refine demand_spec hu i (fun k => ?_) hn2.le
    have := hn k
    have := hp₀ k
    linarith
  -- eventually demand lies in a fixed compact box
  have hbox : ∀ᶠ n in atTop, E.demand i (s n).1 (s n).2 ∈
      Set.pi univ (fun k => Icc (0 : ℝ) (4 * m₀ / p₀ k)) := by
    filter_upwards [hp1', hm1, hspec] with n hn hn1 hopt
    intro k _
    have hposall : ∀ k, 0 < (s n).1 k := fun k => by
      have := hn k
      have := hp₀ k
      linarith
    refine ⟨hopt.1 k, ?_⟩
    have h1 := mul_le_dot (fun k => (hposall k).le) hopt.1 k
    have h2 := hopt.2.1
    rw [le_div_iff₀ (hp₀ k)]
    have h3 : (s n).1 k * E.demand i (s n).1 (s n).2 k ≤ 2 * m₀ := by linarith
    have h4 : p₀ k / 2 * E.demand i (s n).1 (s n).2 k ≤ (s n).1 k * E.demand i (s n).1 (s n).2 k :=
      mul_le_mul_of_nonneg_right (hn k).le (hopt.1 k)
    nlinarith
  refine (isCompact_univ_pi fun k => isCompact_Icc).tendsto_nhds_of_unique_mapClusterPt hbox ?_
  intro d hdB hd
  obtain ⟨ψ, hψ, hlim⟩ := hd.tendsto_subseq
  have hsψ : Tendsto (s ∘ ψ) atTop (𝓝 (p₀, m₀)) := hs.comp hψ.tendsto_atTop
  have hspecψ := hψ.tendsto_atTop.eventually hspec
  have hd0 : 0 ≤ d := fun k => (hdB k (mem_univ k)).1
  -- the limit is affordable
  have hdm : dot p₀ d ≤ m₀ := by
    have h1 : Tendsto (fun n => dot (s (ψ n)).1 (E.demand i (s (ψ n)).1 (s (ψ n)).2)) atTop
        (𝓝 (dot p₀ d)) :=
      (dot_continuous_pair.tendsto (p₀, d)).comp
        (((continuous_fst.tendsto _).comp hsψ).prodMk_nhds hlim)
    have h2 : Tendsto (fun n => (s (ψ n)).2) atTop (𝓝 m₀) := (continuous_snd.tendsto _).comp hsψ
    exact le_of_tendsto_of_tendsto h1 h2 (hspecψ.mono fun n h => h.2.1)
  -- the utility of demand converges to u(d)
  have hud : Tendsto (fun n => u i (E.demand i (s (ψ n)).1 (s (ψ n)).2)) atTop (𝓝 (u i d)) := by
    apply ((hu.cont i) d hd0).tendsto.comp
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hlim, hspecψ.mono fun n h => h.1⟩
  -- the limit is optimal at (p₀, m₀)
  have hopt : Optimal (E.pref i) p₀ m₀ d := by
    refine ⟨hd0, hdm, fun z hz hzm => (hu.rep i d z hd0 hz).2 ?_⟩
    -- for δ ∈ (0,1), (1-δ) z is eventually affordable along the sequence
    have hshrink : ∀ δ : ℝ, 0 < δ → δ < 1 → u i ((1 - δ) • z) ≤ u i d := by
      intro δ hδ0 hδ1
      have hz' : 0 ≤ (1 - δ) • z := fun k => by
        simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (by linarith) (hz k)
      have hcheap : dot p₀ ((1 - δ) • z) < m₀ := by
        rw [dot_smul_right]
        have := dot_nonneg (fun k => (hp₀ k).le) hz
        nlinarith
      have hev : ∀ᶠ n in atTop, dot (s (ψ n)).1 ((1 - δ) • z) < (s (ψ n)).2 := by
        have h1 : Tendsto (fun n => dot (s (ψ n)).1 ((1 - δ) • z)) atTop
            (𝓝 (dot p₀ ((1 - δ) • z))) :=
          ((continuous_dot_left continuous_id _).tendsto p₀).comp
            ((continuous_fst.tendsto _).comp hsψ)
        have h2 : Tendsto (fun n => (s (ψ n)).2) atTop (𝓝 m₀) :=
          (continuous_snd.tendsto _).comp hsψ
        exact h1.eventually_lt h2 hcheap
      refine ge_of_tendsto hud ?_
      filter_upwards [hev, hspecψ] with n hn hopt'
      exact (hu.rep i _ _ hopt'.1 hz').1 (hopt'.2.2 _ hz' hn.le)
    -- let δ → 0
    have hseq : Tendsto (fun n : ℕ => (1 - 1 / ((n : ℝ) + 2)) • z) atTop (𝓝 z) := by
      have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have := tendsto_one_div_succ.comp (tendsto_add_atTop_nat 1)
        refine this.congr fun n => ?_
        simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
        ring_nf
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub h2).smul_const z
    have hcz : Tendsto (fun n : ℕ => u i ((1 - 1 / ((n : ℝ) + 2)) • z)) atTop (𝓝 (u i z)) := by
      apply ((hu.cont i) z hz).tendsto.comp
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hseq, Eventually.of_forall fun n => ?_⟩
      show (0 : K → ℝ) ≤ _
      intro k
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      have : 1 / ((n : ℝ) + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      exact mul_nonneg (by linarith) (hz k)
    refine le_of_tendsto hcz (Eventually.of_forall fun n => hshrink _ (by positivity) ?_)
    have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith
  exact optimal_unique hu i hopt (demand_spec hu i hp₀ hm₀.le)

end Economy

end Yq
