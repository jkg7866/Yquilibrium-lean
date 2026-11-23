/-
  First-order conditions for Theorem 4, Step 1: necessity at interior optima, sufficiency under
  quasiconcavity (Arrow–Enthoven), and strict improvement along a direction of positive
  derivative.
-/
import Yquilibrium.Berge
import Yquilibrium.Imports3
import Mathlib.Analysis.Calculus.Deriv.Mul

open Finset Set Filter Topology

noncomputable section

namespace Yq

variable {K : Type*} [Fintype K]

/-- The derivative along a line. -/
lemma hasDerivAt_line {f : (K → ℝ) → ℝ} {L : (K → ℝ) →L[ℝ] ℝ} {x : K → ℝ}
    (hf : HasFDerivAt f L x) (v : K → ℝ) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (L v) 0 := by
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt f L (x + (0 : ℝ) • v) := by simpa using hf
  exact hf'.comp_hasDerivAt (0 : ℝ) hline

/-- A positive derivative at `0` gives `g 0 < g t` for small `t > 0`. -/
lemma eventually_gt_of_deriv_pos {g : ℝ → ℝ} {d : ℝ} (h : HasDerivAt g d 0) (hd : 0 < d) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), g 0 < g t := by
  have hs := (hasDerivAt_iff_tendsto_slope.1 h).eventually (lt_mem_nhds hd)
  filter_upwards [nhdsGT_le_nhdsNE 0 hs, self_mem_nhdsWithin] with t ht htpos
  rw [slope_def_field, sub_zero] at ht
  have htpos' : (0 : ℝ) < t := htpos
  have := (lt_div_iff₀ htpos').1 ht
  linarith

/-- A negative derivative at `0` gives `g t < g 0` for small `t > 0`. -/
lemma eventually_lt_of_deriv_neg {g : ℝ → ℝ} {d : ℝ} (h : HasDerivAt g d 0) (hd : d < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), g t < g 0 := by
  have hs := (hasDerivAt_iff_tendsto_slope.1 h).eventually (gt_mem_nhds hd)
  filter_upwards [nhdsGT_le_nhdsNE 0 hs, self_mem_nhdsWithin] with t ht htpos
  rw [slope_def_field, sub_zero] at ht
  have htpos' : (0 : ℝ) < t := htpos
  have := (div_lt_iff₀ htpos').1 ht
  linarith

namespace Economy

variable {N : Type*} [Fintype N] {E : Economy N K} {u : N → (K → ℝ) → ℝ}

/-- **Necessary first-order condition**: if an interior bundle is optimal at prices `p ≫ 0` and
  its own value, the gradient is proportional to `p`: `gₖ pₗ = gₗ pₖ`. -/
theorem foc_of_optimal (hu : E.DynRep u) (i : N) {x : K → ℝ} (hx : ∀ k, 0 < x k)
    {p : K → ℝ} (hopt : Optimal (E.pref i) p (dot p x) x)
    {L : (K → ℝ) →L[ℝ] ℝ} {g : K → ℝ} (hL : HasFDerivAt (u i) L x) (hLg : ∀ v, L v = dot g v)
    (k l : K) : g k * p l = g l * p k := by
  classical
  set v : K → ℝ := fun m => (if m = k then p l else 0) - (if m = l then p k else 0) with hvdef
  have hpv : dot p v = 0 := by
    simp only [hvdef, dot, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hgv : dot g v = g k * p l - g l * p k := by
    simp only [hvdef, dot, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- t ↦ u(x + t v) has a local maximum at 0
  have hmax : IsLocalMax (fun t : ℝ => u i (x + t • v)) 0 := by
    have hcont : Continuous fun t : ℝ => x + t • v := continuous_const.add
      (continuous_id.smul continuous_const)
    have hopen : IsOpen {y : K → ℝ | ∀ k, 0 < y k} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun k => isOpen_lt continuous_const (continuous_apply k)
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • v ∈ {y : K → ℝ | ∀ k, 0 < y k} :=
      hcont.continuousAt.preimage_mem_nhds (hopen.mem_nhds
        (show x + (0 : ℝ) • v ∈ {y : K → ℝ | ∀ k, 0 < y k} by simpa using hx))
    filter_upwards [hev] with t ht
    have ht0 : 0 ≤ x + t • v := fun k => (ht k).le
    have hval : dot p (x + t • v) ≤ dot p x := by
      rw [show x + t • v = x + t • v from rfl]
      have : dot p (x + t • v) = dot p x + t * dot p v := by
        simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
          Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this, hpv, mul_zero, add_zero]
    have := (hu.rep i x _ (fun k => (hx k).le) ht0).1 (hopt.2.2 _ ht0 hval)
    simpa using this
  have h0 := hmax.hasDerivAt_eq_zero (hasDerivAt_line hL v)
  rw [hLg, hgv] at h0
  linarith

/-- **Arrow–Enthoven sufficiency**: an interior bundle whose gradient is a positive multiple of
  `p ≫ 0` is optimal at `p` and its own value, by quasiconcavity. -/
theorem optimal_of_foc (hu : E.DynRep u) (i : N) {x : K → ℝ} (hx : ∀ k, 0 < x k)
    {L : (K → ℝ) →L[ℝ] ℝ} {g : K → ℝ} (hL : HasFDerivAt (u i) L x) (hLg : ∀ v, L v = dot g v)
    {p : K → ℝ} (hp : ∀ k, 0 < p k) {c : ℝ} (hc : 0 < c) (hgp : g = c • p) :
    Optimal (E.pref i) p (dot p x) x := by
  have hx0 : 0 ≤ x := fun k => (hx k).le
  refine ⟨hx0, le_rfl, fun y hy hym => (hu.rep i x y hx0 hy).2 ?_⟩
  by_contra hlt
  push_neg at hlt
  have hyne : y ≠ 0 := by
    rintro rfl
    have := u_zero_le_of_dynRep hu i hx0
    linarith
  -- shrink y slightly, keeping it strictly better than x
  have hseq : Tendsto (fun n : ℕ => (1 - 1 / ((n : ℝ) + 2)) • y) atTop (𝓝 y) := by
    have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := tendsto_one_div_succ.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      ring_nf
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub h2).smul_const y
  have hnn : ∀ n : ℕ, 0 ≤ (1 - 1 / ((n : ℝ) + 2)) • y := fun n k => by
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
    have : 1 / ((n : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact mul_nonneg (by linarith) (hy k)
  have hcu : Tendsto (fun n : ℕ => u i ((1 - 1 / ((n : ℝ) + 2)) • y)) atTop (𝓝 (u i y)) := by
    apply ((hu.cont i) y hy).tendsto.comp
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hseq, Eventually.of_forall hnn⟩
  obtain ⟨n, hn⟩ := (hcu.eventually (lt_mem_nhds hlt)).exists
  set δ : ℝ := 1 / ((n : ℝ) + 2) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by
    rw [hδ, div_lt_one (by positivity)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  set y' := (1 - δ) • y with hy'
  have hy'0 : 0 ≤ y' := hnn n
  have hpy : 0 < dot p y := dot_pos hp hy hyne
  have hcheap : dot p y' < dot p x := by
    rw [hy', dot_smul_right]
    nlinarith
  -- the derivative of u along y' − x is negative
  have hd : L (y' - x) < 0 := by
    rw [hLg, hgp, dot_smul_left]
    have : dot p (y' - x) = dot p y' - dot p x := by
      simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [this]
    nlinarith
  obtain ⟨t, ht, ht1⟩ := ((eventually_lt_of_deriv_neg (hasDerivAt_line hL (y' - x)) hd).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  simp only [zero_smul, add_zero] at ht
  -- but quasiconcavity gives u(x + t(y' − x)) ≥ u(x)
  have hmix : x + t • (y' - x) = t • y' + (1 - t) • x := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hq := hu.qc i hy'0 hx0 ht1.1.le ht1.2.le
  rw [← hmix, min_eq_right hn.le] at hq
  linarith

end Economy

end Yq
