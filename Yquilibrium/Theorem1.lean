/-
  Yquilibrium (Goeree, 21 Nov 2026), Appendix A.
  Lemma 2 (free goods) and Theorem 1 (existence, p ≫ 0, Pareto optimality).
-/
import Yquilibrium.Basic

open Finset Filter Topology Set

noncomputable section

namespace Yq

variable {K : Type*} [Fintype K]
variable {P : Pref K}

/-! ### Lemma 2 -/

/-- The indicator vector `d` of the free goods `Z = {k | pₖ = 0}`. -/
def zeroInd (p : K → ℝ) : K → ℝ := fun k => if p k = 0 then 1 else 0

lemma zeroInd_nonneg (p : K → ℝ) : 0 ≤ zeroInd p := fun k => by
  unfold zeroInd
  split_ifs <;> norm_num

/-- Lemma 2(i), in finite form: if every `ε`-cheap bundle `z ≿ x` contains at least `H` of the
  directions `d`, then `μ(p + t d, x) ≥ μ(p, x) + min (t H) ε`. -/
theorem mu_perturb {p d x : K → ℝ} (hx : 0 ≤ x) (hd : 0 ≤ d) {ε H t : ℝ} (ht : 0 ≤ t)
    (hp : 0 ≤ p) (hH : ∀ z, 0 ≤ z → P.R z x → dot p z ≤ mu P p x + ε → H ≤ dot d z) :
    mu P p x + min (t * H) ε ≤ mu P (p + t • d) x := by
  apply le_mu hx
  intro z hz hzx
  rw [dot_add_left, dot_smul_left]
  have hdz := dot_nonneg hd hz
  have hmz := mu_le hp hz hzx
  by_cases hc : dot p z ≤ mu P p x + ε
  · have h1 : t * H ≤ t * dot d z := mul_le_mul_of_nonneg_left (hH z hz hzx hc) ht
    have := min_le_left (t * H) ε
    linarith
  · have := min_le_right (t * H) ε
    have : 0 ≤ t * dot d z := mul_nonneg ht hdz
    push_neg at hc
    linarith

/-- Lemma 2(ii), in finite form: if `μ(p, x) > 0` and some good is free, then nearly-cheapest
  bundles `z ≿ x` contain arbitrarily large amounts of free goods. -/
theorem free_large {p x : K → ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x) {k₀ : K} (hk₀ : p k₀ = 0)
    (hmu : 0 < mu P p x) (M : ℝ) :
    ∃ ε > 0, ∀ z, 0 ≤ z → P.R z x → dot p z ≤ mu P p x + ε → M ≤ dot (zeroInd p) z := by
  classical
  by_contra hcon
  push_neg at hcon
  choose z hz0 hzx hzc hzd using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  -- the sequence lies in a box
  have hbox : ∀ n, z n ∈ Set.pi univ
      (fun k => Icc (0 : ℝ) (max M ((mu P p x + 1) / p k))) := by
    intro n k _
    refine ⟨hz0 n k, ?_⟩
    by_cases hk : p k = 0
    · have h1 := mul_le_dot (zeroInd_nonneg p) (hz0 n) k
      simp only [zeroInd, hk, ite_true, one_mul] at h1
      exact le_max_of_le_left (by linarith [hzd n])
    · have hpk : 0 < p k := lt_of_le_of_ne (hp k) (Ne.symm hk)
      have h1 := mul_le_dot hp (hz0 n) k
      have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      refine le_max_of_le_right ?_
      rw [le_div_iff₀ hpk]
      linarith [hzc n]
  obtain ⟨zs, hzs, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun k => isCompact_Icc).tendsto_subseq hbox
  have hzs0 : 0 ≤ zs := fun k => (hzs k (mem_univ k)).1
  have hzsx : P.R zs x := ((P.upper_closed x hx).mem_of_tendsto hlim
    (Eventually.of_forall fun n => ⟨hz0 (φ n), hzx (φ n)⟩)).2
  -- the limit is a cheapest bundle
  have hcost : dot p zs ≤ mu P p x := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    apply le_of_tendsto ((continuous_dot_right p).continuousAt.tendsto.comp hlim)
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : 1 / ((φ n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    simp only [Function.comp_apply]
    linarith [hzc (φ n)]
  have hmu_le := mu_le hp hzs0 hzsx
  -- some good with a positive price is held
  obtain ⟨j, hj⟩ : ∃ j, 0 < p j * zs j := by
    by_contra h
    push_neg at h
    have : dot p zs ≤ 0 := Finset.sum_nonpos fun j _ => h j
    linarith
  have hpj : 0 < p j := lt_of_le_of_ne (hp j) fun h => by
    rw [← h, zero_mul] at hj
    exact lt_irrefl _ hj
  have hzsj : 0 < zs j := lt_of_le_of_ne (hzs0 j) fun h => by
    rw [← h, mul_zero] at hj
    exact lt_irrefl _ hj
  have hjk : j ≠ k₀ := fun h => by
    rw [h, hk₀] at hpj
    exact lt_irrefl _ hpj
  have hx0 : ¬ P.R 0 x := fun h => by
    have := mu_le hp le_rfl h
    rw [dot_zero_right] at this
    linarith
  have hzs_strict : ¬ P.R 0 zs := fun h => hx0 (P.trans 0 zs x le_rfl hzs0 hx h hzsx)
  -- add one unit of the free good k₀: strictly better
  set w : K → ℝ := fun i => zs i + (if i = k₀ then 1 else 0) with hw
  have hw0 : 0 ≤ w := fun i => by
    have := hzs0 i
    simp only [hw, Pi.zero_apply] at this ⊢
    split_ifs <;> linarith
  have hzw : ¬ P.R zs w := P.mono' zs w hzs0 hzs_strict
    (fun i => by simp only [hw]; split_ifs <;> linarith)
    (fun h => by
      have := congrFun h k₀
      simp [hw] at this)
  have hxw : ¬ P.R x w := P.strict_of_strict_weak hx hzs0 hw0 hzw hzsx
  -- then remove a little of the priced good j: still better than x, but cheaper
  have hη : Tendsto (fun n : ℕ => zs j * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_succ.const_mul (zs j)
  have hlim2 : Tendsto (fun n : ℕ => fun i => w i - (if i = j then zs j * (1 / ((n : ℝ) + 1))
      else 0)) atTop (𝓝 w) := by
    rw [tendsto_pi_nhds]
    intro i
    by_cases hi : i = j
    · simp only [hi, ite_true]
      simpa using (tendsto_const_nhds (x := w j)).sub hη
    · simp only [hi, ite_false, sub_zero]
      exact tendsto_const_nhds
  obtain ⟨n, hn⟩ := (hlim2.eventually
    ((P.lower_closed x hx).isOpen_compl.mem_nhds fun h => hxw h.2)).exists
  have hn1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hn2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hwn0 : (0 : K → ℝ) ≤ fun i => w i - (if i = j then zs j * (1 / ((n : ℝ) + 1)) else 0) :=
    fun i => by
      have h0 := hzs0 i
      simp only [hw, Pi.zero_apply] at h0 ⊢
      by_cases hi : i = j
      · subst hi
        simp only [hjk, ite_false, ite_true, add_zero]
        nlinarith
      · simp only [hi, ite_false, sub_zero]
        split_ifs <;> linarith
  have hR := P.of_not hx hwn0 fun h => hn ⟨hwn0, h⟩
  have hcost' : dot p (fun i => w i - (if i = j then zs j * (1 / ((n : ℝ) + 1)) else 0)) =
      dot p zs - p j * (zs j * (1 / ((n : ℝ) + 1))) := by
    simp only [dot, hw, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hk₀, add_zero]
  have hle := mu_le hp hwn0 hR
  rw [hcost'] at hle
  have : 0 < p j * (zs j * (1 / ((n : ℝ) + 1))) := by positivity
  linarith

/-! ### The economy -/

variable {N : Type*} [Fintype N]

/-- An exchange economy: preferences and strictly positive endowments. -/
structure Economy (N K : Type*) [Fintype N] [Fintype K] where
  pref : N → Pref K
  ω : N → K → ℝ
  ω_pos : ∀ i k, 0 < ω i k

namespace Economy

variable (E : Economy N K)

/-- Total resources `W`. -/
def W : K → ℝ := fun k => ∑ i, E.ω i k

/-- Feasible allocations `F(W)`. -/
def Feasible (x : N → K → ℝ) : Prop := (∀ i, 0 ≤ x i) ∧ ∀ k, ∑ i, x i k ≤ E.W k

/-- Prices `Σ_K(W)`. -/
def Prices : Set (K → ℝ) := {p | 0 ≤ p ∧ dot p E.W = 1}

/-- The potential `Y(x,p) = 1 - ∑ᵢ μᵢ(p, xᵢ)`. -/
def Y (x : N → K → ℝ) (p : K → ℝ) : ℝ := 1 - ∑ i, mu (E.pref i) p (x i)

/-- Individual rationality. -/
def IR (x : N → K → ℝ) : Prop := ∀ i, (E.pref i).R (x i) (E.ω i)

/-- A Yquilibrium (Definition 2). -/
def IsYq (x : N → K → ℝ) (p : K → ℝ) : Prop :=
  E.Feasible x ∧ p ∈ E.Prices ∧
    ∀ x' p', E.Feasible x' → p' ∈ E.Prices → E.Y x p ≤ E.Y x' p'

/-- An individually-rational Yquilibrium (Definition 2). -/
def IsYqIR (x : N → K → ℝ) (p : K → ℝ) : Prop :=
  E.Feasible x ∧ E.IR x ∧ p ∈ E.Prices ∧
    ∀ x' p', E.Feasible x' → E.IR x' → p' ∈ E.Prices → E.Y x p ≤ E.Y x' p'

/-- (Strong) Pareto optimality. -/
def ParetoOptimal (x : N → K → ℝ) : Prop :=
  E.Feasible x ∧ ¬ ∃ x', E.Feasible x' ∧ (∀ i, (E.pref i).R (x' i) (x i)) ∧
    ∃ j, ¬ (E.pref j).R (x j) (x' j)

lemma ω_nonneg (i : N) : 0 ≤ E.ω i := fun k => (E.ω_pos i k).le

lemma W_pos [Nonempty N] (k : K) : 0 < E.W k :=
  Finset.sum_pos (fun i _ => E.ω_pos i k) Finset.univ_nonempty

lemma W_nonneg : 0 ≤ E.W := fun k => Finset.sum_nonneg fun i _ => (E.ω_pos i k).le

lemma ω_feasible : E.Feasible E.ω := ⟨E.ω_nonneg, fun k => le_rfl⟩

lemma ω_IR : E.IR E.ω := fun i => (E.pref i).refl (E.ω_nonneg i)

/-- A strictly positive price in `Σ_K(W)`. -/
def p0 : K → ℝ := fun _ => 1 / ∑ k, E.W k

lemma p0_pos [Nonempty N] [Nonempty K] (k : K) : 0 < E.p0 k := by
  have : 0 < ∑ k, E.W k := Finset.sum_pos (fun k _ => E.W_pos k) Finset.univ_nonempty
  exact div_pos one_pos this

lemma p0_mem [Nonempty N] [Nonempty K] : E.p0 ∈ E.Prices := by
  refine ⟨fun k => (E.p0_pos k).le, ?_⟩
  have : 0 < ∑ k, E.W k := Finset.sum_pos (fun k _ => E.W_pos k) Finset.univ_nonempty
  simp only [dot, p0, ← Finset.mul_sum]
  field_simp

lemma isClosed_feasible : IsClosed {x | E.Feasible x} := by
  have h1 : IsClosed {x : N → K → ℝ | ∀ i, 0 ≤ x i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {x : N → K → ℝ | ∀ k, ∑ i, x i k ≤ E.W k} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun k => isClosed_le
      (continuous_finsetSum _ fun i _ => (continuous_apply k).comp (continuous_apply i))
      continuous_const
  exact h1.inter h2

lemma isCompact_feasible : IsCompact {x | E.Feasible x} := by
  refine (isCompact_univ_pi fun i => isCompact_univ_pi fun k =>
    isCompact_Icc (a := (0 : ℝ)) (b := E.W k)).of_isClosed_subset E.isClosed_feasible ?_
  rintro x ⟨hx0, hxW⟩ i _ k _
  exact ⟨hx0 i k, (Finset.single_le_sum (f := fun j => x j k) (fun j _ => hx0 j k)
    (mem_univ i)).trans (hxW k)⟩

lemma isCompact_feasible_IR : IsCompact {x | E.Feasible x ∧ E.IR x} := by
  refine E.isCompact_feasible.of_isClosed_subset ?_ fun x h => h.1
  have : {x | E.Feasible x ∧ E.IR x} = {x | E.Feasible x} ∩
      ⋂ i, (fun x : N → K → ℝ => x i) ⁻¹' {z | 0 ≤ z ∧ (E.pref i).R z (E.ω i)} := by
    ext x
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter, Set.mem_preimage]
    constructor
    · rintro ⟨hF, hIR⟩
      exact ⟨hF, fun i => ⟨hF.1 i, hIR i⟩⟩
    · rintro ⟨hF, h⟩
      exact ⟨hF, fun i => (h i).2⟩
  rw [this]
  exact E.isClosed_feasible.inter (isClosed_iInter fun i =>
    ((E.pref i).upper_closed _ (E.ω_nonneg i)).preimage (continuous_apply i))

lemma isCompact_prices [Nonempty N] : IsCompact E.Prices := by
  refine (isCompact_univ_pi fun k =>
    isCompact_Icc (a := (0 : ℝ)) (b := 1 / E.W k)).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_const continuous_id).inter
      (isClosed_eq (continuous_dot_left continuous_id E.W) continuous_const)
  · rintro p ⟨hp0, hpW⟩ k _
    refine ⟨hp0 k, ?_⟩
    rw [le_div_iff₀ (E.W_pos k)]
    have := mul_le_dot hp0 E.W_nonneg k
    linarith

/-! ### Theorem 1, for minimizers over a general domain `C` -/

section General

variable (C : Set (N → K → ℝ)) (hCF : ∀ x ∈ C, E.Feasible x)
include hCF

/-- Existence of a minimizer of the potential on `C × Σ_K(W)`. -/
theorem exists_min [Nonempty N] [Nonempty K] (hC : IsCompact C) (hωC : E.ω ∈ C) :
    ∃ x ∈ C, ∃ p ∈ E.Prices, ∀ x' ∈ C, ∀ p' ∈ E.Prices, E.Y x p ≤ E.Y x' p' := by
  have husc : UpperSemicontinuousOn
      (fun q : (N → K → ℝ) × (K → ℝ) => ∑ i, mu (E.pref i) q.2 (q.1 i)) (C ×ˢ E.Prices) := by
    intro q hq
    exact upperSemicontinuousWithinAt_sum fun i _ =>
      mu_usc (P := E.pref i) (s := C ×ˢ E.Prices) continuous_snd ((continuous_apply i).comp continuous_fst)
        (fun a ha => ha.2.1) (fun a ha => (hCF _ ha.1).1 i) q hq
  obtain ⟨⟨x, p⟩, ⟨hx, hp⟩, hmax⟩ :=
    husc.exists_isMaxOn ⟨(E.ω, E.p0), show (E.ω, E.p0) ∈ C ×ˢ E.Prices from ⟨hωC, E.p0_mem⟩⟩ (hC.prod E.isCompact_prices)
  rw [isMaxOn_iff] at hmax
  refine ⟨x, hx, p, hp, fun x' hx' p' hp' => ?_⟩
  have := hmax (x', p') ⟨hx', hp'⟩
  simp only [Y]
  linarith

/-- Strictly positive prices at any minimizer. -/
theorem pos_of_min [Nonempty N] [Nonempty K] (hωC : E.ω ∈ C) {x : N → K → ℝ} {p : K → ℝ}
    (hx : x ∈ C) (hp : p ∈ E.Prices)
    (hmin : ∀ x' ∈ C, ∀ p' ∈ E.Prices, E.Y x p ≤ E.Y x' p') : ∀ k, 0 < p k := by
  classical
  have hp0 : 0 ≤ p := hp.1
  have hxF := hCF x hx
  have hmu0 : ∀ i, 0 ≤ mu (E.pref i) p (x i) := fun i => mu_nonneg hp0 (hxF.1 i)
  obtain ⟨S0, hS0⟩ : ∃ S0, S0 = ∑ i, mu (E.pref i) p (x i) := ⟨_, rfl⟩
  have hS0nn : 0 ≤ S0 := hS0 ▸ Finset.sum_nonneg fun i _ => hmu0 i
  -- Step 0: `S0 > 0`, since otherwise `Y(x,p) = 1 > Y(ω, p0)`.
  have hS0pos : 0 < S0 := by
    by_contra h
    push_neg at h
    have h1 := hmin E.ω hωC E.p0 E.p0_mem
    simp only [Y] at h1
    rw [← hS0] at h1
    obtain ⟨i0⟩ := ‹Nonempty N›
    have hpos : 0 < mu (E.pref i0) E.p0 (E.ω i0) := by
      have := mu_strict (P := E.pref i0) E.p0_pos le_rfl (E.ω_nonneg i0)
        ((E.pref i0).mono 0 (E.ω i0) le_rfl (E.ω_pos i0))
      have h0 := mu_nonneg (P := E.pref i0) (x := 0) E.p0_mem.1 le_rfl
      linarith
    have : mu (E.pref i0) E.p0 (E.ω i0) ≤ ∑ i, mu (E.pref i) E.p0 (E.ω i) :=
      Finset.single_le_sum (f := fun i => mu (E.pref i) E.p0 (E.ω i))
        (fun i _ => mu_nonneg E.p0_mem.1 (E.ω_nonneg i)) (mem_univ i0)
    linarith
  by_contra hcon
  push_neg at hcon
  obtain ⟨k₀, hk₀⟩ := hcon
  have hk₀' : p k₀ = 0 := le_antisymm hk₀ (hp0 k₀)
  have hd := zeroInd_nonneg p
  have hD : 0 < dot (zeroInd p) E.W := by
    have h1 := mul_le_dot hd E.W_nonneg k₀
    simp only [zeroInd, hk₀', ite_true, one_mul] at h1
    linarith [E.W_pos k₀]
  obtain ⟨D, hDdef⟩ : ∃ D, D = dot (zeroInd p) E.W := ⟨_, rfl⟩
  rw [← hDdef] at hD
  -- raising the free prices raises some consumer's minimum income at an infinite rate
  obtain ⟨j, hj⟩ : ∃ j, 0 < mu (E.pref j) p (x j) := by
    by_contra h
    push_neg at h
    have : S0 ≤ 0 := hS0 ▸ Finset.sum_nonpos fun i _ => h i
    linarith
  have hM : 0 < D * S0 + 1 := by positivity
  obtain ⟨ε, hε, hεM⟩ := free_large (P := E.pref j) hp0 (hxF.1 j) hk₀' hj (D * S0 + 1)
  have ht : 0 < ε / (D * S0 + 1) := div_pos hε hM
  obtain ⟨t, htdef⟩ : ∃ t, t = ε / (D * S0 + 1) := ⟨_, rfl⟩
  rw [← htdef] at ht
  have htM : t * (D * S0 + 1) = ε := by rw [htdef]; field_simp
  have base : ∀ i, mu (E.pref i) p (x i) ≤ mu (E.pref i) (p + t • zeroInd p) (x i) := by
    intro i
    have := mu_perturb (P := E.pref i) (hxF.1 i) hd (ε := 1) (H := 0) ht.le hp0
      (fun z hz _ _ => dot_nonneg hd hz)
    simpa using this
  have hjj := mu_perturb (P := E.pref j) (hxF.1 j) hd ht.le hp0 hεM
  rw [htM, min_self] at hjj
  have hsum : S0 + ε ≤ ∑ i, mu (E.pref i) (p + t • zeroInd p) (x i) := by
    calc S0 + ε = ∑ i, (mu (E.pref i) p (x i) + if i = j then ε else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp [hS0]
      _ ≤ _ := Finset.sum_le_sum fun i _ => by
          split_ifs with h
          · subst h
            exact hjj
          · simpa using base i
  -- normalize the perturbed price
  have hc : 0 < 1 + t * D := by positivity
  have hpd0 : 0 ≤ p + t • zeroInd p := fun k => by
    simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (hp0 k) (mul_nonneg ht.le (hd k))
  have hp' : (1 + t * D)⁻¹ • (p + t • zeroInd p) ∈ E.Prices := by
    refine ⟨fun k => ?_, ?_⟩
    · simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 hc.le) (hpd0 k)
    · rw [dot_smul_left, dot_add_left, dot_smul_left, hp.2, ← hDdef, inv_mul_cancel₀ hc.ne']
  have h1 := hmin x hx _ hp'
  simp only [Y] at h1
  rw [Finset.sum_congr rfl fun i _ => mu_smul (P := E.pref i) (inv_nonneg.2 hc.le) hpd0 (hxF.1 i),
    ← Finset.mul_sum, ← hS0] at h1
  have h2 : S0 < (1 + t * D)⁻¹ * ∑ i, mu (E.pref i) (p + t • zeroInd p) (x i) := by
    rw [← div_eq_inv_mul, lt_div_iff₀ hc]
    have : t * D * S0 < ε := by nlinarith
    nlinarith
  linarith

/-- Pareto optimality of any minimizer with strictly positive prices, provided `C` is closed
  under Pareto improvements. -/
theorem pareto_of_min
    (hCup : ∀ x ∈ C, ∀ x', E.Feasible x' → (∀ i, (E.pref i).R (x' i) (x i)) → x' ∈ C)
    {x : N → K → ℝ} {p : K → ℝ} (hx : x ∈ C) (hp : p ∈ E.Prices)
    (hmin : ∀ x' ∈ C, ∀ p' ∈ E.Prices, E.Y x p ≤ E.Y x' p') (hpos : ∀ k, 0 < p k) :
    E.ParetoOptimal x := by
  refine ⟨hCF x hx, ?_⟩
  rintro ⟨x', hx'F, hge, j, hj⟩
  have hlt : ∑ i, mu (E.pref i) p (x i) < ∑ i, mu (E.pref i) p (x' i) :=
    Finset.sum_lt_sum
      (fun i _ => mu_mono_pref hp.1 ((hCF x hx).1 i) (hx'F.1 i) (hge i))
      ⟨j, mem_univ j, mu_strict hpos ((hCF x hx).1 j) (hx'F.1 j) hj⟩
  have := hmin x' (hCup x hx x' hx'F hge) p hp
  simp only [Y] at this
  linarith

end General

/-! ### Theorem 1 -/

/-- **Theorem 1.** The sets of Yquilibria and of individually-rational Yquilibria are non-empty,
  and every (individually-rational) Yquilibrium has a strictly positive price and a
  Pareto-optimal allocation. No convexity is assumed. -/
theorem theorem1 [Nonempty N] [Nonempty K] :
    (∃ x p, E.IsYq x p) ∧ (∃ x p, E.IsYqIR x p) ∧
    (∀ x p, E.IsYq x p → (∀ k, 0 < p k) ∧ E.ParetoOptimal x) ∧
    (∀ x p, E.IsYqIR x p → (∀ k, 0 < p k) ∧ E.ParetoOptimal x) := by
  have hF : ∀ x ∈ {x | E.Feasible x}, E.Feasible x := fun x h => h
  have hFI : ∀ x ∈ {x | E.Feasible x ∧ E.IR x}, E.Feasible x := fun x h => h.1
  have hupF : ∀ x ∈ {x | E.Feasible x}, ∀ x', E.Feasible x' →
      (∀ i, (E.pref i).R (x' i) (x i)) → x' ∈ {x | E.Feasible x} := fun _ _ x' h _ => h
  have hupFI : ∀ x ∈ {x | E.Feasible x ∧ E.IR x}, ∀ x', E.Feasible x' →
      (∀ i, (E.pref i).R (x' i) (x i)) → x' ∈ {x | E.Feasible x ∧ E.IR x} :=
    fun x hx x' hx' hge => ⟨hx', fun i => (E.pref i).trans _ _ _ (hx'.1 i) (hx.1.1 i)
      (E.ω_nonneg i) (hge i) (hx.2 i)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx, p, hp, hmin⟩ :=
      E.exists_min _ hF E.isCompact_feasible E.ω_feasible
    exact ⟨x, p, hx, hp, fun x' p' hx' hp' => hmin x' hx' p' hp'⟩
  · obtain ⟨x, hx, p, hp, hmin⟩ :=
      E.exists_min _ hFI E.isCompact_feasible_IR ⟨E.ω_feasible, E.ω_IR⟩
    exact ⟨x, p, hx.1, hx.2, hp, fun x' p' hx' hIR hp' => hmin x' ⟨hx', hIR⟩ p' hp'⟩
  · rintro x p ⟨hx, hp, hmin⟩
    have hmin' : ∀ x' ∈ {x | E.Feasible x}, ∀ p' ∈ E.Prices, E.Y x p ≤ E.Y x' p' :=
      fun x' hx' p' hp' => hmin x' p' hx' hp'
    have hpos := E.pos_of_min _ hF E.ω_feasible hx hp hmin'
    exact ⟨hpos, E.pareto_of_min _ hF hupF hx hp hmin' hpos⟩
  · rintro x p ⟨hx, hIR, hp, hmin⟩
    have hmin' : ∀ x' ∈ {x | E.Feasible x ∧ E.IR x}, ∀ p' ∈ E.Prices, E.Y x p ≤ E.Y x' p' :=
      fun x' hx' p' hp' => hmin x' p' hx'.1 hx'.2 hp'
    have hpos := E.pos_of_min _ hFI ⟨E.ω_feasible, E.ω_IR⟩ ⟨hx, hIR⟩ hp hmin'
    exact ⟨hpos, E.pareto_of_min _ hFI hupFI ⟨hx, hIR⟩ hp hmin' hpos⟩

end Economy

end Yq
