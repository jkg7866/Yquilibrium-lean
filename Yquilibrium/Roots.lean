/-
  Yquilibrium (Goeree, version of 23 Nov 2026), Appendix A.
  Lemma 3 (roots), Theorem 2(a)–(b) (Yquilibria for an income distribution, Walrasian
  equilibria) and Corollary 1(a) (first welfare theorem).
-/
import Yquilibrium.Theorem1

open Finset Filter Topology Set

noncomputable section

namespace Yq

variable {K : Type*} [Fintype K] {P : Pref K} {p x : K → ℝ} {m : ℝ}

lemma dot_add_const (p z : K → ℝ) (δ : ℝ) :
    dot p (fun k => z k + δ) = dot p z + δ * ∑ k, p k := by
  simp only [dot, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- If `⟨p|z⟩ < c` then `⟨p|z + δ𝟏⟩ < c` for some `δ > 0`. -/
lemma exists_shift_lt {p z : K → ℝ} {c : ℝ} (hp : 0 ≤ p) (h : dot p z < c) :
    ∃ δ > 0, dot p (fun k => z k + δ) < c := by
  have hσ : 0 ≤ ∑ k, p k := Finset.sum_nonneg fun k _ => hp k
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = (c - dot p z) / (2 * (∑ k, p k + 1)) := ⟨_, rfl⟩
  have hδ : 0 < δ := hδdef ▸ div_pos (by linarith) (by positivity)
  have h2 : δ * (2 * (∑ k, p k + 1)) = c - dot p z := by rw [hδdef]; field_simp
  refine ⟨δ, hδ, ?_⟩
  rw [dot_add_const]
  have : δ * ∑ k, p k < δ * (2 * (∑ k, p k + 1)) := mul_lt_mul_of_pos_left (by linarith) hδ
  linarith

/-- `x` is optimal in the budget set `B(p,m) = {z ≥ 0 | ⟨p|z⟩ ≤ m}`. -/
def Optimal (P : Pref K) (p : K → ℝ) (m : ℝ) (x : K → ℝ) : Prop :=
  0 ≤ x ∧ dot p x ≤ m ∧ ∀ z, 0 ≤ z → dot p z ≤ m → P.R x z

/-- Lemma 3(c), first part: an optimal bundle costs its full income, which equals the
  minimum income needed for it. -/
theorem optimal_mu (hp : 0 ≤ p) (h : Optimal P p m x) : mu P p x = dot p x ∧ dot p x = m := by
  obtain ⟨hx, hxm, hopt⟩ := h
  have hm : m ≤ mu P p x := by
    apply le_mu hx
    intro z hz hzx
    by_contra hlt
    push_neg at hlt
    obtain ⟨δ, hδ, hδc⟩ := exists_shift_lt hp hlt
    have hw0 : (0 : K → ℝ) ≤ fun k => z k + δ := fun k => by
      have := hz k
      simp only [Pi.zero_apply] at this ⊢
      linarith
    have hzw : ¬ P.R z (fun k => z k + δ) := P.mono z _ hz fun k => by linarith
    exact P.strict_of_strict_weak hx hz hw0 hzw hzx (hopt _ hw0 hδc.le)
  have h1 := mu_le_dot (P := P) hp hx
  exact ⟨by linarith, by linarith⟩

/-- Lemma 3(c), converse: at `p ≫ 0`, `μ(p,x) = ⟨p|x⟩` makes `x` optimal at income `⟨p|x⟩`. -/
theorem optimal_of_mu (hp : ∀ k, 0 < p k) (hx : 0 ≤ x) (h : mu P p x = dot p x) :
    Optimal P p (dot p x) x := by
  refine ⟨hx, le_rfl, fun y hy hyb => ?_⟩
  by_contra hxy
  have h1 := mu_strict hp hx hy hxy
  have h2 := mu_le_dot (P := P) (fun k => (hp k).le) hy
  linarith

namespace Economy

variable {N : Type*} [Fintype N] (E : Economy N K)

/-- Roots of the potential. -/
def IsRoot (x : N → K → ℝ) (p : K → ℝ) : Prop := E.Feasible x ∧ p ∈ E.Prices ∧ E.Y x p = 0

/-- Income distributions `Σ_N`. -/
def Incomes (m : N → ℝ) : Prop := (∀ i, 0 ≤ m i) ∧ ∑ i, m i = 1

/-- `𝓔(m)`: Walrasian equilibria for the income distribution `m`. -/
def IsWalrasianFor (m : N → ℝ) (x : N → K → ℝ) (p : K → ℝ) : Prop :=
  E.Feasible x ∧ p ∈ E.Prices ∧ ∀ i, Optimal (E.pref i) p (m i) (x i)

/-- Walrasian equilibria: incomes derive from endowments. -/
def IsWalrasian (x : N → K → ℝ) (p : K → ℝ) : Prop :=
  E.IsWalrasianFor (fun i => dot p (E.ω i)) x p

/-- `C_m`: feasible pairs whose bundles are worth `m`. -/
def CSet (m : N → ℝ) : Set ((N → K → ℝ) × (K → ℝ)) :=
  {q | E.Feasible q.1 ∧ q.2 ∈ E.Prices ∧ ∀ i, dot q.2 (q.1 i) = m i}

/-- `𝒴(m)`: Yquilibria for the income distribution `m` (Definition 3). -/
def IsYqFor (m : N → ℝ) (x : N → K → ℝ) (p : K → ℝ) : Prop :=
  (x, p) ∈ E.CSet m ∧ ∀ x' p', (x', p') ∈ E.CSet m → E.Y x p ≤ E.Y x' p'

/-- `𝒴⁺(m)`: individually-rational Yquilibria for the income distribution `m`. -/
def IsYqIRFor (m : N → ℝ) (x : N → K → ℝ) (p : K → ℝ) : Prop :=
  (x, p) ∈ E.CSet m ∧ E.IR x ∧
    ∀ x' p', (x', p') ∈ E.CSet m → E.IR x' → E.Y x p ≤ E.Y x' p'

lemma sum_dot_le {x : N → K → ℝ} (hx : E.Feasible x) {p : K → ℝ} (hp : 0 ≤ p) :
    ∑ i, dot p (x i) ≤ dot p E.W := by
  simp only [dot]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun k _ => by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hx.2 k) (hp k)

lemma sum_dot_ω (p : K → ℝ) : ∑ i, dot p (E.ω i) = dot p E.W := by
  simp only [dot, W]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]

/-! ### Lemma 3 -/

/-- Lemma 3(a), first part. -/
theorem Y_nonneg {x : N → K → ℝ} {p : K → ℝ} (hx : E.Feasible x) (hp : p ∈ E.Prices) :
    0 ≤ E.Y x p := by
  have h1 : ∑ i, mu (E.pref i) p (x i) ≤ ∑ i, dot p (x i) :=
    Finset.sum_le_sum fun i _ => mu_le_dot hp.1 (hx.1 i)
  have h2 := E.sum_dot_le hx hp.1
  have h3 : dot p E.W = 1 := hp.2
  simp only [Y]
  linarith

/-- Lemma 3(a), second part. -/
theorem Y_eq_zero_iff {x : N → K → ℝ} {p : K → ℝ} (hx : E.Feasible x) (hp : p ∈ E.Prices) :
    E.Y x p = 0 ↔ (∀ i, mu (E.pref i) p (x i) = dot p (x i)) ∧ ∑ i, dot p (x i) = 1 := by
  have hle : ∀ i, mu (E.pref i) p (x i) ≤ dot p (x i) := fun i => mu_le_dot hp.1 (hx.1 i)
  have h1 : ∑ i, mu (E.pref i) p (x i) ≤ ∑ i, dot p (x i) := Finset.sum_le_sum fun i _ => hle i
  have h2 := E.sum_dot_le hx hp.1
  have h3 : dot p E.W = 1 := hp.2
  simp only [Y]
  constructor
  · intro h
    have hs : ∑ i, dot p (x i) = 1 := by linarith
    refine ⟨fun i => ?_, hs⟩
    have hz : ∑ i, (dot p (x i) - mu (E.pref i) p (x i)) = 0 := by
      rw [Finset.sum_sub_distrib]
      linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sub_nonneg.2 (hle i)).1 hz i
      (mem_univ i)
    linarith
  · rintro ⟨h, hs⟩
    rw [Finset.sum_congr rfl fun i _ => h i, hs]
    ring

/-- Lemma 3(b): every root is a Yquilibrium. -/
theorem root_isYq {x : N → K → ℝ} {p : K → ℝ} (h : E.IsRoot x p) : E.IsYq x p :=
  ⟨h.1, h.2.1, fun x' p' hx' hp' => by rw [h.2.2]; exact E.Y_nonneg hx' hp'⟩

/-- Lemma 3(b): every root has a strictly positive price and a Pareto-optimal allocation. -/
theorem root_pos_pareto [Nonempty N] [Nonempty K] {x : N → K → ℝ} {p : K → ℝ}
    (h : E.IsRoot x p) : (∀ k, 0 < p k) ∧ E.ParetoOptimal x :=
  E.theorem1.2.2.1 x p (E.root_isYq h)

/-- In a Walrasian equilibrium for `m`, bundles are worth exactly the incomes. -/
theorem walrasianFor_income {m : N → ℝ} {x : N → K → ℝ} {p : K → ℝ}
    (h : E.IsWalrasianFor m x p) (i : N) : dot p (x i) = m i :=
  (optimal_mu h.2.1.1 (h.2.2 i)).2

/-- Lemma 3(d): roots are exactly the Walrasian equilibria for some income distribution,
  namely `mᵢ = ⟨p|xᵢ⟩`. -/
theorem root_iff [Nonempty N] [Nonempty K] {x : N → K → ℝ} {p : K → ℝ} :
    E.IsRoot x p ↔ ∃ m, Incomes m ∧ E.IsWalrasianFor m x p := by
  constructor
  · intro h
    obtain ⟨hx, hp, hY⟩ := h
    have hpos := (E.root_pos_pareto ⟨hx, hp, hY⟩).1
    obtain ⟨hmu, hs⟩ := (E.Y_eq_zero_iff hx hp).1 hY
    exact ⟨fun i => dot p (x i), ⟨fun i => dot_nonneg hp.1 (hx.1 i), hs⟩, hx, hp,
      fun i => optimal_of_mu hpos (hx.1 i) (hmu i)⟩
  · rintro ⟨m, hm, hx, hp, hopt⟩
    refine ⟨hx, hp, (E.Y_eq_zero_iff hx hp).2 ⟨fun i => (optimal_mu hp.1 (hopt i)).1, ?_⟩⟩
    rw [Finset.sum_congr rfl fun i _ => (optimal_mu hp.1 (hopt i)).2]
    exact hm.2

/-! ### Theorem 2 -/

lemma continuous_dot_pair (i : N) :
    Continuous fun q : (N → K → ℝ) × (K → ℝ) => dot q.2 (q.1 i) := by
  unfold dot
  exact continuous_finsetSum _ fun k _ => ((continuous_apply k).comp continuous_snd).mul
    ((continuous_apply k).comp ((continuous_apply i).comp continuous_fst))

lemma isCompact_CSet [Nonempty N] (m : N → ℝ) : IsCompact (E.CSet m) := by
  have hcl : IsClosed {q : (N → K → ℝ) × (K → ℝ) | ∀ i, dot q.2 (q.1 i) = m i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_eq (continuous_dot_pair i) continuous_const
  have heq : E.CSet m = ({x | E.Feasible x} ×ˢ E.Prices) ∩
      {q : (N → K → ℝ) × (K → ℝ) | ∀ i, dot q.2 (q.1 i) = m i} := by
    ext q
    simp only [CSet, mem_setOf_eq, mem_inter_iff, mem_prod]
    tauto
  refine (E.isCompact_feasible.prod E.isCompact_prices).of_isClosed_subset ?_
    fun q hq => ⟨hq.1, hq.2.1⟩
  rw [heq]
  exact (E.isClosed_feasible.prod E.isCompact_prices.isClosed).inter hcl

lemma CSet_nonempty [Nonempty N] [Nonempty K] {m : N → ℝ} (hm : Incomes m) :
    (E.CSet m).Nonempty := by
  refine ⟨(fun i => m i • E.W, E.p0), ⟨fun i k => ?_, fun k => ?_⟩, E.p0_mem, fun i => ?_⟩
  · show 0 ≤ m i * E.W k
    exact mul_nonneg (hm.1 i) (E.W_nonneg k)
  · show ∑ i, m i * E.W k ≤ E.W k
    rw [← Finset.sum_mul, hm.2, one_mul]
  · show dot E.p0 (m i • E.W) = m i
    rw [dot_smul_right, E.p0_mem.2, mul_one]

/-- Minimizers of the potential on a compact set of feasible pairs exist. -/
theorem exists_min_on (D : Set ((N → K → ℝ) × (K → ℝ))) (hD : IsCompact D) (hne : D.Nonempty)
    (hDF : ∀ q ∈ D, E.Feasible q.1 ∧ q.2 ∈ E.Prices) :
    ∃ q ∈ D, ∀ q' ∈ D, E.Y q.1 q.2 ≤ E.Y q'.1 q'.2 := by
  have husc : UpperSemicontinuousOn
      (fun q : (N → K → ℝ) × (K → ℝ) => ∑ i, mu (E.pref i) q.2 (q.1 i)) D := by
    intro q hq
    exact upperSemicontinuousWithinAt_sum fun i _ =>
      mu_usc (P := E.pref i) (s := D) continuous_snd ((continuous_apply i).comp continuous_fst)
        (fun a ha => (hDF a ha).2.1) (fun a ha => (hDF a ha).1.1 i) q hq
  obtain ⟨q, hq, hmax⟩ := husc.exists_isMaxOn hne hD
  rw [isMaxOn_iff] at hmax
  refine ⟨q, hq, fun q' hq' => ?_⟩
  have := hmax q' hq'
  simp only [Y]
  linarith

/-- **Theorem 2**, existence: for every income distribution `m`, `𝒴(m)` is non-empty. -/
theorem theorem2_exists [Nonempty N] [Nonempty K] {m : N → ℝ} (hm : Incomes m) :
    ∃ x p, E.IsYqFor m x p := by
  obtain ⟨⟨x, p⟩, hq, hmin⟩ := E.exists_min_on (E.CSet m) (E.isCompact_CSet m)
    (E.CSet_nonempty hm) fun q hq => ⟨hq.1, hq.2.1⟩
  exact ⟨x, p, hq, fun x' p' h => hmin (x', p') h⟩

/-- **Theorem 2(a)**: if the potential has a root at `m`, then `𝒴(m)` is the set of roots
  at `m`. -/
theorem theorem2_a {m : N → ℝ} (hroot : ∃ x₀ p₀, (x₀, p₀) ∈ E.CSet m ∧ E.Y x₀ p₀ = 0)
    (x : N → K → ℝ) (p : K → ℝ) :
    E.IsYqFor m x p ↔ (x, p) ∈ E.CSet m ∧ E.Y x p = 0 := by
  obtain ⟨x₀, p₀, h₀, hY₀⟩ := hroot
  constructor
  · rintro ⟨hC, hmin⟩
    have h1 := hmin x₀ p₀ h₀
    have h2 := E.Y_nonneg hC.1 hC.2.1
    exact ⟨hC, by linarith⟩
  · rintro ⟨hC, hY⟩
    exact ⟨hC, fun x' p' h => by rw [hY]; exact E.Y_nonneg h.1 h.2.1⟩

/-- **Theorem 2(b)**: a Walrasian equilibrium is a root, its income distribution
  `mᵂᵢ = ⟨p|ωᵢ⟩` lies in `Σ_N`, and it belongs to `𝒴⁺(mᵂ)` and to `𝒴⁺`
  (so `mᵂ ∈ Σ_N⁺`). -/
theorem theorem2_b {x : N → K → ℝ} {p : K → ℝ} (h : E.IsWalrasian x p) :
    Incomes (fun i => dot p (E.ω i)) ∧ E.IsRoot x p ∧
      E.IsYqIRFor (fun i => dot p (E.ω i)) x p ∧ E.IsYqIR x p := by
  obtain ⟨hx, hp, hopt⟩ := h
  have hinc : Incomes (fun i => dot p (E.ω i)) :=
    ⟨fun i => dot_nonneg hp.1 (E.ω_nonneg i), by rw [E.sum_dot_ω]; exact hp.2⟩
  have hroot : E.IsRoot x p := by
    refine ⟨hx, hp, (E.Y_eq_zero_iff hx hp).2 ⟨fun i => (optimal_mu hp.1 (hopt i)).1, ?_⟩⟩
    rw [Finset.sum_congr rfl fun i _ => (optimal_mu hp.1 (hopt i)).2]
    exact hinc.2
  have hIR : E.IR x := fun i => (hopt i).2.2 (E.ω i) (E.ω_nonneg i) le_rfl
  refine ⟨hinc, hroot, ⟨⟨hx, hp, fun i => E.walrasianFor_income ⟨hx, hp, hopt⟩ i⟩, hIR,
    fun x' p' h' _ => by rw [hroot.2.2]; exact E.Y_nonneg h'.1 h'.2.1⟩,
    hx, hIR, hp, fun x' p' hx' _ hp' => by rw [hroot.2.2]; exact E.Y_nonneg hx' hp'⟩

/-! ### Corollary 1(a) -/

/-- **Corollary 1(a)** (first welfare theorem): every root, and in particular every Walrasian
  equilibrium, is Pareto optimal. -/
theorem corollary1_a [Nonempty N] [Nonempty K] :
    (∀ x p, E.IsRoot x p → E.ParetoOptimal x) ∧
    (∀ x p, E.IsWalrasian x p → E.ParetoOptimal x) :=
  ⟨fun _ _ h => (E.root_pos_pareto h).2, fun _ _ h => (E.root_pos_pareto (E.theorem2_b h).2.1).2⟩

end Economy

end Yq
