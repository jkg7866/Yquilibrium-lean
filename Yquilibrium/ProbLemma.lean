/-
  A general probability lemma behind Step 2 of the proof of Theorem 4, from Lévy's extension of
  the Borel–Cantelli lemma: if a bounded non-decreasing process jumps by at least ε with
  conditional probability at least η whenever the state is in A, then the state is in A only
  finitely often, almost surely.
-/
import Mathlib.Probability.Martingale.BorelCantelli

open Filter MeasureTheory Set
open scoped ENNReal ProbabilityTheory Topology

namespace Yq

/-- Infinitely many jumps of size `ε` are impossible for a bounded non-decreasing sequence. -/
lemma not_frequently_jump {S : ℕ → ℝ} (hmono : Monotone S) (hbdd : BddAbove (range S))
    {ε : ℝ} (hε : 0 < ε) {G : ℕ → Prop} (hjump : ∀ t, G t → S t + ε ≤ S (t + 1)) :
    ¬ ∃ᶠ t in atTop, G t := by
  intro hfr
  obtain ⟨φ, hφ, hG⟩ := extraction_of_frequently_atTop hfr
  obtain ⟨M, hM⟩ := hbdd
  have key : ∀ m : ℕ, S (φ 0) + (m + 1) * ε ≤ S (φ m + 1) := by
    intro m
    induction m with
    | zero => simpa using hjump _ (hG 0)
    | succ m ih =>
      have h1 := hjump _ (hG (m + 1))
      have h2 : S (φ m + 1) ≤ S (φ (m + 1)) := hmono (hφ (Nat.lt_succ_self m))
      push_cast
      linarith
  obtain ⟨m, hm⟩ := exists_nat_gt ((M - S (φ 0)) / ε)
  have h1 := key m
  have h2 : S (φ m + 1) ≤ M := hM ⟨_, rfl⟩
  rw [div_lt_iff₀ hε] at hm
  nlinarith

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}

/-- **Progress lemma.** Let `S` be non-decreasing and bounded along every path. Suppose that,
  given `ℱ t`, the event `G t` (measurable at `t + 1`) has conditional probability at least
  `η` on `A t` (measurable at `t`), and `G t` raises `S` by at least `ε`. Then almost surely
  `A t` occurs only finitely often. -/
theorem finitely_often_of_progress (S : ℕ → Ω → ℝ) (A G : ℕ → Set Ω)
    (hA : ∀ t, MeasurableSet[ℱ t] (A t)) (hG : ∀ t, MeasurableSet[ℱ (t + 1)] (G t))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hpath : ∀ᵐ ω ∂μ, (Monotone fun t => S t ω) ∧ BddAbove (range fun t => S t ω) ∧
      ∀ t, ω ∈ G t → S t ω + ε ≤ S (t + 1) ω)
    (hcond : ∀ t, ∀ᵐ ω ∂μ,
      η * (A t).indicator (1 : Ω → ℝ) ω ≤ μ[(G t).indicator (1 : Ω → ℝ) | ℱ t] ω) :
    ∀ᵐ ω ∂μ, ∀ᶠ t in atTop, ω ∉ A t := by
  classical
  set s : ℕ → Set Ω := fun n => Nat.casesOn n ∅ G with hsdef
  have hs : ∀ n, MeasurableSet[ℱ n] (s n) := by
    intro n
    cases n with
    | zero => exact @MeasurableSet.empty _ (ℱ 0)
    | succ k => exact hG k
  have hlevy := ae_mem_limsup_atTop_iff μ hs
  have hc := ae_all_iff.2 hcond
  have hnn : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ μ[(G t).indicator (1 : Ω → ℝ) | ℱ t] ω :=
    ae_all_iff.2 fun t => condExp_nonneg
      (Eventually.of_forall fun ω => indicator_nonneg (fun _ _ => zero_le_one) ω)
  filter_upwards [hlevy, hc, hnn, hpath] with ω hlev hc hnn hpω
  obtain ⟨hmono, hbdd, hjump⟩ := hpω
  by_contra hfr
  rw [not_eventually] at hfr
  simp only [not_not] at hfr
  -- the conditional probabilities sum to infinity
  have hdiv : Tendsto (fun n => ∑ k ∈ Finset.range n,
      μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k] ω) atTop atTop := by
    show Tendsto (fun n => ∑ k ∈ Finset.range n,
      μ[(G k).indicator (1 : Ω → ℝ) | ℱ k] ω) atTop atTop
    apply tendsto_atTop_atTop_of_monotone
    · intro a b hab
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) fun k _ _ => hnn k
    · intro M
      obtain ⟨φ, hφ, hAφ⟩ := extraction_of_frequently_atTop hfr
      obtain ⟨m, hm⟩ := exists_nat_ge (M / η)
      refine ⟨φ m + 1, ?_⟩
      have hsub : (Finset.range (m + 1)).image φ ⊆ Finset.range (φ m + 1) := by
        intro k hk
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hk
        exact Finset.mem_range.2 (Nat.lt_succ_of_le (hφ.monotone
          (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))))
      calc M ≤ η * (m + 1) := by
            rw [div_le_iff₀ hη] at hm
            nlinarith
        _ = ∑ i ∈ Finset.range (m + 1), η * (A (φ i)).indicator (1 : Ω → ℝ) ω := by
            rw [Finset.sum_congr rfl fun i _ => by rw [indicator_of_mem (hAφ i), Pi.one_apply,
              mul_one]]
            simp [mul_comm]
        _ = ∑ k ∈ (Finset.range (m + 1)).image φ, η * (A k).indicator (1 : Ω → ℝ) ω :=
            (Finset.sum_image (f := fun k => η * (A k).indicator (1 : Ω → ℝ) ω)
              fun a _ b _ h => hφ.injective h).symm
        _ ≤ ∑ k ∈ Finset.range (φ m + 1), η * (A k).indicator (1 : Ω → ℝ) ω :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
              mul_nonneg hη.le (indicator_nonneg (fun _ _ => zero_le_one) ω)
        _ ≤ ∑ k ∈ Finset.range (φ m + 1), μ[(G k).indicator (1 : Ω → ℝ) | ℱ k] ω :=
            Finset.sum_le_sum fun k _ => hc k
  -- hence G occurs infinitely often, which a bounded non-decreasing S cannot afford
  have hmem := hlev.2 hdiv
  rw [mem_limsup_iff_frequently_mem] at hmem
  apply not_frequently_jump hmono hbdd hε (G := fun t => ω ∈ G t)
    fun t h => hjump t h
  rw [frequently_atTop] at hmem ⊢
  intro a
  obtain ⟨b, hb, hbs⟩ := hmem (a + 1)
  cases b with
  | zero => omega
  | succ k => exact ⟨k, by omega, hbs⟩

end Yq
