/-
  Two-good CES utilities with ρ > 1 (non-convex preferences), used for Proposition 1.
  u(z) = ((a z₀)^ρ + ((1-a) z₁)^ρ)^(1/ρ).
-/
import Yquilibrium.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Finset Filter Topology Set

noncomputable section

namespace Yq

/-- A continuous utility that is strictly increasing on `ℝᴷ₊` induces a preference. -/
def prefOf {K : Type*} [Fintype K] [Nonempty K] (U : (K → ℝ) → ℝ) (hc : Continuous U)
    (hm : ∀ x y, 0 ≤ x → x ≤ y → x ≠ y → U x < U y) : Pref K where
  R z x := U x ≤ U z
  total x y _ _ := le_total (U y) (U x)
  trans x y z _ _ _ h1 h2 := h2.trans h1
  upper_closed x _ := (isClosed_le continuous_const continuous_id).inter
    (isClosed_le continuous_const hc)
  lower_closed x _ := (isClosed_le continuous_const continuous_id).inter
    (isClosed_le hc continuous_const)
  mono x y hx hxy := not_le.2 (hm x y hx (fun k => (hxy k).le) fun h => by
    have := hxy (Classical.arbitrary K)
    rw [h] at this
    exact lt_irrefl _ this)
  mono' x y hx _ hxy hne := not_le.2 (hm x y hx hxy hne)

/-- Two-good CES utility. -/
def ces (a ρ : ℝ) (z : Fin 2 → ℝ) : ℝ := ((a * z 0) ^ ρ + ((1 - a) * z 1) ^ ρ) ^ ρ⁻¹

lemma dot_two (p z : Fin 2 → ℝ) : dot p z = p 0 * z 0 + p 1 * z 1 := by
  simp [dot, Fin.sum_univ_two]

section CES

variable {a ρ : ℝ}

/-- Strict superadditivity of `s ↦ s^ρ` for `ρ > 1`. -/
lemma rpow_add_lt {s t : ℝ} (hρ : 1 < ρ) (hs : 0 < s) (ht : 0 < t) :
    s ^ ρ + t ^ ρ < (s + t) ^ ρ := by
  have hsplit : ∀ w : ℝ, 0 < w → w ^ ρ = w * w ^ (ρ - 1) := fun w hw => by
    conv_lhs => rw [show ρ = 1 + (ρ - 1) by ring]
    rw [Real.rpow_add hw, Real.rpow_one]
  rw [hsplit s hs, hsplit t ht, hsplit (s + t) (by linarith)]
  have h1 : s ^ (ρ - 1) < (s + t) ^ (ρ - 1) := Real.rpow_lt_rpow hs.le (by linarith) (by linarith)
  have h2 : t ^ (ρ - 1) < (s + t) ^ (ρ - 1) := Real.rpow_lt_rpow ht.le (by linarith) (by linarith)
  have h3 := mul_lt_mul_of_pos_left h1 hs
  have h4 := mul_lt_mul_of_pos_left h2 ht
  nlinarith

lemma rpow_add_le {s t : ℝ} (hρ : 1 < ρ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s ^ ρ + t ^ ρ ≤ (s + t) ^ ρ := by
  have hρ0 : ρ ≠ 0 := by linarith
  rcases hs.lt_or_eq with hs' | hs'
  · rcases ht.lt_or_eq with ht' | ht'
    · exact (rpow_add_lt hρ hs' ht').le
    · rw [← ht', Real.zero_rpow hρ0, add_zero, add_zero]
  · rw [← hs', Real.zero_rpow hρ0, zero_add, zero_add]

lemma ces_le_lin (ha0 : 0 < a) (ha1 : a < 1) (hρ : 1 < ρ) {z : Fin 2 → ℝ} (hz : 0 ≤ z) :
    ces a ρ z ≤ a * z 0 + (1 - a) * z 1 := by
  have hs : 0 ≤ a * z 0 := mul_nonneg ha0.le (hz 0)
  have ht : 0 ≤ (1 - a) * z 1 := mul_nonneg (by linarith) (hz 1)
  have hρ0 : 0 < ρ := by linarith
  calc ces a ρ z ≤ ((a * z 0 + (1 - a) * z 1) ^ ρ) ^ ρ⁻¹ :=
        Real.rpow_le_rpow (by positivity) (rpow_add_le hρ hs ht) (inv_nonneg.2 hρ0.le)
    _ = a * z 0 + (1 - a) * z 1 := Real.rpow_rpow_inv (by positivity) hρ0.ne'

lemma ces_lt_lin (ha0 : 0 < a) (ha1 : a < 1) (hρ : 1 < ρ) {z : Fin 2 → ℝ} (h0 : 0 < z 0)
    (h1 : 0 < z 1) : ces a ρ z < a * z 0 + (1 - a) * z 1 := by
  have hs : 0 < a * z 0 := mul_pos ha0 h0
  have ht : 0 < (1 - a) * z 1 := mul_pos (by linarith) h1
  have hρ0 : 0 < ρ := by linarith
  calc ces a ρ z < ((a * z 0 + (1 - a) * z 1) ^ ρ) ^ ρ⁻¹ :=
        Real.rpow_lt_rpow (by positivity) (rpow_add_lt hρ hs ht) (inv_pos.2 hρ0)
    _ = a * z 0 + (1 - a) * z 1 := Real.rpow_rpow_inv (by positivity) hρ0.ne'

lemma ces_x (ha0 : 0 < a) (hρ : 1 < ρ) {z : Fin 2 → ℝ} (h0 : 0 ≤ z 0) (h1 : z 1 = 0) :
    ces a ρ z = a * z 0 := by
  have hρ0 : 0 < ρ := by linarith
  simp only [ces, h1, mul_zero, Real.zero_rpow hρ0.ne', add_zero]
  exact Real.rpow_rpow_inv (mul_nonneg ha0.le h0) hρ0.ne'

lemma ces_y (ha1 : a < 1) (hρ : 1 < ρ) {z : Fin 2 → ℝ} (h0 : z 0 = 0) (h1 : 0 ≤ z 1) :
    ces a ρ z = (1 - a) * z 1 := by
  have hρ0 : 0 < ρ := by linarith
  simp only [ces, h0, mul_zero, Real.zero_rpow hρ0.ne', zero_add]
  exact Real.rpow_rpow_inv (mul_nonneg (by linarith) h1) hρ0.ne'

lemma ces_continuous (hρ : 1 < ρ) : Continuous (ces a ρ) := by
  have hρ0 : 0 < ρ := by linarith
  unfold ces
  refine Continuous.rpow_const ?_ fun _ => Or.inr (inv_nonneg.2 hρ0.le)
  exact (((continuous_const.mul (continuous_apply 0)).rpow_const fun _ => Or.inr hρ0.le).add
    ((continuous_const.mul (continuous_apply 1)).rpow_const fun _ => Or.inr hρ0.le))

lemma ces_strictMono (ha0 : 0 < a) (ha1 : a < 1) (hρ : 1 < ρ) (x y : Fin 2 → ℝ) (hx : 0 ≤ x)
    (hxy : x ≤ y) (hne : x ≠ y) : ces a ρ x < ces a ρ y := by
  have hρ0 : 0 < ρ := by linarith
  have hb : 0 < 1 - a := by linarith
  have hs : a * x 0 ≤ a * y 0 := mul_le_mul_of_nonneg_left (hxy 0) ha0.le
  have ht : (1 - a) * x 1 ≤ (1 - a) * y 1 := mul_le_mul_of_nonneg_left (hxy 1) hb.le
  have hs0 : 0 ≤ a * x 0 := mul_nonneg ha0.le (hx 0)
  have ht0 : 0 ≤ (1 - a) * x 1 := mul_nonneg hb.le (hx 1)
  have hsum : (a * x 0) ^ ρ + ((1 - a) * x 1) ^ ρ < (a * y 0) ^ ρ + ((1 - a) * y 1) ^ ρ := by
    have h0 := Real.rpow_le_rpow hs0 hs hρ0.le
    have h1 := Real.rpow_le_rpow ht0 ht hρ0.le
    by_cases hk : x 0 = y 0
    · have hk1 : x 1 < y 1 := by
        refine lt_of_le_of_ne (hxy 1) fun h => hne ?_
        funext k
        fin_cases k
        · exact hk
        · exact h
      have := Real.rpow_lt_rpow ht0 (mul_lt_mul_of_pos_left hk1 hb) hρ0
      linarith
    · have hk0 : x 0 < y 0 := lt_of_le_of_ne (hxy 0) hk
      have := Real.rpow_lt_rpow hs0 (mul_lt_mul_of_pos_left hk0 ha0) hρ0
      linarith
  exact Real.rpow_lt_rpow (by positivity) hsum (inv_pos.2 hρ0)

/-- The preference induced by a two-good CES utility. -/
def cesPref (a ρ : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hρ : 1 < ρ) : Pref (Fin 2) :=
  prefOf (ces a ρ) (ces_continuous hρ) (ces_strictMono ha0 ha1 hρ)

/-- Optimal bundles for CES with `ρ > 1`: a single good, the one with the higher
  `aₖ / pₖ`, bought with the whole income. -/
theorem ces_optimal_iff (ha0 : 0 < a) (ha1 : a < 1) (hρ : 1 < ρ) {p : Fin 2 → ℝ}
    (hp : ∀ k, 0 < p k) {m : ℝ} (hm : 0 ≤ m) {z : Fin 2 → ℝ} :
    Optimal (cesPref a ρ ha0 ha1 hρ) p m z ↔
      0 ≤ z ∧ dot p z = m ∧ (z 0 = 0 ∨ z 1 = 0) ∧
        (0 < z 0 → (1 - a) * p 0 ≤ a * p 1) ∧ (0 < z 1 → a * p 1 ≤ (1 - a) * p 0) := by
  have hb : 0 < 1 - a := by linarith
  have hp0 := hp 0
  have hp1 := hp 1
  set M := max (a / p 0) ((1 - a) / p 1) with hMdef
  have hM0 : a ≤ M * p 0 := by
    have := le_max_left (a / p 0) ((1 - a) / p 1)
    rw [← hMdef, div_le_iff₀ hp0] at this
    exact this
  have hM1 : 1 - a ≤ M * p 1 := by
    have := le_max_right (a / p 0) ((1 - a) / p 1)
    rw [← hMdef, div_le_iff₀ hp1] at this
    exact this
  have hMpos : 0 < M := lt_of_lt_of_le (div_pos ha0 hp0) (le_max_left _ _)
  -- the value bound: u(w) ≤ M ⟨p|w⟩
  have hbound : ∀ w : Fin 2 → ℝ, 0 ≤ w → ces a ρ w ≤ M * dot p w := by
    intro w hw
    rw [dot_two]
    have := ces_le_lin ha0 ha1 hρ hw
    have h0 := mul_le_mul_of_nonneg_right hM0 (hw 0)
    have h1 := mul_le_mul_of_nonneg_right hM1 (hw 1)
    nlinarith
  -- the best single-good bundle attains M m
  have hbest : ∃ w : Fin 2 → ℝ, 0 ≤ w ∧ dot p w ≤ m ∧ ces a ρ w = M * m := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rcases le_total ((1 - a) / p 1) (a / p 0) with h | h
    · refine ⟨fun k => if k = 0 then m / p 0 else 0, fun k => ?_, ?_, ?_⟩
      · show (0 : ℝ) ≤ if k = 0 then m / p 0 else 0
        split_ifs
        · exact div_nonneg hm hp0.le
        · exact le_rfl
      · rw [dot_two, if_pos rfl, if_neg h10]
        have h' : p 0 * (m / p 0) = m := by field_simp
        linarith
      · rw [ces_x ha0 hρ (by rw [if_pos rfl]; exact div_nonneg hm hp0.le) (by rw [if_neg h10]),
          if_pos rfl, hMdef, max_eq_left h]
        field_simp
    · refine ⟨fun k => if k = 0 then 0 else m / p 1, fun k => ?_, ?_, ?_⟩
      · show (0 : ℝ) ≤ if k = 0 then 0 else m / p 1
        split_ifs
        · exact le_rfl
        · exact div_nonneg hm hp1.le
      · rw [dot_two, if_pos rfl, if_neg h10]
        have h' : p 1 * (m / p 1) = m := by field_simp
        linarith
      · rw [ces_y ha1 hρ (by rw [if_pos rfl]) (by rw [if_neg h10]; exact div_nonneg hm hp1.le),
          if_neg h10, hMdef, max_eq_right h]
        field_simp
  obtain ⟨w, hw0, hwm, hwv⟩ := hbest
  constructor
  · rintro ⟨hz, hzm, hopt⟩
    have hge : M * m ≤ ces a ρ z := hwv ▸ hopt w hw0 hwm
    have hle := hbound z hz
    have hdot : dot p z = m := by
      refine le_antisymm hzm ?_
      by_contra h
      push_neg at h
      have := mul_lt_mul_of_pos_left h hMpos
      linarith
    have hlin := ces_le_lin ha0 ha1 hρ hz
    rw [dot_two] at hle hdot
    have hz0 : 0 ≤ z 0 := hz 0
    have hz1 : 0 ≤ z 1 := hz 1
    have hsingle : z 0 = 0 ∨ z 1 = 0 := by
      by_contra h
      push_neg at h
      have := ces_lt_lin ha0 ha1 hρ (lt_of_le_of_ne hz0 (Ne.symm h.1))
        (lt_of_le_of_ne hz1 (Ne.symm h.2))
      have h0 := mul_le_mul_of_nonneg_right hM0 hz0
      have h1 := mul_le_mul_of_nonneg_right hM1 hz1
      nlinarith
    -- tightness of a z₀ + (1−a) z₁ ≤ M ⟨p|z⟩
    have htight : (M * p 0 - a) * z 0 + (M * p 1 - (1 - a)) * z 1 = 0 := by
      have h0 := mul_le_mul_of_nonneg_right hM0 hz0
      have h1 := mul_le_mul_of_nonneg_right hM1 hz1
      nlinarith
    have hA : 0 ≤ (M * p 0 - a) * z 0 := mul_nonneg (by linarith) hz0
    have hB : 0 ≤ (M * p 1 - (1 - a)) * z 1 := mul_nonneg (by linarith) hz1
    refine ⟨hz, by rw [dot_two]; exact hdot, hsingle, fun hpos => ?_, fun hpos => ?_⟩
    · have : (M * p 0 - a) * z 0 = 0 := by linarith
      have hMa : M * p 0 = a := by
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · linarith
      -- (1−a)/p₁ ≤ M = a/p₀
      have h1 : (1 - a) * p 0 ≤ M * p 1 * p 0 := mul_le_mul_of_nonneg_right hM1 hp0.le
      nlinarith
    · have : (M * p 1 - (1 - a)) * z 1 = 0 := by linarith
      have hMa : M * p 1 = 1 - a := by
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · linarith
      have h1 : a * p 1 ≤ M * p 0 * p 1 := mul_le_mul_of_nonneg_right hM0 hp1.le
      nlinarith
  · rintro ⟨hz, hzm, hsingle, hx, hy⟩
    refine ⟨hz, hzm.le, fun v hv hvm => ?_⟩
    show ces a ρ v ≤ ces a ρ z
    have hval : ces a ρ z = M * m := by
      rcases hsingle with h0 | h1
      · have hm' : m = p 1 * z 1 := by rw [← hzm, dot_two, h0]; ring
        rw [ces_y ha1 hρ h0 (hz 1), hm']
        rcases (hz 1).lt_or_eq with hpos | hzero
        · have hMeq : M = (1 - a) / p 1 := by
            rw [hMdef]
            apply max_eq_right
            rw [div_le_div_iff₀ hp0 hp1]
            linarith [hy hpos]
          rw [hMeq]
          field_simp
        · rw [← hzero]
          simp
      · have hm' : m = p 0 * z 0 := by rw [← hzm, dot_two, h1]; ring
        rw [ces_x ha0 hρ (hz 0) h1, hm']
        rcases (hz 0).lt_or_eq with hpos | hzero
        · have hMeq : M = a / p 0 := by
            rw [hMdef]
            apply max_eq_left
            rw [div_le_div_iff₀ hp1 hp0]
            linarith [hx hpos]
          rw [hMeq]
          field_simp
        · rw [← hzero]
          simp
    rw [hval]
    exact (hbound v hv).trans (mul_le_mul_of_nonneg_left hvm hMpos.le)

end CES

/-! ### Numeric bounds -/

lemma rpow_five_halves_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ ((5 : ℝ) / 2)) ^ 2 = x ^ 5 := by
  rw [← Real.rpow_natCast (x ^ ((5 : ℝ) / 2)), ← Real.rpow_mul hx]
  norm_num

lemma rpow_five_halves_ge {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (h : c ^ 2 ≤ x ^ 5) :
    c ≤ x ^ ((5 : ℝ) / 2) := by
  apply le_of_pow_le_pow_left₀ two_ne_zero (Real.rpow_nonneg hx _)
  rw [rpow_five_halves_sq hx]
  exact h

lemma rpow_five_halves_le {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x ^ 5 ≤ c ^ 2) :
    x ^ ((5 : ℝ) / 2) ≤ c := by
  apply le_of_pow_le_pow_left₀ two_ne_zero hc
  rw [rpow_five_halves_sq hx]
  exact h

/-- `c ≤ ces a (5/2) z` from `c^(5/2) ≤ (a z₀)^(5/2) + ((1−a) z₁)^(5/2)`. -/
lemma ces_ge_of {a c : ℝ} {z : Fin 2 → ℝ} (hc : 0 ≤ c)
    (h : c ^ ((5 : ℝ) / 2) ≤ (a * z 0) ^ ((5 : ℝ) / 2) + ((1 - a) * z 1) ^ ((5 : ℝ) / 2)) :
    c ≤ ces a (5 / 2) z := by
  have h' := Real.rpow_le_rpow (Real.rpow_nonneg hc _) h (by norm_num : (0 : ℝ) ≤ (5 / 2)⁻¹)
  rwa [Real.rpow_rpow_inv hc (by norm_num)] at h'

lemma ces_le_of {a c : ℝ} {z : Fin 2 → ℝ} (hc : 0 ≤ c) (hs : 0 ≤ a * z 0)
    (ht : 0 ≤ (1 - a) * z 1)
    (h : (a * z 0) ^ ((5 : ℝ) / 2) + ((1 - a) * z 1) ^ ((5 : ℝ) / 2) ≤ c ^ ((5 : ℝ) / 2)) :
    ces a (5 / 2) z ≤ c := by
  have h' := Real.rpow_le_rpow (by positivity) h (by norm_num : (0 : ℝ) ≤ (5 / 2)⁻¹)
  rwa [Real.rpow_rpow_inv hc (by norm_num)] at h'

/-- Buyer's endowment utility: `21 ≤ u_B(25,45) ≤ 33`. -/
lemma uB_bounds : 21 ≤ ces (3 / 5) (5 / 2) ![25, 45] ∧ ces (3 / 5) (5 / 2) ![25, 45] ≤ 33 := by
  constructor
  · apply ces_ge_of (by norm_num)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have h1 : (2021 : ℝ) ≥ (21 : ℝ) ^ ((5 : ℝ) / 2) :=
      rpow_five_halves_le (by norm_num) (by norm_num) (by norm_num)
    have h2 : (871 : ℝ) ≤ (3 / 5 * 25 : ℝ) ^ ((5 : ℝ) / 2) :=
      rpow_five_halves_ge (by norm_num) (by norm_num) (by norm_num)
    have h3 : (1374 : ℝ) ≤ ((1 - 3 / 5) * 45 : ℝ) ^ ((5 : ℝ) / 2) :=
      rpow_five_halves_ge (by norm_num) (by norm_num) (by norm_num)
    linarith
  · have := ces_le_lin (a := 3 / 5) (ρ := 5 / 2) (by norm_num) (by norm_num) (by norm_num)
      (z := ![25, 45]) (fun k => by fin_cases k <;> simp)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at this
    linarith

/-- Seller's endowment utility: `42 ≤ u_S(75,55) ≤ 55`. -/
lemma uS_bounds : 42 ≤ ces (9 / 20) (5 / 2) ![75, 55] ∧ ces (9 / 20) (5 / 2) ![75, 55] ≤ 55 := by
  constructor
  · apply ces_ge_of (by norm_num)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have h1 : (11433 : ℝ) ≥ (42 : ℝ) ^ ((5 : ℝ) / 2) :=
      rpow_five_halves_le (by norm_num) (by norm_num) (by norm_num)
    have h2 : (6617 : ℝ) ≤ (9 / 20 * 75 : ℝ) ^ ((5 : ℝ) / 2) :=
      rpow_five_halves_ge (by norm_num) (by norm_num) (by norm_num)
    have h3 : (5032 : ℝ) ≤ ((1 - 9 / 20) * 55 : ℝ) ^ ((5 : ℝ) / 2) :=
      rpow_five_halves_ge (by norm_num) (by norm_num) (by norm_num)
    linarith
  · apply ces_le_of (by norm_num) (by norm_num) (by norm_num)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have h1 : (22000 : ℝ) ≤ (55 : ℝ) ^ ((5 : ℝ) / 2) :=
      rpow_five_halves_ge (by norm_num) (by norm_num) (by norm_num)
    have h2 : (9 / 20 * 75 : ℝ) ^ ((5 : ℝ) / 2) ≤ 6618 :=
      rpow_five_halves_le (by norm_num) (by norm_num) (by norm_num)
    have h3 : ((1 - 9 / 20) * 55 : ℝ) ^ ((5 : ℝ) / 2) ≤ 5033 :=
      rpow_five_halves_le (by norm_num) (by norm_num) (by norm_num)
    linarith

end Yq
