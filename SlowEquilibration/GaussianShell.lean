-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianQuadratic
public import Mathlib.Probability.Moments.Basic

/-! Actual Gaussian squared-radius Chernoff bounds, in arbitrary finite
dimension. The rate is computed from the genuine Gaussian quadratic integral. -/

@[expose] public section
namespace SlowEquilibration.GaussianShell
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem integrable_exp_norm_sq {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : E => Real.exp (t * ‖x‖ ^ 2)) (stdGaussian E) := by
  have h := GaussianQuadratic.integrable_exp_quadratic (by linarith : 0 < 1 - 2 * t) (0 : E)
  convert h using 1
  ext x
  simp only [inner_zero_left]
  congr 1
  ring

theorem integral_exp_norm_sq {t : ℝ} (ht : t < 1 / 2) :
    (∫ x : E, Real.exp (t * ‖x‖ ^ 2) ∂stdGaussian E) =
      (1 - 2 * t) ^ (-((Module.finrank ℝ E : ℝ) / 2)) := by
  have h := GaussianQuadratic.integral_exp_quadratic (by linarith : 0 < 1 - 2 * t) (0 : E)
  simp only [inner_zero_left, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
    Real.exp_zero, mul_one] at h
  convert h using 1
  congr 1
  ext x
  congr 1
  ring

/-- The exact chi-square large deviation rate per ambient coordinate. -/
def rate (a : ℝ) : ℝ := (a - 1 - Real.log a) / 2

theorem rate_pos {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) : 0 < rate a := by
  have h := Real.log_lt_sub_one_of_pos ha ha1
  unfold rate
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem optimized_rhs {a : ℝ} (ha : 0 < a) :
    Real.exp (-((a - 1) / (2 * a)) * (a * Module.finrank ℝ E)) *
      (1 - 2 * ((a - 1) / (2 * a))) ^ (-((Module.finrank ℝ E : ℝ) / 2)) =
      Real.exp (-(Module.finrank ℝ E : ℝ) * rate a) := by
  have hi : 1 - 2 * ((a - 1) / (2 * a)) = a⁻¹ := by field_simp; ring
  rw [hi, Real.rpow_def_of_pos (inv_pos.mpr ha), ← Real.exp_add, Real.log_inv]
  congr 1
  unfold rate
  field_simp
  ring

theorem upper_tail {a : ℝ} (ha : 1 < a) :
    (stdGaussian E).real {x | a * Module.finrank ℝ E ≤ ‖x‖ ^ 2} ≤
      Real.exp (-(Module.finrank ℝ E : ℝ) * rate a) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have ht : (a - 1) / (2 * a) < 1 / 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * a)).mpr
    linarith
  have h := measure_ge_le_exp_mul_mgf (μ := stdGaussian E) (X := fun x => ‖x‖ ^ 2)
    (a * Module.finrank ℝ E) (show 0 ≤ (a - 1) / (2 * a) by positivity)
    (integrable_exp_norm_sq ht)
  rw [mgf, integral_exp_norm_sq ht, optimized_rhs ha0] at h
  exact h

theorem lower_tail {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (stdGaussian E).real {x | ‖x‖ ^ 2 ≤ a * Module.finrank ℝ E} ≤
      Real.exp (-(Module.finrank ℝ E : ℝ) * rate a) := by
  have ht : (a - 1) / (2 * a) < 1 / 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * a)).mpr
    linarith
  have h := measure_le_le_exp_mul_mgf (μ := stdGaussian E) (X := fun x => ‖x‖ ^ 2)
    (a * Module.finrank ℝ E)
    (show (a - 1) / (2 * a) ≤ 0 from div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
    (integrable_exp_norm_sq ht)
  rw [mgf, integral_exp_norm_sq ht, optimized_rhs ha] at h
  exact h

theorem shell_mass_lower {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 1 < b) :
    1 - Real.exp (-(Module.finrank ℝ E : ℝ) * rate a) -
      Real.exp (-(Module.finrank ℝ E : ℝ) * rate b) ≤
        (stdGaussian E).real {x | a * Module.finrank ℝ E ≤ ‖x‖ ^ 2 ∧
          ‖x‖ ^ 2 ≤ b * Module.finrank ℝ E} := by
  let S : Set E := {x | a * Module.finrank ℝ E ≤ ‖x‖ ^ 2 ∧
    ‖x‖ ^ 2 ≤ b * Module.finrank ℝ E}
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const (measurable_norm.pow_const 2)).inter
      (measurableSet_le (measurable_norm.pow_const 2) measurable_const)
  have hsub : Sᶜ ⊆ {x | ‖x‖ ^ 2 ≤ a * Module.finrank ℝ E} ∪
      {x | b * Module.finrank ℝ E ≤ ‖x‖ ^ 2} := by
    intro x hx
    simp only [S, mem_compl_iff, mem_ofPred_eq, not_and_or, not_le, mem_union] at *
    exact hx.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)
  have hbound := (measureReal_mono hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add (lower_tail ha ha1) (upper_tail hb)))
  have htotal := measureReal_add_measureReal_compl (μ := stdGaussian E) hS
  rw [probReal_univ] at htotal
  change _ ≤ (stdGaussian E).real S
  linarith

theorem shell_mass_eventually {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 1 < b) :
    ∀ᶠ N : ℕ in atTop,
      (1 / 2 : ℝ) ≤ (stdGaussian (EuclideanSpace ℝ (Fin N))).real
        {x | a * N ≤ ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 ≤ b * N} := by
  have hdec (c : ℝ) (hc : 0 < c) :
      Tendsto (fun N : ℕ => Real.exp (-(N : ℝ) * c)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const hc)
  have hA := (hdec (rate a) (rate_pos ha ha1.ne)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hB := (hdec (rate b) (rate_pos (by linarith) hb.ne')).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hA, hB] with N hA hB
  have h := shell_mass_lower (E := EuclideanSpace ℝ (Fin N)) ha ha1 hb
  simp only [finrank_euclideanSpace, Fintype.card_fin] at h
  linarith

end
end SlowEquilibration.GaussianShell
