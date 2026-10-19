-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFiberDensity
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Coordinate independence of canonical whole-field regression

All genuine Gaussian kernels and pointwise pdfs commute with actual coefficient
isometries. This permits local coefficient splits without altering whole-field marks.
-/

@[expose] public section

namespace SlowEquilibration.GaussianRegression

open MeasureTheory ProbabilityTheory Set Function
open scoped RealInnerProductSpace ENNReal Topology

noncomputable section

variable {E D F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The actual Gram operator is unchanged by isometric coefficient coordinates. -/
theorem gram_comp_isometry (A : E →L[ℝ] F) (j : D ≃ₗᵢ[ℝ] E) :
    gram (A.comp (j : D →L[ℝ] E)) = gram A := by
  unfold gram
  rw [ContinuousLinearMap.adjoint_comp, j.adjoint_eq_symm]
  ext w
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, j.apply_symm_apply]

/-- The true minimum-norm coefficient lift commutes with an isometric change of coordinates. -/
theorem lift_comp_isometry (A : E →L[ℝ] F) (j : D ≃ₗᵢ[ℝ] E) :
    lift (A.comp (j : D →L[ℝ] E)) = (j.symm : E →L[ℝ] D).comp (lift A) := by
  unfold lift
  rw [gram_comp_isometry, ContinuousLinearMap.adjoint_comp, j.adjoint_eq_symm,
    ContinuousLinearMap.comp_assoc]

/-- The actual full residual commutes with the isometric coefficient coordinates. -/
theorem residual_comp_isometry (A : E →L[ℝ] F) (j : D ≃ₗᵢ[ℝ] E) :
    (j : D →L[ℝ] E).comp (residual (A.comp (j : D →L[ℝ] E))) =
      (residual A).comp (j : D →L[ℝ] E) := by
  ext x
  simp only [residual, ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply,
    map_sub, lift_comp_isometry, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, j.apply_symm_apply]

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace F] [BorelSpace F]

/-- Canonical whole-field regression kernels transform correctly at every target,
including target zero; the proof uses the genuine standard Gaussian isometry law. -/
theorem regressionKernel_comp_isometry (A : E →L[ℝ] F) (j : D ≃ₗᵢ[ℝ] E) (w : F) :
    (regressionKernel (A.comp (j : D →L[ℝ] E)) w).map j = regressionKernel A w := by
  rw [regressionKernel_apply, regressionKernel_apply, Measure.map_map j.continuous.measurable (by fun_prop)]
  have he : j ∘ (fun x : D => residual (A.comp (j : D →L[ℝ] E)) x +
      lift (A.comp (j : D →L[ℝ] E)) w) = (fun x : E => residual A x + lift A w) ∘ j := by
    funext x
    simp only [Function.comp_apply, map_add]
    have h0 := congrArg (fun T : D →L[ℝ] E => T x) (residual_comp_isometry A j)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] at h0
    rw [h0, lift_comp_isometry]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, j.apply_symm_apply]
  rw [he, ← Measure.map_map (by fun_prop) j.continuous.measurable, stdGaussian_map j]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace F] [BorelSpace F] in
/-- The pointwise observation pdf is unchanged by actual isometric coefficient
coordinates; this includes its literal zero-observation value. -/
theorem observationPdf_comp_isometry (A : E →L[ℝ] F) (j : D ≃ₗᵢ[ℝ] E) (w : F) :
    observationPdf (A.comp (j : D →L[ℝ] E)) w = observationPdf A w := by
  unfold observationPdf
  rw [gram_comp_isometry, lift_comp_isometry]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, j.symm.norm_map]

/-- Arbitrary full-field Borel expectations commute with the actual isometric
local coefficient split, for every prescribed target. -/
theorem regression_lintegral_comp_isometry (A : E →L[ℝ] F) (j : D ≃ₗᵢ[ℝ] E) (w : F)
    (phi : E → ℝ≥0∞) (hphi : Measurable phi) :
    (∫⁻ x, phi (j x) ∂regressionKernel (A.comp (j : D →L[ℝ] E)) w) =
      ∫⁻ x, phi x ∂regressionKernel A w := by
  rw [← regressionKernel_comp_isometry A j w, lintegral_map hphi j.continuous.measurable]

end
end SlowEquilibration.GaussianRegression
