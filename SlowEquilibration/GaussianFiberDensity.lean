-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianRegressionDensity
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Pointwise Gaussian regression on every affine observation fiber

The ambient ordinary Gaussian pdf is factored exactly on every specified fiber.
This proves the weighted fiber identity for arbitrary Borel marks at observation
zero without an almost-everywhere choice of a conditional density.
-/

@[expose] public section

namespace SlowEquilibration.GaussianRegression

open MeasureTheory ProbabilityTheory Set Function
open scoped RealInnerProductSpace Topology ENNReal

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma gram_sqrt_det_pos (A : E →L[ℝ] F) (hA : Surjective A) : 0 < Real.sqrt (gram A).det := by
  rw [← squareObservation_abs_det A hA]
  exact abs_pos.mpr (squareObservation A hA).toLinearEquiv.isUnit_det'.ne_zero

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma gram_det_pos (A : E →L[ℝ] F) (hA : Surjective A) : 0 < (gram A).det :=
  Real.sqrt_pos.mp (gram_sqrt_det_pos A hA)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma normalizer_kernel_product (A : E →L[ℝ] F) (hA : Surjective A) :
    GaussianDensity.normalizer E = GaussianDensity.normalizer F * GaussianDensity.normalizer A.ker := by
  have hd : Module.finrank ℝ E = Module.finrank ℝ A.ker + Module.finrank ℝ F := by
    rw [← A.ker.finrank_add_finrank_orthogonal]
    rw [(effectiveEquiv A hA).finrank_eq]
  unfold GaussianDensity.normalizer
  rw [hd, Nat.cast_add, add_div, Real.rpow_add (by positivity), mul_inv_rev]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma affine_fiber_norm_sq (A : E →L[ℝ] F) (w : F) (k : A.ker) :
    ‖(k : E) + lift A w‖ ^ 2 = ‖k‖ ^ 2 + ‖lift A w‖ ^ 2 := by
  rw [norm_add_sq_real, lift_orthogonal_ker A w k k.2]
  simp only [Submodule.norm_coe, mul_zero, add_zero]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- Actual ambient Gaussian pdf factorization, before any fiber integration. -/
theorem density_on_affine_fiber (A : E →L[ℝ] F) (hA : Surjective A) (w : F) (k : A.ker) :
    GaussianDensity.density ((k : E) + lift A w) =
      GaussianDensity.normalizer F * Real.exp (-(1 / 2 : ℝ) * ‖lift A w‖ ^ 2) *
        GaussianDensity.density k := by
  unfold GaussianDensity.density
  rw [normalizer_kernel_product A hA, affine_fiber_norm_sq]
  rw [show -(1 / 2 : ℝ) * (‖k‖ ^ 2 + ‖lift A w‖ ^ 2) =
    -(1 / 2 : ℝ) * ‖k‖ ^ 2 + -(1 / 2 : ℝ) * ‖lift A w‖ ^ 2 by ring, Real.exp_add]
  ring

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- Exact pointwise coarea/regression density identity at every observation,
including the literal zero fiber and every Borel mark on that fiber. -/
theorem ennreal_density_on_affine_fiber (A : E →L[ℝ] F) (hA : Surjective A) (w : F) (k : A.ker) :
    ENNReal.ofReal (GaussianDensity.density ((k : E) + lift A w)) =
      ENNReal.ofReal (Real.sqrt (gram A).det) * observationPdf A w *
        ENNReal.ofReal (GaussianDensity.density k) := by
  have hp := gram_sqrt_det_pos A hA
  have hphi : 0 ≤ (Real.sqrt (gram A).det)⁻¹ * GaussianDensity.normalizer F *
      Real.exp (-(1 / 2 : ℝ) * ‖lift A w‖ ^ 2) := by
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hp.le) GaussianDensity.normalizer_pos.le)
      (Real.exp_pos _).le
  have hr : GaussianDensity.density ((k : E) + lift A w) =
      Real.sqrt (gram A).det *
        (((Real.sqrt (gram A).det)⁻¹ * GaussianDensity.normalizer F *
          Real.exp (-(1 / 2 : ℝ) * ‖lift A w‖ ^ 2)) * GaussianDensity.density k) := by
    rw [density_on_affine_fiber A hA]
    field_simp [hp.ne']
  have he := congrArg ENNReal.ofReal hr
  rw [ENNReal.ofReal_mul hp.le, ENNReal.ofReal_mul hphi] at he
  simpa only [observationPdf, mul_assoc] using he

omit [MeasurableSpace F] [BorelSpace F] in
/-- The genuine full-vector residual law is the actual subspace Gaussian law. -/
theorem residualLaw_eq_kernelGaussian (A : E →L[ℝ] F) (hA : Surjective A) :
    residualLaw A = (stdGaussian A.ker).map (fun k : A.ker => (k : E)) := by
  rw [← projection_stdGaussian A.ker, Measure.map_map measurable_subtype_coe (by fun_prop)]
  unfold residualLaw
  rw [residual_eq_starProjection A hA]
  congr 1

/-- The canonical whole-field kernel at every specified observation is the
actual affine translation of the genuine kernel-subspace Gaussian. -/
theorem regressionKernel_eq_affine_kernelGaussian (A : E →L[ℝ] F) (hA : Surjective A) (w : F) :
    regressionKernel A w = (stdGaussian A.ker).map (fun k : A.ker => (k : E) + lift A w) := by
  have he : regressionKernel A w = (residualLaw A).map (fun r => r + lift A w) := by
    rw [regressionKernel_apply, residualLaw, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [he, residualLaw_eq_kernelGaussian A hA,
    Measure.map_map (by fun_prop) measurable_subtype_coe]
  rfl

/-- Every fixed affine observation fiber obeys the true weighted Gaussian
regression identity for arbitrary nonnegative Borel marks, without any slice-a.e. premise. -/
theorem weighted_affine_fiber_formula (A : E →L[ℝ] F) (hA : Surjective A) (w : F)
    (phi : E → ℝ≥0∞) (hphi : Measurable phi) :
    (∫⁻ k : A.ker, ENNReal.ofReal (GaussianDensity.density ((k : E) + lift A w)) *
      phi ((k : E) + lift A w) ∂volume) =
        ENNReal.ofReal (Real.sqrt (gram A).det) * observationPdf A w *
          ∫⁻ y, phi y ∂regressionKernel A w := by
  rw [regressionKernel_eq_affine_kernelGaussian A hA w, lintegral_map hphi (by fun_prop),
    GaussianDensity.stdGaussian_eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul _
      GaussianDensity.density_continuous.measurable.ennreal_ofReal (by fun_prop)]
  simp_rw [ennreal_density_on_affine_fiber A hA w]
  simp only [mul_assoc, Pi.mul_apply]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ (show observationPdf A w ≠ ⊤ from ENNReal.ofReal_ne_top)]

end
end SlowEquilibration.GaussianRegression
