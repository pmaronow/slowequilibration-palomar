-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCountIntegrability
public import SlowEquilibration.ConditionedIntrinsicHessian
public import SlowEquilibration.PureConditionedHessian

/-! Actual conditional determinant integrability at every radial shift. -/

@[expose] public section
namespace SlowEquilibration.UnrestrictedConditionedDeterminants

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open IntrinsicHessianLaw IntrinsicGradientRegression WholeFieldRegression
open ConditionedIntrinsicHessian PureConditionedHessian SphericalSequentialRegression
open SphericalCountIntegrability
open scoped ENNReal BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal shifted GOE determinant is integrable at every real shift,
without a spectral-gap premise. -/
lemma fixed_shifted_determinant_integrable (n N : ℕ) (b k : ℝ) :
    Integrable (fun W : Matrix (Fin n) (Fin n) ℝ => (W-k • 1).det) (goeLaw n N b) := by
  simp_rw [Matrix.det_apply']
  apply integrable_finsetSum
  intro σ hσ
  apply Integrable.const_mul
  apply GOEPrincipalMinors.integrable_product_of_all_moments
  intro i hi p hp
  convert (goe_entry_memLp n N b (σ i) i hp).sub
    (memLp_const (k*(1 : Matrix (Fin n) (Fin n) ℝ) (σ i) i)) using 1
  funext W
  rfl

lemma shifted_law_abs_det_integrable {Ω : Type*} [MeasurableSpace Ω] {η : Measure Ω}
    (n N : ℕ) (b k : ℝ) (H : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hH : HasLaw H ((goeLaw n N b).map (fun W => W-k • 1)) η) :
    Integrable (fun w => |(H w).det|) η := by
  have hd : Measurable (fun W : Matrix (Fin n) (Fin n) ℝ => |W.det|) :=
    continuous_id.matrix_det.abs.measurable
  have hs : Measurable (fun W : Matrix (Fin n) (Fin n) ℝ => W-k • 1) := by fun_prop
  have hi : Integrable (fun W : Matrix (Fin n) (Fin n) ℝ => |W.det|)
      ((goeLaw n N b).map (fun W => W-k • 1)) :=
    (integrable_map_measure hd.aestronglyMeasurable hs.aemeasurable).mpr
      (fixed_shifted_determinant_integrable n N b k).abs
  simpa only [Function.comp_def] using hH.integrable_comp hi

/-- Unrestricted actual mixed posterior determinant integrability at every
specified score target, including shifts inside the semicircle support. -/
theorem mixed_intrinsicDet_integrable {n : ℕ} (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector (n+1)) (hx : ‖x‖^2=(n+1 : ℕ)) (b : EuclideanSpace ℝ (Fin 2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    Integrable (fun J => |(intrinsicHessian (field c J) x).det|)
      (coefficientKernel (jointCLM c x (tangentFrame x hx))
        (jointScoreTarget n (((n+1 : ℕ) : ℝ) • b))) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let target := jointScoreTarget n (((n+1 : ℕ) : ℝ) • b)
  have hH := conditioned_intrinsicMatrix_hasLaw μ hQ hnp x hx target
  have hi := shifted_law_abs_det_integrable n (n+1) (Q^2*μ.xi2 Q)
    (target (Sum.inl 1)/(n+1 : ℕ)) (intrinsicMatrix c x hx) hH
  convert hi using 1
  funext J
  unfold intrinsicMatrix
  rw [LinearMap.det_toMatrix]

/-- Proper pure conditioning omits the redundant radial observation and has
finite determinant expectation at every normalized value h. -/
theorem pure_intrinsicDet_integrable {n : ℕ} (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n+1)) (hx : ‖x‖^2=(n+1 : ℕ)) (h : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    Integrable (fun J => |(intrinsicHessian (field c J) x).det|)
      (coefficientKernel (ValueTangentConditioning.valueTangentCLM c x (tangentFrame x hx))
        (valueTarget n h)) := by
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hH := pure_hessian_at_normalized_value p hp alpha halpha hQ x hx h
  have hi := shifted_law_abs_det_integrable n (n+1) (Q^2*μ.xi2 Q) ((p:ℝ)*h)
    (intrinsicMatrix c x hx) hH
  convert hi using 1
  funext J
  unfold intrinsicMatrix
  rw [LinearMap.det_toMatrix]

end
end SlowEquilibration.UnrestrictedConditionedDeterminants
