-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedIntrinsicHessian
public import SlowEquilibration.MixtureThresholds

/-! # Actual conditioning with the redundant radial score omitted

Value plus complete tangent gradient is nondegenerate for every positive-overlap
finite mixture. In particular this is the proper canonical target for a pure
model, where the radial derivative is a proved multiple of the value.
-/

@[expose] public section

namespace SlowEquilibration.ValueTangentConditioning

open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicGradientRegression
open SlowEquilibration.IntrinsicHessianLaw SlowEquilibration.ConditionedIntrinsicHessian
open SlowEquilibration.SphericalForm SlowEquilibration.SphereHessian
open scoped RealInnerProductSpace ENNReal Topology BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- The actual coordinate projection omitting exactly the radial score. -/
def forgetRadial (k : ℕ) : EuclideanSpace ℝ (Sum (Fin 2) (Fin k)) →L[ℝ]
    EuclideanSpace ℝ (Sum (Fin 1) (Fin k)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Sum (Fin 1) (Fin k) => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Sum.elim
      (fun _ => EuclideanSpace.proj (Sum.inl 0))
      (fun i => EuclideanSpace.proj (Sum.inr i))))

def valueTangentCLM {N P k : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin k → Vector N) : EuclideanDisorder N P →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin 1) (Fin k)) :=
  (forgetRadial k).comp (jointCLM c x e)

@[simp] theorem valueTangentCLM_apply_value {N P k : ℕ} (c : Degree P → ℝ)
    (x : Vector N) (e : Fin k → Vector N) (g : EuclideanDisorder N P) (i : Fin 1) :
    valueTangentCLM c x e g (Sum.inl i) = jet c 0 x (fun i => Fin.elim0 i) (unpackDisorder g) := by
  simp [valueTangentCLM, forgetRadial]

@[simp] theorem valueTangentCLM_apply_gradient {N P k : ℕ} (c : Degree P → ℝ)
    (x : Vector N) (e : Fin k → Vector N) (g : EuclideanDisorder N P) (i : Fin k) :
    valueTangentCLM c x e g (Sum.inr i) = jet c 1 x (fun _ => e i) (unpackDisorder g) := by
  simp [valueTangentCLM, forgetRadial]

/-- Actual covariance matrix of the value and tangent gradient, including
pure mixtures, where joint value/radial conditioning would be redundant. -/
theorem center_valueTangent_gram_matrix {N k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) x = 0) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Sum (Fin 1) (Fin k)) ℝ).toBasis
      (EuclideanSpace.basisFun (Sum (Fin 1) (Fin k)) ℝ).toBasis
      (GaussianRegression.gram (valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q) x e)).toLinearMap =
      Matrix.fromBlocks (((N : ℝ) * μ.xi Q) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0
        ((Q * μ.xi1 Q) • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
  classical
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ
  have hvalue := congrFun (congrFun (center_score_gram_matrix hN μ hQ x hx) 0) 0
  rw [LinearMap.toMatrix_apply] at hvalue
  change GaussianRegression.gram (scoreCLM c x) (EuclideanSpace.basisFun (Fin 2) ℝ 0) 0 = _ at hvalue
  rw [← actual_covariance_gram] at hvalue
  simp only [actualObservation, scoreCLM_apply_zero, unpack_euclideanDisorder,
    Matrix.smul_apply, smul_eq_mul, FiniteMixture.scoreCovariance] at hvalue
  ext i j
  rw [LinearMap.toMatrix_apply]
  change GaussianRegression.gram (valueTangentCLM c x e)
    (EuclideanSpace.basisFun (Sum (Fin 1) (Fin k)) ℝ j) i = _
  rw [← actual_covariance_gram]
  cases i with
  | inl i =>
    fin_cases i
    cases j with
    | inl j =>
      fin_cases j
      simpa only [actualObservation, valueTangentCLM_apply_value, unpack_euclideanDisorder,
        Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, ite_true, mul_one] using hvalue
    | inr j =>
      simpa only [actualObservation, valueTangentCLM_apply_value, valueTangentCLM_apply_gradient,
        unpack_euclideanDisorder, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] using
        value_tangent_gradient_covariance_zero c hc x (e j) (htan j)
  | inr i =>
    cases j with
    | inl j =>
      fin_cases j
      rw [covariance_comm]
      simpa only [actualObservation, valueTangentCLM_apply_value, valueTangentCLM_apply_gradient,
        unpack_euclideanDisorder, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] using
        value_tangent_gradient_covariance_zero c hc x (e i) (htan i)
    | inr j =>
      simp only [actualObservation, valueTangentCLM_apply_gradient, unpack_euclideanDisorder,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
      rw [tangent_gradient_covariance hN c hc x (e i) (e j) hx (htan i),
        orthonormal_iff_ite.mp he, firstCovariance_center, firstCovariance_mixture]

/-- Positive value and tangent variances prove genuine observation surjectivity. -/
theorem center_valueTangent_surjective {N k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) x = 0) :
    Surjective (valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q) x e) := by
  apply surjective_of_gram_det_ne_zero
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix
    (EuclideanSpace.basisFun (Sum (Fin 1) (Fin k)) ℝ).toBasis,
    center_valueTangent_gram_matrix hN μ hQ.le x hx e he htan,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_smul, Matrix.det_one, Matrix.det_one]
  simp only [Fintype.card_fin, pow_one, mul_one]
  exact mul_ne_zero (mul_pos (Nat.cast_pos.mpr hN) (μ.xi_pos hQ)).ne'
    (pow_ne_zero _ (mul_pos hQ (mixture_xi1_pos μ hQ)).ne')

/-- The real ambient Hessian annihilates this nonredundant observation lift. -/
theorem ambientHessian_valueTangent_lift_zero {N P k : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (e : Fin k → Vector N)
    (htan : ∀ i, inner ℝ (e i) x = 0) :
    (ambientHessianCLM c x e).comp (valueTangentCLM c x e).adjoint = 0 := by
  rw [valueTangentCLM, ContinuousLinearMap.adjoint_comp,
    ← ContinuousLinearMap.comp_assoc, ambientHessian_joint_lift_zero c hc x e htan,
    ContinuousLinearMap.zero_comp]

/-- The entire true ambient tangent Hessian keeps its actual law under every
proper value/tangent-gradient conditioning target. -/
theorem valueTangent_ambientHessian_map {N P k : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (e : Fin k → Vector N)
    (htan : ∀ i, inner ℝ (e i) x = 0)
    (a : EuclideanSpace ℝ (Sum (Fin 1) (Fin k))) :
    (coefficientKernel (valueTangentCLM c x e) a).map (hessianMatrix c x e) =
      (disorderLaw N P).map (hessianMatrix c x e) := by
  have hm : Measurable (actualObservation (ambientHessianCLM c x e)) :=
    (ambientHessianCLM c x e).continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
      (flatDisorder_measurable N P))
  have h := congrArg (fun m => m.map (hessianDecode k))
    (coefficientKernel_target_map_linear _ _ (ambientHessian_valueTangent_lift_zero c hc x e htan) a)
  rw [Measure.map_map (hessianDecode_measurable k) hm,
    Measure.map_map (hessianDecode_measurable k) hm] at h
  simpa only [Function.comp_def, hessianDecode_actual] using h

end
end SlowEquilibration.ValueTangentConditioning
