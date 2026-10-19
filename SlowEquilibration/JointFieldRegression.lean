-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.WholeFieldRegression
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Joint score and tangent-gradient whole-field regression

The observation includes the value, radial derivative, and all tangent gradient
coordinates. Its block covariance and nondegeneracy come from the actual field.
-/

@[expose] public section

namespace SlowEquilibration.WholeFieldRegression

open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open scoped RealInnerProductSpace ENNReal Topology

noncomputable section

/-- Simultaneous actual value/radial/tangent observation of every tensor coordinate. -/
def jointCLM {N P k : ℕ} (c : Degree P → ℝ) (u : Vector N)
    (e : Fin k → Vector N) : EuclideanDisorder N P →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin 2) (Fin k)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Sum (Fin 2) (Fin k) => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Sum.elim
      (fun i => (EuclideanSpace.proj i).comp (scoreCLM c u))
      (fun j => (EuclideanSpace.proj j).comp (gradientCLM c u e))))

@[simp] theorem jointCLM_apply_inl {N P k : ℕ} (c : Degree P → ℝ) (u : Vector N)
    (e : Fin k → Vector N) (g : EuclideanDisorder N P) (i : Fin 2) :
    jointCLM c u e g (Sum.inl i) = scoreCLM c u g i := by simp [jointCLM]

@[simp] theorem jointCLM_apply_inr {N P k : ℕ} (c : Degree P → ℝ) (u : Vector N)
    (e : Fin k → Vector N) (g : EuclideanDisorder N P) (i : Fin k) :
    jointCLM c u e g (Sum.inr i) = gradientCLM c u e g i := by simp [jointCLM]

/-- The full covariance is its true block matrix; cross blocks vanish by
actual tensor derivative covariance, rather than a postulated independent model. -/
theorem center_joint_gram_matrix {N k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Sum (Fin 2) (Fin k)) ℝ).toBasis
      (EuclideanSpace.basisFun (Sum (Fin 2) (Fin k)) ℝ).toBasis
      (GaussianRegression.gram (jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u e)).toLinearMap =
      Matrix.fromBlocks ((N : ℝ) • μ.scoreCovariance Q) 0 0
        ((Q * μ.xi1 Q) • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
  classical
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc : ∀ p, 0 ≤ c p := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ
  have hcross (i : Fin 2) (j : Fin k) :
      cov[fun J : Disorder N μ.maxDegree => scoreCLM c u (euclideanDisorder J) i,
        fun J : Disorder N μ.maxDegree => gradientCLM c u e (euclideanDisorder J) j;
        disorderLaw N μ.maxDegree] = 0 := by
    fin_cases i
    · simpa [scoreCLM] using
        value_tangent_gradient_covariance_zero c hc u (e j) (htan j)
    · simpa [scoreCLM] using
        radial_tangent_gradient_covariance_zero c hc u (e j) (htan j)
  ext i j
  rw [LinearMap.toMatrix_apply]
  change GaussianRegression.gram (jointCLM c u e)
    (EuclideanSpace.basisFun (Sum (Fin 2) (Fin k)) ℝ j) i = _
  rw [← actual_covariance_gram]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hs := congrFun (congrFun (center_score_gram_matrix hN μ hQ u hu) i) j
      rw [LinearMap.toMatrix_apply] at hs
      change GaussianRegression.gram (scoreCLM c u) (EuclideanSpace.basisFun (Fin 2) ℝ j) i = _ at hs
      rw [← actual_covariance_gram] at hs
      simpa only [actualObservation, jointCLM_apply_inl, Matrix.fromBlocks_apply₁₁] using hs
    | inr j =>
      simpa only [actualObservation, jointCLM_apply_inl, jointCLM_apply_inr,
        Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] using hcross i j
  | inr i =>
    cases j with
    | inl j =>
      rw [covariance_comm]
      simpa only [actualObservation, jointCLM_apply_inl, jointCLM_apply_inr,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] using hcross j i
    | inr j =>
      simp only [actualObservation, jointCLM_apply_inr, gradientCLM_apply, unpack_euclideanDisorder,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
      rw [tangent_gradient_covariance hN c hc u (e i) (e j) hu (htan i),
        orthonormal_iff_ite.mp he, firstCovariance_center, firstCovariance_mixture]

/-- The joint covariance determinant includes both the N² score factor and
all k genuine tangent-gradient variance factors. -/
theorem center_joint_gram_det {N k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0) :
    (GaussianRegression.gram (jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u e)).det =
      ((N : ℝ) ^ 2 * (μ.scoreCovariance Q).det) * (Q * μ.xi1 Q) ^ k := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix
    (EuclideanSpace.basisFun (Sum (Fin 2) (Fin k)) ℝ).toBasis,
    center_joint_gram_matrix hN μ hQ u hu e he htan,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_smul, Matrix.det_one]
  simp

/-- The full score/tangent observation is genuinely surjective for a nonpure
finite mixture; all hypotheses describe the actual coefficients and frame. -/
theorem center_joint_surjective {N k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0) :
    Surjective (jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u e) := by
  apply surjective_of_gram_det_ne_zero
  rw [center_joint_gram_det hN μ hQ.le u hu e he htan]
  exact (mul_pos (mul_pos (sq_pos_of_pos (Nat.cast_pos.mpr hN)) (μ.scoreCovariance_det_pos hQ hnp))
    (pow_pos (mul_pos hQ (mixture_xi1_pos μ hQ)) k)).ne'

/-- Full Borel whole-disorder regression for the actual simultaneous score
and gradient, with all actual observation nondegeneracy discharged. -/
theorem joint_whole_field_disintegration {N k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0)
    (phi : EuclideanSpace ℝ (Sum (Fin 2) (Fin k)) × Disorder N μ.maxDegree → ℝ≥0∞)
    (hphi : Measurable phi) :
    let A := jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u e
    (∫⁻ J, phi (actualObservation A J, J) ∂disorderLaw N μ.maxDegree) =
      ∫⁻ w, ∫⁻ J, phi (w, J) ∂coefficientKernel A w
        ∂GaussianRegression.observationLaw A :=
  actual_disintegration _ (center_joint_surjective hN μ hQ hnp u hu e he htan) phi hphi

/-- Explicit joint observationPdf formula at literal zero. It is the actual
density when positive Q and mixture nonpurity give nondegeneracy. -/
theorem center_joint_pdf_zero {N k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0) :
    GaussianRegression.observationPdf
      (jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u e) 0 =
      ENNReal.ofReal (GaussianDensity.normalizer (EuclideanSpace ℝ (Sum (Fin 2) (Fin k))) /
        Real.sqrt (((N : ℝ) ^ 2 * (μ.scoreCovariance Q).det) * (Q * μ.xi1 Q) ^ k)) := by
  rw [GaussianRegression.observationPdf_zero, center_joint_gram_det hN μ hQ u hu e he htan]

/-- Exact ambient-density/fiber regression identity for a Borel mark of all
original tensor coordinates, at every specified target, including zero. -/
theorem actual_weighted_affine_fiber {N P : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (A : EuclideanDisorder N P →L[ℝ] F) (hA : Surjective A) (w : F)
    (phi : Disorder N P → ℝ≥0∞) (hphi : Measurable phi) :
    (∫⁻ k : A.ker, ENNReal.ofReal (GaussianDensity.density
        ((k : EuclideanDisorder N P) + GaussianRegression.lift A w)) *
      phi (unpackDisorder ((k : EuclideanDisorder N P) + GaussianRegression.lift A w)) ∂volume) =
      ENNReal.ofReal (Real.sqrt (GaussianRegression.gram A).det) *
        GaussianRegression.observationPdf A w * ∫⁻ J, phi J ∂coefficientKernel A w := by
  rw [coefficientKernel_apply, lintegral_map hphi (unpackCLM N P).continuous.measurable]
  exact GaussianRegression.weighted_affine_fiber_formula A hA w
    (fun g => phi (unpackCLM N P g)) (hphi.comp (unpackCLM N P).continuous.measurable)

/-- Full-field Borel marks on the actual zero-gradient fiber have the
canonical pointwise Gaussian regression factor, with no exceptional target. -/
theorem gradient_weighted_zero_fiber {N k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0)
    (phi : Disorder N μ.maxDegree → ℝ≥0∞) (hphi : Measurable phi) :
    let A := gradientCLM (centerCoefficients (mixtureCoefficients μ) Q) u e
    (∫⁻ z : A.ker, ENNReal.ofReal (GaussianDensity.density (z : EuclideanDisorder N μ.maxDegree)) *
      phi (unpackDisorder (z : EuclideanDisorder N μ.maxDegree)) ∂volume) =
      ENNReal.ofReal (Real.sqrt ((Q * μ.xi1 Q) ^ k)) *
        GaussianRegression.observationPdf A 0 * ∫⁻ J, phi J ∂coefficientKernel A 0 := by
  dsimp only
  have h := actual_weighted_affine_fiber _ (center_gradient_surjective hN μ hQ u hu e he htan) 0 phi hphi
  simpa only [map_zero, add_zero, center_gradient_gram_det hN μ hQ.le u hu e he htan] using h

/-- Full-field Borel marks on the simultaneous literal zero score/gradient
fiber, with actual nondegeneracy discharged from the nonpure mixture. -/
theorem joint_weighted_zero_fiber {N k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0)
    (phi : Disorder N μ.maxDegree → ℝ≥0∞) (hphi : Measurable phi) :
    let A := jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u e
    (∫⁻ z : A.ker, ENNReal.ofReal (GaussianDensity.density (z : EuclideanDisorder N μ.maxDegree)) *
      phi (unpackDisorder (z : EuclideanDisorder N μ.maxDegree)) ∂volume) =
      ENNReal.ofReal (Real.sqrt (((N : ℝ) ^ 2 * (μ.scoreCovariance Q).det) * (Q * μ.xi1 Q) ^ k)) *
        GaussianRegression.observationPdf A 0 * ∫⁻ J, phi J ∂coefficientKernel A 0 := by
  dsimp only
  have h := actual_weighted_affine_fiber _ (center_joint_surjective hN μ hQ hnp u hu e he htan) 0 phi hphi
  simpa only [map_zero, add_zero, center_joint_gram_det hN μ hQ.le u hu e he htan] using h

end
end SlowEquilibration.WholeFieldRegression
