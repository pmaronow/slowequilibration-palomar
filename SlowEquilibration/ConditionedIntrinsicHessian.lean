-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.IntrinsicHessianLaw

/-! # Actual Hessian under prescribed whole-field value/radial/gradient conditioning

The canonical full tensor regression version is evaluated at every target.
The true tangent ambient Hessian annihilates the joint observation lift, so
its GOE law survives conditioning. The complete intrinsic Hessian has the
specified radial identity shift.
-/

@[expose] public section

namespace SlowEquilibration.ConditionedIntrinsicHessian

open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalForm SlowEquilibration.SphereHessian
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicGradientRegression
open SlowEquilibration.IntrinsicHessianLaw
open scoped RealInnerProductSpace ENNReal Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- Genuine observation law invariance holds at every specified target,
including nonzero marks of probability zero. -/
theorem coefficientKernel_target_map_linear {N P : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    (A : EuclideanDisorder N P →L[ℝ] F) (B : EuclideanDisorder N P →L[ℝ] G)
    (hBA : B.comp A.adjoint = 0) (w : F) :
    (coefficientKernel A w).map (actualObservation B) =
      (disorderLaw N P).map (actualObservation B) := by
  have hm : Measurable (actualObservation B) :=
    B.continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
      (flatDisorder_measurable N P))
  have hBlift (v : F) : B (GaussianRegression.lift A v) = 0 := by
    have h := congrArg (fun L : F →L[ℝ] G => L ((GaussianRegression.gram A).inverse v)) hBA
    exact h
  have hBres (g : EuclideanDisorder N P) : B (GaussianRegression.residual A g) = B g := by
    change B (g - GaussianRegression.lift A (A g)) = B g
    rw [map_sub, hBlift, sub_zero]
  rw [coefficientKernel_apply, GaussianRegression.regressionKernel_apply,
    Measure.map_map hm (unpackCLM N P).continuous.measurable,
    Measure.map_map (hm.comp (unpackCLM N P).continuous.measurable) (by fun_prop)]
  have he : (actualObservation B ∘ unpackCLM N P) ∘
      (fun g => GaussianRegression.residual A g + GaussianRegression.lift A w) = B := by
    funext g
    change B (GaussianRegression.residual A g + GaussianRegression.lift A w) = B g
    rw [map_add, hBres, hBlift, add_zero]
  rw [he]
  exact ((hasLaw_map B.continuous.measurable.aemeasurable).fun_comp
    (actual_flattened_gaussian N P)).map_eq.symm

/-- Actual full ambient tangent Hessian as a coefficient-linear observation. -/
def ambientHessianCLM {N P k : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin k → Vector N) : EuclideanDisorder N P →L[ℝ]
      EuclideanSpace ℝ (Fin k × Fin k) :=
  jetFamilyCLM c (fun _ => 2) (fun _ => x) (fun ij => ![e ij.1, e ij.2])

@[simp] theorem ambientHessianCLM_apply {N P k : ℕ} (c : Degree P → ℝ)
    (x : Vector N) (e : Fin k → Vector N) (g : EuclideanDisorder N P) (i j : Fin k) :
    ambientHessianCLM c x e g (i,j) = hessianEntry c x e i j (unpackDisorder g) := by
  simp [ambientHessianCLM, hessianEntry]

/-- All Hessian/score/gradient cross covariances vanish in the actual tensor
law, hence the genuine ambient Hessian annihilates the joint observed lift. -/
theorem ambientHessian_joint_lift_zero {N P k : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (e : Fin k → Vector N)
    (htan : ∀ i, inner ℝ (e i) x = 0) :
    (ambientHessianCLM c x e).comp (jointCLM c x e).adjoint = 0 := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Sum (Fin 2) (Fin k)) ℝ).toBasis.ext
  intro j
  apply PiLp.ext
  intro ij
  rcases ij with ⟨i,l⟩
  let f := (EuclideanSpace.proj (i,l)).comp (ambientHessianCLM c x e)
  have h := actual_scalar_cross_covariance f (jointCLM c x e)
    (EuclideanSpace.basisFun (Sum (Fin 2) (Fin k)) ℝ j)
  simp only [EuclideanSpace.basisFun_inner] at h
  change cov[fun J : Disorder N P => ambientHessianCLM c x e (euclideanDisorder J) (i,l),
    fun J : Disorder N P => jointCLM c x e (euclideanDisorder J) j; disorderLaw N P] =
      ambientHessianCLM c x e ((jointCLM c x e).adjoint
        (EuclideanSpace.basisFun (Sum (Fin 2) (Fin k)) ℝ j)) (i,l) at h
  change ambientHessianCLM c x e ((jointCLM c x e).adjoint
      (EuclideanSpace.basisFun (Sum (Fin 2) (Fin k)) ℝ j)) (i,l) = 0
  rw [← h]
  simp only [ambientHessianCLM_apply, unpack_euclideanDisorder]
  cases j with
  | inl j =>
    fin_cases j
    · change cov[hessianEntry c x e i l,
        fun J => scoreCLM c x (euclideanDisorder J) 0; disorderLaw N P] = 0
      simp only [scoreCLM_apply_zero, unpack_euclideanDisorder]
      exact hessian_value_covariance_zero c hc x e htan i l
    · change cov[hessianEntry c x e i l,
        fun J => scoreCLM c x (euclideanDisorder J) 1; disorderLaw N P] = 0
      simp only [scoreCLM_apply_one, unpack_euclideanDisorder]
      exact hessian_gradient_covariance_zero c hc x e htan i l x
  | inr j =>
    change cov[hessianEntry c x e i l,
      fun J => gradientCLM c x e (euclideanDisorder J) j; disorderLaw N P] = 0
    simp only [gradientCLM_apply, unpack_euclideanDisorder]
    exact hessian_gradient_covariance_zero c hc x e htan i l (e j)

/-- Complete matrix decoding of the actual coefficient Hessian observation. -/
def hessianDecode (k : ℕ) (y : EuclideanSpace ℝ (Fin k × Fin k)) :
    Matrix (Fin k) (Fin k) ℝ := fun i j => y (i,j)

lemma hessianDecode_measurable (k : ℕ) : Measurable (hessianDecode k) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact (EuclideanSpace.proj _).continuous.measurable

lemma hessianDecode_actual {N P k : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin k → Vector N) (J : Disorder N P) :
    hessianDecode k (actualObservation (ambientHessianCLM c x e) J) = hessianMatrix c x e J := by
  funext i j
  change ambientHessianCLM c x e (euclideanDisorder J) (i,j) = hessianEntry c x e i j J
  rw [ambientHessianCLM_apply, unpack_euclideanDisorder]

/-- The canonical full original tensor law at every joint score/gradient
target retains the literal ambient Hessian law. -/
theorem ambientHessian_conditioned_map {N P k : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (e : Fin k → Vector N)
    (htan : ∀ i, inner ℝ (e i) x = 0)
    (a : EuclideanSpace ℝ (Sum (Fin 2) (Fin k))) :
    (coefficientKernel (jointCLM c x e) a).map (hessianMatrix c x e) =
      (disorderLaw N P).map (hessianMatrix c x e) := by
  have hm : Measurable (actualObservation (ambientHessianCLM c x e)) :=
    (ambientHessianCLM c x e).continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
      (flatDisorder_measurable N P))
  have h := congrArg (fun m => m.map (hessianDecode k))
    (coefficientKernel_target_map_linear _ _ (ambientHessian_joint_lift_zero c hc x e htan) a)
  rw [Measure.map_map (hessianDecode_measurable k) hm,
    Measure.map_map (hessianDecode_measurable k) hm] at h
  simpa only [Function.comp_def, hessianDecode_actual] using h

/-- The actual Hessian has its full GOE law under the canonical whole-tensor
kernel, evaluated at every prescribed actual score/gradient target. -/
theorem center_conditioned_ambient_hasLaw {N k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) x = 0)
    (a : EuclideanSpace ℝ (Sum (Fin 2) (Fin k))) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    HasLaw (hessianMatrix c x e) (goeLaw k N (Q ^ 2 * μ.xi2 Q))
      (coefficientKernel (jointCLM c x e) a) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hm : Measurable (actualObservation (ambientHessianCLM c x e)) :=
    (ambientHessianCLM c x e).continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate N μ.maxDegree => ℝ)).symm.continuous.measurable.comp
      (flatDisorder_measurable N μ.maxDegree))
  have hH : Measurable (hessianMatrix c x e) := by
    convert (hessianDecode_measurable k).comp hm using 1
    funext J
    exact (hessianDecode_actual c x e J).symm
  refine ⟨hH.aemeasurable, ?_⟩
  rw [ambientHessian_conditioned_map c
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ) x e htan]
  exact (center_hessian_matrix_hasLaw hN μ hQ x hx e he htan).map_eq

/-- Actual operator matrix in the constructed complete tangent orthonormal basis. -/
def intrinsicMatrix {n P : ℕ} (c : Degree P → ℝ) (x : Vector (n + 1))
    (hx : ‖x‖ ^ 2 = (n + 1 : ℕ)) (J : Disorder (n + 1) P) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (tangentBasis x hx).toBasis (tangentBasis x hx).toBasis
    (intrinsicHessian (field c J) x).toLinearMap

/-- Genuine full intrinsic Hessian law at every canonical nonpure-mixture
conditioning target. The actual radial score produces the literal identity
shift, and the whole original coefficient kernel is retained. -/
theorem conditioned_intrinsicMatrix_hasLaw {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector (n + 1)) (hx : ‖x‖ ^ 2 = (n + 1 : ℕ))
    (a : EuclideanSpace ℝ (Sum (Fin 2) (Fin n))) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    HasLaw (intrinsicMatrix c x hx)
      ((goeLaw n (n + 1) (Q ^ 2 * μ.xi2 Q)).map
        (fun W => W - (a (Sum.inl 1) / (n + 1 : ℕ)) • (1 : Matrix (Fin n) (Fin n) ℝ)))
      (coefficientKernel (jointCLM c x (tangentFrame x hx)) a) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hH := center_conditioned_ambient_hasLaw (by omega) μ hQ.le x hx
    (tangentFrame x hx) (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx) a
  have hm : Measurable (fun W : Matrix (Fin n) (Fin n) ℝ =>
      W - (a (Sum.inl 1) / (n + 1 : ℕ)) • 1) := by fun_prop
  have hshift := (hasLaw_map hm.aemeasurable).fun_comp hH
  apply hshift.congr
  filter_upwards [coefficientKernel_observation_ae _
    (center_joint_surjective (by omega) μ hQ hnp x hx (tangentFrame x hx)
      (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx)) a] with J hJ
  have hk := congrArg (fun y : EuclideanSpace ℝ (Sum (Fin 2) (Fin n)) => y (Sum.inl 1)) hJ
  change scoreCLM c x (euclideanDisorder J) 1 = a (Sum.inl 1) at hk
  rw [scoreCLM_apply_one, unpack_euclideanDisorder] at hk
  change intrinsicMatrix c x hx J = _
  rw [intrinsicMatrix, intrinsicHessian_toMatrix c J x hx, radialMultiplier_eq_jet, hk]

/-- At targets with zero tangent coordinates, the full canonical coefficient
law is supported on actual intrinsic critical points of the same field. -/
theorem conditioned_critical_ae {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector (n + 1)) (hx : ‖x‖ ^ 2 = (n + 1 : ℕ))
    (a : EuclideanSpace ℝ (Sum (Fin 2) (Fin n))) (ha : ∀ i, a (Sum.inr i) = 0) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂coefficientKernel (jointCLM c x (tangentFrame x hx)) a,
      surfaceGradient (field c J) x = 0 := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  filter_upwards [coefficientKernel_observation_ae _
    (center_joint_surjective (by omega) μ hQ hnp x hx (tangentFrame x hx)
      (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx)) a] with J hJ
  have hzero : intrinsicGamma c x (euclideanDisorder J) = 0 := by
    apply (tangentBasis x hx).repr.injective
    apply PiLp.ext
    intro i
    rw [OrthonormalBasis.repr_apply_apply, map_zero]
    change inner ℝ (tangentBasis x hx i) (intrinsicGamma c x (euclideanDisorder J)) = 0
    rw [intrinsicGamma_inner, unpack_euclideanDisorder]
    have h := congrArg (fun y : EuclideanSpace ℝ (Sum (Fin 2) (Fin n)) => y (Sum.inr i)) hJ
    change gradientCLM c x (tangentFrame x hx) (euclideanDisorder J) i = a (Sum.inr i) at h
    rw [gradientCLM_apply, unpack_euclideanDisorder, ha] at h
    exact h
  have h := congrArg (fun v : tangentPlane x => (v : Vector (n + 1))) hzero
  simpa only [intrinsicGamma_coe (by omega) c x hx, unpack_euclideanDisorder, Submodule.coe_zero] using h

end
end SlowEquilibration.ConditionedIntrinsicHessian
