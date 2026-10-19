-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorRemainderCovariance
public import SlowEquilibration.SphericalLatitudeJointRegression

@[expose] public section

/-! The actual transverse Taylor remainder keeps its entire finite-dimensional
law under every target of the genuine affine-latitude first-jet posterior. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicHessianLaw
open SlowEquilibration.ConditionedIntrinsicHessian SlowEquilibration.SphericalLatitudeChartKacRice
open scoped RealInnerProductSpace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem scalar_comp_adjoint_eq_zero {N P : ℕ} {ι : Type*} [Fintype ι]
    (f : EuclideanDisorder N P →L[ℝ] ℝ)
    (A : EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ ι)
    (hf : ∀ i, f (((EuclideanSpace.proj i).comp A).adjoint 1)=0) :
    f.comp A.adjoint=0 := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun ι ℝ).toBasis.ext
  intro i
  have hh := actual_scalar_cross_covariance f A (EuclideanSpace.basisFun ι ℝ i)
  simp only [EuclideanSpace.basisFun_inner] at hh
  change f (A.adjoint (EuclideanSpace.basisFun ι ℝ i))=0
  rw [← hh]
  have hi := scalar_observation_covariance f ((EuclideanSpace.proj i).comp A)
  change cov[fun J => f (euclideanDisorder J),fun J => A (euclideanDisorder J) i;disorderLaw N P]=_ at hi
  exact hi.trans (hf i)

theorem taylorRemainder_latitude_joint_lift_zero {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (z : Vector (n+2)) (hz : inner ℝ z (latitudeMap w e q y)=0) :
    (taylorRemainderCLM c (latitudeMap w e q y) z).comp (latitudeJointCLM c w e q y hy).adjoint=0 := by
  apply scalar_comp_adjoint_eq_zero
  intro i
  rcases i with i | i
  · fin_cases i
    · have heq : (EuclideanSpace.proj (Sum.inl (0 : Fin 2))).comp (latitudeJointCLM c w e q y hy)=
          valueObservation c (latitudeMap w e q y) := by
        ext g
        change latitudeJointCLM c w e q y hy g (Sum.inl 0)=valueObservation c (latitudeMap w e q y) g
        simp only [latitudeJointCLM_apply_inl,latitudeScoreCLM_apply_zero,valueObservation,flatJetCLM_apply]
      change (taylorRemainderCLM c (latitudeMap w e q y) z) (((EuclideanSpace.proj (Sum.inl (0 : Fin 2))).comp (latitudeJointCLM c w e q y hy)).adjoint 1)=0
      rw [heq]
      exact taylorRemainder_value_orthogonal (by omega) c hc _ z hz
    · have heq : (EuclideanSpace.proj (Sum.inl (1 : Fin 2))).comp (latitudeJointCLM c w e q y hy)=
          directionObservation c (latitudeMap w e q y) (latitudeRadialVector e q y) := by
        ext g
        change latitudeJointCLM c w e q y hy g (Sum.inl 1)=directionObservation c (latitudeMap w e q y) (latitudeRadialVector e q y) g
        simp only [latitudeJointCLM_apply_inl,latitudeScoreCLM_apply_one,directionObservation,flatJetCLM_apply]
      change (taylorRemainderCLM c (latitudeMap w e q y) z) (((EuclideanSpace.proj (Sum.inl (1 : Fin 2))).comp (latitudeJointCLM c w e q y hy)).adjoint 1)=0
      rw [heq]
      exact taylorRemainder_direction_orthogonal (by omega) c hc _ z _ hz
  · have heq : (EuclideanSpace.proj (Sum.inr i)).comp (latitudeJointCLM c w e q y hy)=
        directionObservation c (latitudeMap w e q y) (latitudeGradientDirections e q y hy i) := by
      ext g
      change latitudeJointCLM c w e q y hy g (Sum.inr i)=directionObservation c (latitudeMap w e q y) (latitudeGradientDirections e q y hy i) g
      simp only [latitudeJointCLM_apply_inr,gradientCLM_apply,directionObservation,flatJetCLM_apply]
    rw [heq]
    exact taylorRemainder_direction_orthogonal (by omega) c hc _ z _ hz

def taylorRemainderFamily {N P : ℕ} {ι : Type*} [Fintype ι]
    (c : Degree P → ℝ) (m : Vector N) (z : ι → Vector N) :
    EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => taylorRemainderCLM c m (z i)))

@[simp] theorem taylorRemainderFamily_apply {N P : ℕ} {ι : Type*} [Fintype ι]
    (c : Degree P → ℝ) (m : Vector N) (z : ι → Vector N) (g : EuclideanDisorder N P) (i : ι) :
    taylorRemainderFamily c m z g i=taylorRemainderCLM c m (z i) g := by
  simp [taylorRemainderFamily]

/-- Every finite family of actual residual evaluations has its original law
at every target of the canonical full-tensor posterior. -/
theorem latitude_posterior_taylorRemainder_family_map {n P : ℕ} {ι : Type*} [Fintype ι]
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (z : ι → Vector (n+2)) (hz : ∀ i, inner ℝ (z i) (latitudeMap w e q y)=0)
    (target : EuclideanSpace ℝ (Sum (Fin 2) (Fin n))) :
    (coefficientKernel (latitudeJointCLM c w e q y hy) target).map
      (actualObservation (taylorRemainderFamily c (latitudeMap w e q y) z)) =
    (disorderLaw (n+2) P).map (actualObservation (taylorRemainderFamily c (latitudeMap w e q y) z)) := by
  apply coefficientKernel_target_map_linear
  ext a i
  change taylorRemainderCLM c (latitudeMap w e q y) (z i)
    ((latitudeJointCLM c w e q y hy).adjoint a)=0
  exact congrArg (fun L => L a) (taylorRemainder_latitude_joint_lift_zero c hc w e q y hy (z i) (hz i))

end
end SlowEquilibration.SphericalTaylorRemainder
