-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPalmMarginal
public import SlowEquilibration.ConditionedDeterminantMoments
public import SlowEquilibration.SphericalTwoPointCovariance

@[expose] public section

/-! The physical Palm posterior conditions the *scaled center field* H_Q,
while the quadratic latitude bank belongs to the unscaled H_N. The
cross-coefficient covariance below keeps that distinction explicit. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open SphericalTwoPointCovariance
open WholeFieldRegression IntrinsicHessianLaw SphericalSequentialRegression
open ConditionedIntrinsicHessian ConditionedDeterminantMoments
open SphericalAging.FiniteModel (Hamiltonian)
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 900000

/-- Cross covariance of two actual tensor fields with different degree
weights on the same ordered Gaussian coefficient array. -/
theorem jet_cross_covariance {N P n m : ℕ} (c d : Degree P → ℝ)
    (x y : Vector N) (a : Fin n → Vector N) (b : Fin m → Vector N) :
    cov[jet c n x a, jet d m y b; disorderLaw N P] =
      ∑ p : Degree P, Real.sqrt (c p)*Real.sqrt (d p)*
        cov[fun J : PureDisorder N p.val.val =>
              iteratedFDeriv ℝ n (Hamiltonian N p.val.val J) x a,
            fun J : PureDisorder N p.val.val =>
              iteratedFDeriv ℝ m (Hamiltonian N p.val.val J) y b;
          PureLaw N p.val.val] := by
  classical
  have heqX : jet c n x a =
      fun J => ∑ p : Degree P, Real.sqrt (c p)*blockJet p n x a J :=
    funext (jet_sum c n x a)
  have heqY : jet d m y b =
      fun J => ∑ p : Degree P, Real.sqrt (d p)*blockJet p m y b J :=
    funext (jet_sum d m y b)
  rw [heqX, heqY]
  change cov[fun J => ∑ p : Degree P, Real.sqrt (c p)*blockJet p n x a J,
    fun J => ∑ p : Degree P, Real.sqrt (d p)*blockJet p m y b J;
    disorderLaw N P] = _
  rw [covariance_fun_sum_fun_sum]
  · simp_rw [covariance_const_mul_left, covariance_const_mul_right,
      blockJet_covariance]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_eq_single p]
    · simp only [ite_true]
      ring
    · intro q hq hqp
      simp [Ne.symm hqp]
    · simp
  · intro p
    exact (blockJet_memLp p n x a).const_mul _
  · intro p
    exact (blockJet_memLp p m y b).const_mul _

/-- The genuine latitude quadratic bank is orthogonal to the value of the
physical scaled center field, without treating H_Q as H_N. -/
theorem quadraticLatitudeJet_scaledCenter_value_covariance_zero
    {N : ℕ} (hN : 0 < N) (μ : FiniteMixture) (Q a : ℝ)
    (u ω : Vector N) (hω : inner ℝ ω u=0) :
    cov[quadraticLatitudeJet μ a u ω,
      jet (centerCoefficients (mixtureCoefficients μ) Q) 0 u
        (fun i => Fin.elim0 i); disorderLaw N μ.maxDegree]=0 := by
  unfold quadraticLatitudeJet
  rw [covariance_const_mul_left, jet_cross_covariance]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro p hp
  rw [pure_hessian_value_covariance hN p.property]
  simp [hω]

/-- The bank is orthogonal to every directional gradient of the scaled
center field, including its radial mark and tangent-gradient coordinates. -/
theorem quadraticLatitudeJet_scaledCenter_gradient_covariance_zero
    {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    (hμ : 3 ≤ μ.minDegree) (Q a : ℝ) (u ω v : Vector N)
    (hω : inner ℝ ω u=0) :
    cov[quadraticLatitudeJet μ a u ω,
      jet (centerCoefficients (mixtureCoefficients μ) Q) 1 u
        (fun _ => v); disorderLaw N μ.maxDegree]=0 := by
  unfold quadraticLatitudeJet
  rw [covariance_const_mul_left, jet_cross_covariance]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hz : μ.coeff p.val.val=0
  · simp [centerCoefficients, mixtureCoefficients, hz]
  have hp3 : 3 ≤ p.val.val :=
    hμ.trans (μ.degree_bounds (Finsupp.mem_support_iff.mpr hz)).1
  rw [pure_hessian_gradient_covariance hN hp3]
  simp [hω]

/-- True cross-orthogonality for the physical observer of H_Q, in which
every conditioned score and gradient uses the scaled center coefficients.
This is stronger than the unscaled-observer marginal above. -/
theorem flatQuadraticLatitudeJet_physicalJoint_cross_zero
    {N m : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    (hμ : 3 ≤ μ.minDegree) (Q a : ℝ) (u ω : Vector N)
    (hω : inner ℝ ω u=0) (e : Fin m → Vector N) :
    (flatQuadraticLatitudeJet μ a u ω).comp
      (jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u e).adjoint=0 := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Sum (Fin 2) (Fin m)) ℝ).toBasis.ext
  intro j
  have h := actual_scalar_cross_covariance (flatQuadraticLatitudeJet μ a u ω)
    (jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u e)
    (EuclideanSpace.basisFun (Sum (Fin 2) (Fin m)) ℝ j)
  simp only [EuclideanSpace.basisFun_inner] at h
  change cov[fun J : Disorder N μ.maxDegree =>
      flatQuadraticLatitudeJet μ a u ω (euclideanDisorder J),
      fun J : Disorder N μ.maxDegree =>
        jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u e
          (euclideanDisorder J) j; disorderLaw N μ.maxDegree] =
    flatQuadraticLatitudeJet μ a u ω
      ((jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u e).adjoint
        (EuclideanSpace.basisFun (Sum (Fin 2) (Fin m)) ℝ j)) at h
  simp only [flatQuadraticLatitudeJet_actual] at h
  change flatQuadraticLatitudeJet μ a u ω
    ((jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u e).adjoint
      (EuclideanSpace.basisFun (Sum (Fin 2) (Fin m)) ℝ j)) = 0
  rw [← h]
  cases j with
  | inl j =>
    fin_cases j
    · change cov[quadraticLatitudeJet μ a u ω,
        fun J : Disorder N μ.maxDegree =>
          scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u
            (euclideanDisorder J) 0; disorderLaw N μ.maxDegree] = 0
      simp only [scoreCLM_apply_zero, unpack_euclideanDisorder]
      exact quadraticLatitudeJet_scaledCenter_value_covariance_zero
        hN μ Q a u ω hω
    · change cov[quadraticLatitudeJet μ a u ω,
        fun J : Disorder N μ.maxDegree =>
          scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u
            (euclideanDisorder J) 1; disorderLaw N μ.maxDegree] = 0
      simp only [scoreCLM_apply_one, unpack_euclideanDisorder]
      exact quadraticLatitudeJet_scaledCenter_gradient_covariance_zero
        hN μ hμ Q a u ω u hω
  | inr j =>
    simpa only [jointCLM_apply_inr, gradientCLM_apply,
      unpack_euclideanDisorder] using
      quadraticLatitudeJet_scaledCenter_gradient_covariance_zero
        hN μ hμ Q a u ω (e j) hω

/-- The entire finite-dimensional Y₂ bank retains its original law under
the *literal* mixedLaw used by determinant-weighted physical Palm estimates. -/
theorem quadraticLatitudeJetFamily_physicalMixedPalm_marginal
    {n k : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a : ℝ) (u : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (ω : Fin k → Vector (n+2)) (hω : ∀ i, inner ℝ (ω i) u=0)
    (z : EuclideanSpace ℝ (Fin 2)) :
    (mixedLaw μ Q u hu z).map
      (fun J => flatQuadraticLatitudeJetFamily μ a u ω (euclideanDisorder J)) =
      (disorderLaw (n+2) μ.maxDegree).map
        (fun J => flatQuadraticLatitudeJetFamily μ a u ω (euclideanDisorder J)) := by
  let A := jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u
    (tangentFrame u hu)
  let B := flatQuadraticLatitudeJetFamily μ a u ω
  have hBA : B.comp A.adjoint=0 := by
    ext v i
    change flatQuadraticLatitudeJet μ a u (ω i) (A.adjoint v)=0
    have hi := flatQuadraticLatitudeJet_physicalJoint_cross_zero
      (by omega : 0 < n+2) μ hμ Q a u (ω i) (hω i) (tangentFrame u hu)
    exact congrArg (fun C : EuclideanSpace ℝ (Sum (Fin 2) (Fin (n+1))) →L[ℝ] ℝ => C v) hi
  have h := coefficientKernel_target_map_linear A B hBA
    (jointScoreTarget (n+1) (((n+2:ℕ):ℝ) • z))
  change (mixedLaw μ Q u hu z).map
      (fun J => flatQuadraticLatitudeJetFamily μ a u ω (euclideanDisorder J)) =
    (disorderLaw (n+2) μ.maxDegree).map
      (fun J => flatQuadraticLatitudeJetFamily μ a u ω (euclideanDisorder J)) at h
  exact h

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
