-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetJointGaussian
public import SlowEquilibration.NormalizedPairObservations
public import SlowEquilibration.ConditionedIntrinsicHessian

@[expose] public section

/-! Auxiliary unscaled-center observer: the degree-two latitude bank keeps
its original marginal at every value/radial/gradient target when the observer
uses the unscaled field coefficients. The manuscript's physical `mixedLaw`
instead observes the scaled center field `H_Q`; that separate bridge is
proved in `SphericalQuadraticLatitudeJetPhysicalPalmMarginal`. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open WholeFieldRegression NormalizedPairObservations
open ConditionedIntrinsicHessian IntrinsicHessianLaw
open scoped RealInnerProductSpace
set_option autoImplicit false

def flatQuadraticLatitudeJet {N : ℕ} (μ : FiniteMixture) (a : ℝ)
    (u ω : Vector N) : EuclideanDisorder N μ.maxDegree →L[ℝ] ℝ :=
  ((1-a^2)/2) • flatJetCLM (mixtureCoefficients μ) 2 (a • u) ![ω,ω]

@[simp] theorem flatQuadraticLatitudeJet_actual {N : ℕ} (μ : FiniteMixture)
    (a : ℝ) (u ω : Vector N) (J : Disorder N μ.maxDegree) :
    flatQuadraticLatitudeJet μ a u ω (euclideanDisorder J) =
      quadraticLatitudeJet μ a u ω J := by
  simp [flatQuadraticLatitudeJet, quadraticLatitudeJet]

/-- The scalar bank probe annihilates the adjoint of the genuine normalized
mixed Palm observer, including every tangent-gradient coordinate. -/
theorem flatQuadraticLatitudeJet_mixedObservation_cross_zero
    {N m : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    (hμ : 3 ≤ μ.minDegree) (a : ℝ) (u ω : Vector N)
    (hω : inner ℝ ω u=0) (e : Fin m → Vector N) :
    (flatQuadraticLatitudeJet μ a u ω).comp
      (singleMixedObservation (mixtureCoefficients μ) u e).adjoint=0 := by
  let c := mixtureCoefficients μ
  let B := flatQuadraticLatitudeJet μ a u ω
  let A := singleMixedObservation c u e
  have hB : MemLp (quadraticLatitudeJet μ a u ω) 2
      (disorderLaw N μ.maxDegree) :=
    (jet_memLp c 2 (a • u) ![ω,ω]).const_mul _
  have hval : MemLp (jet c 0 u (fun i => Fin.elim0 i)) 2
      (disorderLaw N μ.maxDegree) := jet_memLp c 0 u _
  have hrad : MemLp (jet c 1 u (fun _ => u)) 2
      (disorderLaw N μ.maxDegree) := jet_memLp c 1 u _
  have hgrad (v : MixedObservationSpace m) :
      MemLp (jet c 1 u (fun _ => frameSum e v.snd)) 2
        (disorderLaw N μ.maxDegree) := jet_memLp c 1 u _
  apply ContinuousLinearMap.ext
  intro v
  change B (A.adjoint v)=0
  have hcov := actual_scalar_cross_covariance B A v
  change cov[fun J : Disorder N μ.maxDegree =>
    flatQuadraticLatitudeJet μ a u ω (euclideanDisorder J),
    fun J : Disorder N μ.maxDegree => inner ℝ v (A (euclideanDisorder J));
    disorderLaw N μ.maxDegree]=B (A.adjoint v) at hcov
  simp only [flatQuadraticLatitudeJet_actual] at hcov
  have hfun : (fun J : Disorder N μ.maxDegree =>
      inner ℝ v (A (euclideanDisorder J))) =
      (fun J => (v.fst 0/Real.sqrt (N:ℝ))*jet c 0 u (fun i => Fin.elim0 i) J) +
      (fun J => (v.fst 1/Real.sqrt (N:ℝ))*jet c 1 u (fun _ => u) J) +
      (fun J => jet c 1 u (fun _ => frameSum e v.snd) J) := by
    funext J
    exact singleMixedObservation_inner_actual c u e v J
  rw [hfun] at hcov
  rw [covariance_add_right hB
      ((hval.const_mul _).add (hrad.const_mul _)) (hgrad v),
    covariance_add_right hB (hval.const_mul _) (hrad.const_mul _)] at hcov
  simpa only [c, covariance_const_mul_right,
    quadraticLatitudeJet_center_value_covariance_zero hN μ a u ω hω,
    quadraticLatitudeJet_center_radial_covariance_zero hN μ hμ a u ω hω,
    quadraticLatitudeJet_center_tangent_covariance_zero hN μ hμ a u ω
      (frameSum e v.snd) hω, mul_zero, zero_add] using hcov.symm

/-- Auxiliary unscaled-coefficient observation: at each prescribed normalized
value/radial/tangent target, including probability-zero targets, a fixed
genuine degree-two latitude probe retains its unconditioned law. -/
theorem quadraticLatitudeJet_mixedPalm_marginal
    {N m : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    (hμ : 3 ≤ μ.minDegree) (a : ℝ) (u ω : Vector N)
    (hω : inner ℝ ω u=0) (e : Fin m → Vector N)
    (target : MixedObservationSpace m) :
    (coefficientKernel (singleMixedObservation (mixtureCoefficients μ) u e) target).map
      (quadraticLatitudeJet μ a u ω) =
      (disorderLaw N μ.maxDegree).map (quadraticLatitudeJet μ a u ω) := by
  have h := coefficientKernel_target_map_linear
    (singleMixedObservation (mixtureCoefficients μ) u e)
    (flatQuadraticLatitudeJet μ a u ω)
    (flatQuadraticLatitudeJet_mixedObservation_cross_zero hN μ hμ a u ω hω e)
    target
  change (coefficientKernel (singleMixedObservation (mixtureCoefficients μ) u e)
    target).map (fun J => flatQuadraticLatitudeJet μ a u ω (euclideanDisorder J)) =
      (disorderLaw N μ.maxDegree).map
        (fun J => flatQuadraticLatitudeJet μ a u ω (euclideanDisorder J)) at h
  simpa only [flatQuadraticLatitudeJet_actual] using h

/-- The whole finite set of genuine quadratic latitude probes is one
Euclidean-valued linear observation of the original Gaussian tensors. -/
def flatQuadraticLatitudeJetFamily {N k : ℕ} (μ : FiniteMixture) (a : ℝ)
    (u : Vector N) (ω : Fin k → Vector N) :
    EuclideanDisorder N μ.maxDegree →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => flatQuadraticLatitudeJet μ a u (ω i)))

@[simp] theorem flatQuadraticLatitudeJetFamily_actual {N k : ℕ}
    (μ : FiniteMixture) (a : ℝ) (u : Vector N) (ω : Fin k → Vector N)
    (J : Disorder N μ.maxDegree) (i : Fin k) :
    flatQuadraticLatitudeJetFamily μ a u ω (euclideanDisorder J) i =
      quadraticLatitudeJet μ a u (ω i) J := by
  simp [flatQuadraticLatitudeJetFamily]

/-- The complete finite-dimensional bank marginal is unchanged under each
target of the auxiliary unscaled-coefficient observer. -/
theorem quadraticLatitudeJetFamily_mixedPalm_marginal
    {N m k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    (hμ : 3 ≤ μ.minDegree) (a : ℝ) (u : Vector N)
    (ω : Fin k → Vector N) (hω : ∀ i, inner ℝ (ω i) u=0)
    (e : Fin m → Vector N) (target : MixedObservationSpace m) :
    (coefficientKernel (singleMixedObservation (mixtureCoefficients μ) u e) target).map
      (fun J => flatQuadraticLatitudeJetFamily μ a u ω (euclideanDisorder J)) =
      (disorderLaw N μ.maxDegree).map
        (fun J => flatQuadraticLatitudeJetFamily μ a u ω (euclideanDisorder J)) := by
  let A := singleMixedObservation (mixtureCoefficients μ) u e
  let B := flatQuadraticLatitudeJetFamily μ a u ω
  have hBA : B.comp A.adjoint=0 := by
    ext v i
    change flatQuadraticLatitudeJet μ a u (ω i) (A.adjoint v)=0
    have hi := flatQuadraticLatitudeJet_mixedObservation_cross_zero
      hN μ hμ a u (ω i) (hω i) e
    exact congrArg (fun C : MixedObservationSpace m →L[ℝ] ℝ => C v) hi
  have h := coefficientKernel_target_map_linear A B hBA target
  change (coefficientKernel (singleMixedObservation (mixtureCoefficients μ) u e)
    target).map
      (fun J => flatQuadraticLatitudeJetFamily μ a u ω (euclideanDisorder J)) =
    (disorderLaw N μ.maxDegree).map
      (fun J => flatQuadraticLatitudeJetFamily μ a u ω (euclideanDisorder J)) at h
  exact h

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
