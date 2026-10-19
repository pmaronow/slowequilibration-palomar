-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapPosteriorAngularBudget
public import SlowEquilibration.SphericalPureConditionalPointMGF

/-! An exact two-point exponential moment under the actual value and
zero-tangent-gradient conditioned disorder law. This is the Gaussian
input to source `pc-band-second`; no independent-Hessian assumption is used. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapPosteriorPairMGF
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression
open SphericalPosteriorMaps SphericalMarkedWindows SphericalCriticalLatitude
open SphericalTaylorRemainder
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 900000

/-- Exact Gaussian pair MGF under the physical pure-compatible posterior.
The norm of the sum retains the true cross covariance between the two
spins, including its sign. -/
theorem valueConditioned_exp_pair
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (w₁ w₂ : Vector (n+1)) (β e : ℝ) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let R := valueCriticalCoefficientResidual n μ Q u
    let f := (valueObservation c w₁).comp R +
      (valueObservation c w₂).comp R
    let m := valueObservation c w₁ (valueLift n μ Q u ((n+1 : ℕ)*e))+
      valueObservation c w₂ (valueLift n μ Q u ((n+1 : ℕ)*e))
    (∫ J, Real.exp (β*field c J w₁)*Real.exp (β*field c J w₂)
      ∂valueConditionedLaw c u hu e) =
      Real.exp (β*m+β^2*‖f.adjoint 1‖^2/2) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let R := valueCriticalCoefficientResidual n μ Q u
  let f := (valueObservation c w₁).comp R+
    (valueObservation c w₂).comp R
  let m := valueObservation c w₁ (valueLift n μ Q u ((n+1 : ℕ)*e))+
    valueObservation c w₂ (valueLift n μ Q u ((n+1 : ℕ)*e))
  have hmark : AEStronglyMeasurable (fun J : Disorder (n+1) μ.maxDegree =>
      Real.exp (β*field c J w₁)*Real.exp (β*field c J w₂))
      ((stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).map
        (fun g => unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q u e g))) := by
    apply Continuous.aestronglyMeasurable
    have hc₁ : Continuous (fun J : Disorder (n+1) μ.maxDegree => field c J w₁) := by
      convert (fieldCLM c w₁).continuous using 1
      funext J
      exact (fieldCLM_apply c w₁ J).symm
    have hc₂ : Continuous (fun J : Disorder (n+1) μ.maxDegree => field c J w₂) := by
      convert (fieldCLM c w₂).continuous using 1
      funext J
      exact (fieldCLM_apply c w₂ J).symm
    exact (Real.continuous_exp.comp (hc₁.const_mul β)).mul
      (Real.continuous_exp.comp (hc₂.const_mul β))
  have hmap : AEMeasurable (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
      unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q u e g))
      (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) := by
    apply Continuous.aemeasurable
    have hp : Continuous (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
        valuePosterior n μ Q u e g) := by
      unfold valuePosterior
      fun_prop
    fun_prop
  rw [valueConditionedLaw_eq_map n μ hQ u hu e,
    integral_map hmap hmark]
  have hpoint (g : EuclideanDisorder (n+1) μ.maxDegree) :
      field c (unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q u e g)) w₁+
      field c (unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q u e g)) w₂ =
        f g+m := by
    rw [←valueObservation_actual,←valueObservation_actual]
    change valueObservation c w₁ (valuePosterior n μ Q u e g)+
      valueObservation c w₂ (valuePosterior n μ Q u e g) = _
    simp only [f,m,valuePosterior,R,valueCriticalCoefficientResidual,
      add_apply,ContinuousLinearMap.comp_apply,map_add]
    ring
  simp_rw [←Real.exp_add]
  have hlinear (g : EuclideanDisorder (n+1) μ.maxDegree) :
      f g=inner ℝ (f.adjoint 1) g := by
    rw [f.adjoint_inner_left]
    simp
  simp_rw [show ∀ g : EuclideanDisorder (n+1) μ.maxDegree,
      β*field c (unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q u e g)) w₁+
      β*field c (unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q u e g)) w₂ =
      β*(f g+m) from fun g => by rw [←mul_add,hpoint g]]
  simp_rw [hlinear]
  have he (g : EuclideanDisorder (n+1) μ.maxDegree) :
      Real.exp (β*(inner ℝ (f.adjoint 1) g+m)) =
        Real.exp (β*m)*Real.exp (β*inner ℝ (f.adjoint 1) g) := by
    rw [mul_add,Real.exp_add]
    ring
  simp_rw [he]
  rw [integral_const_mul,GaussianDensity.integral_exp_inner_stdGaussian,
    ←Real.exp_add]

end
end SlowEquilibration.SourcePureCapPosteriorPairMGF
