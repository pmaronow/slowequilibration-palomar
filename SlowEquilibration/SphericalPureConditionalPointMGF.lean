-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalValueCriticalLatitudeCovariance
public import SlowEquilibration.GaussianDensity

@[expose] public section

/-! A genuine pointwise conditional exponential moment for the original
Gaussian disorder, before specialization to the pure polynomial variance. -/

namespace SlowEquilibration.SphericalPureConditionalPointMGF
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression
open SphericalPosteriorMaps SphericalMarkedWindows SphericalCriticalLatitude
open SphericalTaylorRemainder
open scoped RealInnerProductSpace
set_option autoImplicit false

theorem valueConditioned_exp_point
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (w : Vector (n+1)) (β e : ℝ) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let f := (valueObservation c w).comp (valueCriticalCoefficientResidual n μ Q u)
    (∫ J, Real.exp (β*field c J w) ∂valueConditionedLaw c u hu e) =
      Real.exp (β*valueObservation c w (valueLift n μ Q u ((n+1 : ℕ)*e))+
        β^2*‖f.adjoint 1‖^2/2) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let f := (valueObservation c w).comp (valueCriticalCoefficientResidual n μ Q u)
  have hmark : AEStronglyMeasurable (fun J : Disorder (n+1) μ.maxDegree =>
      Real.exp (β*field c J w))
      ((stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).map
        (fun g => unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q u e g))) := by
    apply Continuous.aestronglyMeasurable
    have hc : Continuous (fun J : Disorder (n+1) μ.maxDegree => field c J w) := by
      convert (fieldCLM c w).continuous using 1
      funext J
      exact (fieldCLM_apply c w J).symm
    exact Real.continuous_exp.comp (hc.const_mul β)
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
      field c (unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q u e g)) w =
        f g+valueObservation c w (valueLift n μ Q u ((n+1 : ℕ)*e)) := by
    rw [←valueObservation_actual]
    change valueObservation c w (euclideanDisorder
      (unpackDisorder (valuePosterior n μ Q u e g))) = _
    rw [show euclideanDisorder
      (unpackDisorder (valuePosterior n μ Q u e g)) =
        valuePosterior n μ Q u e g from rfl]
    simp only [f,valuePosterior,valueCriticalCoefficientResidual,
      ContinuousLinearMap.comp_apply,map_add]
  simp_rw [hpoint]
  have hlin (g : EuclideanDisorder (n+1) μ.maxDegree) :
      f g=inner ℝ (f.adjoint 1) g := by
    rw [f.adjoint_inner_left]
    simp
  simp_rw [hlin]
  have he (g : EuclideanDisorder (n+1) μ.maxDegree) :
      Real.exp (β*(inner ℝ (f.adjoint 1) g+
        valueObservation c w (valueLift n μ Q u ((n+1 : ℕ)*e)))) =
      Real.exp (β*valueObservation c w (valueLift n μ Q u ((n+1 : ℕ)*e))) *
        Real.exp (β*inner ℝ (f.adjoint 1) g) := by
    rw [mul_add,Real.exp_add]
    ring
  simp_rw [he]
  rw [integral_const_mul,GaussianDensity.integral_exp_inner_stdGaussian,
    ←Real.exp_add]

end
end SlowEquilibration.SphericalPureConditionalPointMGF
