-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapPosteriorCrossPairBound
public import SlowEquilibration.SphericalPureOriginalConditionalBandFubini

/-! The exact original-field two-spin mean under a pure critical-point
posterior, expressed by the two previously proved one-spin mean profiles
and the physical cross-latitude residual covariance. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapPosteriorPairMean
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalGaussianJet WholeFieldRegression
open SphericalPosteriorMaps SphericalMarkedWindows SphericalCriticalLatitude
open SphericalTaylorRemainder
open SourcePureCapPosteriorPairRatio
open SourcePureCapPosteriorCrossKernel
open SphericalPureOriginalConditionalBandFubini
open SphericalPureOriginalConditionalPointMean
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Exact two-point posterior expectation of the original pure Hamiltonian
at arbitrary original-sphere spins. This identity works at every finite
dimension and for either parity. -/
theorem pure_original_conditioned_pair_exp_mean
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (u w₁ w₂ : Vector (n+1))
    (hu : ‖u‖^2=(n+1 : ℕ))
    (hw₁ : ‖w₁‖^2=(n+1 : ℕ)) (hw₂ : ‖w₂‖^2=(n+1 : ℕ))
    (β H : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) 1
    let q₁ := overlap u w₁
    let q₂ := overlap u w₂
    let s := overlap w₁ w₂-q₁*q₂
    (∫ J, Real.exp (β*field (mixtureCoefficients μ) J w₁)*
        Real.exp (β*field (mixtureCoefficients μ) J w₂)
      ∂valueConditionedLaw c u hu (H/(n+1 : ℕ))) =
      originalPureMeanProfile n p alpha β H u w₁*
        originalPureMeanProfile n p alpha β H u w₂*
        Real.exp (β^2*(n+1 : ℕ)*sourceValueTauCross μ 1 q₁ q₂ s) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) 1
  let q₁ := overlap u w₁
  let q₂ := overlap u w₂
  let s := overlap w₁ w₂-q₁*q₂
  have hc : c = mixtureCoefficients μ := by
    funext k
    simp [c,centerCoefficients]
  conv_lhs =>
    arg 2
    ext J
    rw [←hc]
  rw [valueConditioned_exp_pair_factorization n μ
    (by norm_num : (0 : ℝ) < 1) u hu w₁ w₂ β (H/(n+1 : ℕ))]
  have hkernel := actual_value_critical_residual_cross_kernel n μ
    (by norm_num : (0 : ℝ) < 1) u hu w₁ w₂
    (show overlap u w₁=q₁ from rfl)
    (show overlap u w₂=q₂ from rfl)
    (show overlap w₁ w₂=q₁*q₂+s by dsimp [s]; ring)
  rw [hkernel]
  have hpoint₁ := pure_original_conditioned_point_exp_mean n p hp alpha halpha
    (by norm_num : (0 : ℝ) < 1) u w₁ hu hw₁
    (show overlap u w₁=q₁ from rfl) β H
  have hpoint₂ := pure_original_conditioned_point_exp_mean n p hp alpha halpha
    (by norm_num : (0 : ℝ) < 1) u w₂ hu hw₂
    (show overlap u w₂=q₂ from rfl) β H
  simp only [Real.sqrt_one,one_pow,one_mul] at hpoint₁ hpoint₂
  have hpoint₁' : (∫ J, Real.exp (β*field c J w₁)
      ∂valueConditionedLaw c u hu (H/(n+1 : ℕ))) =
      originalPureMeanProfile n p alpha β H u w₁ := by
    have heq : (fun J : Disorder (n+1) μ.maxDegree =>
        Real.exp (β*field c J w₁)) =
        (fun J => Real.exp (β*field (mixtureCoefficients μ) J w₁)) := by
      funext J
      rw [hc]
    rw [heq]
    exact hpoint₁
  have hpoint₂' : (∫ J, Real.exp (β*field c J w₂)
      ∂valueConditionedLaw c u hu (H/(n+1 : ℕ))) =
      originalPureMeanProfile n p alpha β H u w₂ := by
    have heq : (fun J : Disorder (n+1) μ.maxDegree =>
        Real.exp (β*field c J w₂)) =
        (fun J => Real.exp (β*field (mixtureCoefficients μ) J w₂)) := by
      funext J
      rw [hc]
    rw [heq]
    exact hpoint₂
  rw [hpoint₁',hpoint₂']
  simp only [q₁,q₂,s]
  simp only [μ,mul_assoc]

end
end SlowEquilibration.SourcePureCapPosteriorPairMean
