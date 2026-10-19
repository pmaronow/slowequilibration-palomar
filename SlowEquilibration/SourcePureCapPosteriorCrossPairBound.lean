-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapPosteriorCrossBudget

/-! Uniform two-spin exponential moment for arbitrary pairs of latitudes
inside the selected proper-pure cap, under the original critical-point
value-conditioned posterior. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapPosteriorCrossPairBound
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalGaussianJet WholeFieldRegression
open SphericalPosteriorMaps SphericalMarkedWindows SphericalCriticalLatitude
open SphericalTaylorRemainder PureStationarity
open SourcePureCapPosteriorPairRatio
open SourcePureCapPosteriorCrossKernel
open SourcePureCapPosteriorCrossBudget
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The exact source cross-latitude pair bound for the physical field.
Both latitudes vary independently in `[a,1)`, while a single coefficient
`Cβ(a)` controls the transverse overlap. -/
theorem pure_valueConditioned_cross_exp_pair_le_product
    (n p : ℕ) (hp : 2 ≤ p) (β e : ℝ)
    {a q₁ q₂ t : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hq₁ : q₁ ∈ Ico a 1) (hq₂ : q₂ ∈ Ico a 1) (ht : |t| ≤ 1)
    (u w₁ w₂ : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (hq₁u : overlap u w₁=q₁) (hq₂u : overlap u w₂=q₂)
    (hpair : overlap w₁ w₂=q₁*q₂+
      Real.sqrt (1-q₁^2)*Real.sqrt (1-q₂^2)*t) :
    let μ := FiniteMixture.pure p hp 1 (by positivity)
    let c := centerCoefficients (mixtureCoefficients μ) 1
    (∫ J, Real.exp (β*field c J w₁)*Real.exp (β*field c J w₂)
      ∂valueConditionedLaw c u hu e) ≤
      (∫ J, Real.exp (β*field c J w₁) ∂valueConditionedLaw c u hu e)*
      (∫ J, Real.exp (β*field c J w₂) ∂valueConditionedLaw c u hu e)*
        Real.exp ((n+1 : ℕ)*pureResidualCoefficient p β a*t^2) := by
  dsimp only
  let μ := FiniteMixture.pure p hp 1 (by positivity)
  let c := centerCoefficients (mixtureCoefficients μ) 1
  let R := valueCriticalCoefficientResidual n μ 1 u
  let f₁ := (valueObservation c w₁).comp R
  let f₂ := (valueObservation c w₂).comp R
  rw [valueConditioned_exp_pair_factorization n μ
    (by norm_num : (0 : ℝ) < 1) u hu w₁ w₂ β e]
  have hkernel := actual_value_critical_residual_cross_kernel n μ
    (by norm_num : (0 : ℝ) < 1) u hu w₁ w₂ hq₁u hq₂u hpair
  change f₁ (f₂.adjoint 1) = (n+1 : ℕ)*sourceValueTauCross μ 1 q₁ q₂
    (Real.sqrt (1-q₁^2)*Real.sqrt (1-q₂^2)*t) at hkernel
  rw [hkernel]
  have hcov := pure_source_cross_covariance_major_on_cap p hp β ha hq₁ hq₂ ht
  have hbase : β^2*sourceValueTauCross μ 1 q₁ q₂
      (Real.sqrt (1-q₁^2)*Real.sqrt (1-q₂^2)*t) ≤
      pureResidualCoefficient p β a*t^2 := (le_abs_self _).trans hcov
  have hN : (0 : ℝ) ≤ (n+1 : ℕ) := Nat.cast_nonneg _
  have hexp : Real.exp (β^2*((n+1 : ℕ)*sourceValueTauCross μ 1 q₁ q₂
      (Real.sqrt (1-q₁^2)*Real.sqrt (1-q₂^2)*t))) ≤
      Real.exp ((n+1 : ℕ)*pureResidualCoefficient p β a*t^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hN (sub_nonneg.mpr hbase)]
  exact mul_le_mul_of_nonneg_left hexp (mul_nonneg
    (integral_nonneg (fun J => (Real.exp_pos _).le))
    (integral_nonneg (fun J => (Real.exp_pos _).le)))

end
end SlowEquilibration.SourcePureCapPosteriorCrossPairBound
