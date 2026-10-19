-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapPosteriorPairMGF
public import SlowEquilibration.SphericalValueCriticalLatitudeCovariance

/-! The genuine proper-pure conditional two-spin Gibbs weight is bounded
by the product of its one-spin means times the source quadratic transverse
overlap factor. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapPosteriorPairRatio
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalGaussianJet WholeFieldRegression
open SphericalPosteriorMaps SphericalMarkedWindows SphericalCriticalLatitude
open SphericalTaylorRemainder PureStationarity
open SphericalParisiPureLatitudeCovariance
open SourcePureCapPosteriorPairMGF SourcePureCapPosteriorAngularBudget
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Exact normalized Wick formula under the original value-conditioned
field. The cross covariance is the true coefficient-residual pairing. -/
theorem valueConditioned_exp_pair_factorization
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (w₁ w₂ : Vector (n+1)) (β e : ℝ) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let R := valueCriticalCoefficientResidual n μ Q u
    let f₁ := (valueObservation c w₁).comp R
    let f₂ := (valueObservation c w₂).comp R
    (∫ J, Real.exp (β*field c J w₁)*Real.exp (β*field c J w₂)
      ∂valueConditionedLaw c u hu e) =
      (∫ J, Real.exp (β*field c J w₁) ∂valueConditionedLaw c u hu e)*
      (∫ J, Real.exp (β*field c J w₂) ∂valueConditionedLaw c u hu e)*
        Real.exp (β^2*f₁ (f₂.adjoint 1)) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let R := valueCriticalCoefficientResidual n μ Q u
  let f₁ := (valueObservation c w₁).comp R
  let f₂ := (valueObservation c w₂).comp R
  let m₁ := valueObservation c w₁ (valueLift n μ Q u ((n+1 : ℕ)*e))
  let m₂ := valueObservation c w₂ (valueLift n μ Q u ((n+1 : ℕ)*e))
  rw [valueConditioned_exp_pair n μ hQ u hu w₁ w₂ β e,
    SphericalPureConditionalPointMGF.valueConditioned_exp_point n μ hQ u hu w₁ β e,
    SphericalPureConditionalPointMGF.valueConditioned_exp_point n μ hQ u hu w₂ β e]
  change Real.exp (β*(m₁+m₂)+β^2*‖(f₁+f₂).adjoint 1‖^2/2) =
    Real.exp (β*m₁+β^2*‖f₁.adjoint 1‖^2/2)*
      Real.exp (β*m₂+β^2*‖f₂.adjoint 1‖^2/2)*
        Real.exp (β^2*f₁ (f₂.adjoint 1))
  rw [←Real.exp_add,←Real.exp_add]
  congr 1
  rw [map_add, add_apply, norm_add_sq_real]
  have hpair : inner ℝ (f₁.adjoint 1) (f₂.adjoint 1) =
      f₁ (f₂.adjoint 1) := by
    rw [f₁.adjoint_inner_left]
    simp
  rw [hpair]
  ring

/-- At two spins of one latitude, the actual conditional pair weight is
bounded by the product of the two actual posterior means and the strict
source cap's transverse-overlap exponential. This holds for odd p too. -/
theorem pure_valueConditioned_exp_pair_le_product
    (n p : ℕ) (hp : 2 ≤ p) (β e : ℝ)
    {a q t : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ Ico a 1) (ht : |t| ≤ 1)
    (u w₁ w₂ : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (hq₁ : overlap u w₁=q) (hq₂ : overlap u w₂=q)
    (hpair : overlap w₁ w₂=q^2+(1-q^2)*t) :
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
  have hkernel := actual_value_critical_residual_kernel n μ
    (by norm_num : (0 : ℝ) < 1) u hu w₁ w₂ hq₁ hq₂ hpair
  change f₁ (f₂.adjoint 1) = (n+1 : ℕ)*sourceValueTau μ 1 q t at hkernel
  rw [hkernel]
  have hcov := pure_source_covariance_major_on_cap p hp β ha hq ht
  have hbase : β^2*sourceValueTau μ 1 q t ≤
      pureResidualCoefficient p β a*t^2 := (le_abs_self _).trans hcov
  have hN : (0 : ℝ) ≤ (n+1 : ℕ) := Nat.cast_nonneg _
  have hexp : Real.exp (β^2*((n+1 : ℕ)*sourceValueTau μ 1 q t)) ≤
      Real.exp ((n+1 : ℕ)*pureResidualCoefficient p β a*t^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hN (sub_nonneg.mpr hbase)]
  exact mul_le_mul_of_nonneg_left hexp (mul_nonneg
    (integral_nonneg (fun J => (Real.exp_pos _).le))
    (integral_nonneg (fun J => (Real.exp_pos _).le)))

end
end SlowEquilibration.SourcePureCapPosteriorPairRatio
