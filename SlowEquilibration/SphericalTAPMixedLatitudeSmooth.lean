-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedContactDerivatives

@[expose] public section

/-! Smoothness of the literal mixed latitude exponent in its latitude
coordinate. This supplies continuous curvature near the contact latitude. -/

namespace SlowEquilibration.SphericalTAPMixedLatitudeSmooth
noncomputable section
open SphericalTAPMixedBandExponent ConditionedEntrance SphericalMarkedWindows
set_option autoImplicit false

private theorem xi_smooth (μ : FiniteMixture) : ContDiff ℝ ⊤ μ.xi := by
  unfold FiniteMixture.xi
  fun_prop

private theorem xi1_smooth (μ : FiniteMixture) : ContDiff ℝ ⊤ μ.xi1 := by
  unfold FiniteMixture.xi1
  fun_prop

private theorem valueTheta_smooth (μ : FiniteMixture) (Q : ℝ) :
    ContDiff ℝ ⊤ (valueTheta μ Q) := by
  unfold valueTheta monomialSum
  fun_prop

private theorem radialTheta_smooth (μ : FiniteMixture) (Q : ℝ) :
    ContDiff ℝ ⊤ (radialTheta μ Q) := by
  unfold radialTheta monomialSum
  fun_prop

theorem sourceMixedMean_smooth (μ : FiniteMixture) (Q e k : ℝ) :
    ContDiff ℝ ⊤ (sourceMixedMean μ Q e k) := by
  unfold sourceMixedMean
  exact ((valueTheta_smooth μ Q).mul contDiff_const).add
    ((radialTheta_smooth μ Q).mul contDiff_const)

theorem sourceMixedVariance_smooth (μ : FiniteMixture) (Q : ℝ) :
    ContDiff ℝ ⊤ (sourceMixedVariance μ Q) := by
  unfold sourceMixedVariance sourceMixedCross sourceMixedGradientReduction
  have hxi := xi_smooth μ
  have hxi1 := xi1_smooth μ
  have hv := valueTheta_smooth μ Q
  have hr := radialTheta_smooth μ Q
  simp only [scorePairEquiv_apply,Fin.isValue,Matrix.cons_val_zero,
    Matrix.cons_val_one]
  fun_prop

theorem sourceMixedBandExponent_latitude_contDiffAt (μ : FiniteMixture)
    (β Q e k a : ℝ) (ha : |a| < 1) :
    ContDiffAt ℝ ⊤ (sourceMixedBandExponent μ β Q e k) a := by
  have hden : 1-a^2 ≠ 0 := ne_of_gt (by nlinarith [(abs_lt.mp ha).1,(abs_lt.mp ha).2])
  have hm := sourceMixedMean_smooth μ Q e k
  have hv := sourceMixedVariance_smooth μ Q
  unfold sourceMixedBandExponent sourceMixedXi
  fun_prop

/-- The actual latitude second derivative of the mixed exponent is continuous
through every physical latitude strictly between −1 and 1. -/
theorem sourceMixedBandExponent_latitude_second_continuousAt
    (μ : FiniteMixture) (β Q e k a : ℝ) (ha : |a| < 1) :
    ContinuousAt (deriv (deriv (sourceMixedBandExponent μ β Q e k))) a := by
  have h2 : ContDiffAt ℝ 2 (sourceMixedBandExponent μ β Q e k) a :=
    (sourceMixedBandExponent_latitude_contDiffAt μ β Q e k a ha).of_le (by norm_num)
  have h1 : ContDiffAt ℝ 1 (deriv (sourceMixedBandExponent μ β Q e k)) a :=
    h2.derivWithin (by norm_num)
  have h0 : ContDiffAt ℝ 0 (deriv (deriv (sourceMixedBandExponent μ β Q e k))) a :=
    h1.derivWithin (by norm_num)
  exact h0.continuousAt

end
end SlowEquilibration.SphericalTAPMixedLatitudeSmooth
